"""Differential test: orbit-os buddy.c (compiled with zig cc) vs the verified Lean model.

Both programs receive the same random operation sequences and must print identical results
for every command: returned page index of each allocation, return code of each free, and the
complete counter state (free_pages, nfree[0..10]) after each operation.
"""
import os
import random

from drivers import c_buddy, lean_model, run, run_raw

SEQS = int(os.environ.get("BUDDY_DIFF_SEQS", 300))
OPS = int(os.environ.get("BUDDY_DIFF_OPS", 200))


def random_session(rng: random.Random, overlapping: bool) -> list[str]:
    n = rng.choice([1, 7, 64, 100, 512, 1000, 1024, 1536, 2048, rng.randint(1, 4096)])
    cmds = [f"init {n}"]
    # usable ranges: disjoint holes (as mm_init produces) or arbitrary, possibly overlapping ones
    cursor = 0
    for _ in range(rng.randint(1, 5)):
        if overlapping:
            a = rng.randrange(n)
            cmds.append(f"add {a} {rng.randint(0, n - a)}")
        else:
            if cursor >= n:
                break
            a = rng.randint(cursor, min(n - 1, cursor + n // 4 + 1))
            ln = rng.randint(1, max(1, n - a))
            cmds.append(f"add {a} {ln}")
            cursor = a + ln + rng.randint(0, 8)
    cmds.append("state")
    for _ in range(OPS):
        r = rng.random()
        if r < 0.5:
            cmds.append(f"alloc {rng.choice([0, 0, 0, 1, 1, 2, 3, 4, 5, 8, 10, 11])}")
        else:
            cmds.append(f"free {rng.randrange(n + 8)}")
        cmds.append("state")
    return cmds


def free_heavy_session(rng: random.Random) -> list[str]:
    """allocate a lot, then free exactly the returned blocks in random order (needs C output)."""
    n = rng.choice([256, 1024, 2048])
    cmds = [f"init {n}", f"add 0 {n}"]
    cmds += [f"alloc {rng.choice([0, 0, 1, 2, 3])}" for _ in range(60)]
    out = run([c_buddy()], cmds)
    got = [int(x) for x in out[2:] if x != "-1"]
    rng.shuffle(got)
    for g in got:
        cmds += [f"free {g}", "state"]
    return cmds


def compare(cmds):
    c_out = run([c_buddy()], cmds)
    l_out = run([lean_model(), "buddy"], cmds)
    assert len(c_out) == len(l_out) == len(cmds)
    checks = 0
    for k, (cmd, c, ln) in enumerate(zip(cmds, c_out, l_out)):
        if cmd == "state":
            assert c.split()[:12] == ln.split(), f"line {k} ({cmd}): C={c} Lean={ln}"
            checks += 1
        else:
            assert c == ln, f"line {k} ({cmd}): C={c} Lean={ln}"
    return c_out, checks


def test_random_sequences_agree():
    rng = random.Random(20261126)
    cmds = []
    for _ in range(SEQS):
        cmds += random_session(rng, overlapping=False)
    c_out, checks = compare(cmds)
    # with disjoint adds the C self-check (buddy_check) passes after every operation
    assert all(line.split()[-1] == "0" for cmd, line in zip(cmds, c_out) if cmd == "state")
    assert checks > SEQS * OPS


def test_alloc_free_sequences_agree():
    rng = random.Random(31337)
    cmds = []
    for _ in range(40):
        cmds += free_heavy_session(rng)
    c_out, _ = compare(cmds)
    # freeing everything that was allocated restores a fully coalesced span
    assert all(line.split()[-1] == "0" for cmd, line in zip(cmds, c_out) if cmd == "state")


def test_alloc_then_free_restores_counters():
    """alloc-then-free restores the counters exactly (Lean: Buddy.alloc_free_roundtrip)."""
    rng = random.Random(7)
    for _ in range(30):
        o = rng.randint(0, 10)
        pre = ["init 1024", "add 0 1024", f"alloc {rng.randint(0, 3)}", "state", f"alloc {o}"]
        res = run([c_buddy()], pre)
        seq = pre + [f"free {res[4]}", "state"]
        res = run([c_buddy()], seq)
        assert res[3] == res[6]
        assert [x.split()[:12] for x in res] == [x.split() for x in run([lean_model(), "buddy"], seq)]


def test_overlapping_add_phase_agrees():
    """For overlapping (buggy) adds the model still reproduces buddy_add_range exactly: same
    free-page count and per-order free-list lengths. Afterwards the C allocator's intrusive
    free lists can contain the same page twice, which the model's block lists do not represent,
    so allocation sequences on such states are not compared; the C driver is only observed
    (it frequently crashes on its corrupted lists)."""
    rng = random.Random(99)
    crashed = overcommitted = 0
    for _ in range(200):
        cmds = random_session(rng, overlapping=True)
        add_phase = cmds[:cmds.index("state") + 1]
        c = run([c_buddy()], add_phase)
        ln = run([lean_model(), "buddy"], add_phase)
        assert c[-1].split()[:12] == ln[-1].split()
        n = int(add_phase[0].split()[1])
        overcommitted += int(c[-1].split()[0]) > n
        rc, _ = run_raw([c_buddy()], cmds)
        crashed += rc != 0
    assert overcommitted > 0
    print(f"overlapping adds: {overcommitted}/200 sessions with more free pages than the span has; "
          f"C driver crashed in {crashed}/200 full sessions")


def test_overlapping_add_range_bug():
    """Real bug in buddy_add_range: re-adding a range that starts inside an existing free block
    manages its pages twice. buddy_check() does not notice, and the same page is handed out by
    two live allocations (Lean: Buddy.bug_state_free, bug_breaks_invariant,
    bug_double_allocation)."""
    cmds = ["init 4", "add 0 4", "add 1 1", "state", "alloc 0", "alloc 2", "state"]
    c = run([c_buddy()], cmds)
    ln = run([lean_model(), "buddy"], cmds)
    assert c[3] == "5 1 0 1 0 0 0 0 0 0 0 0 0"          # 5 free pages in a 4-page span, check = 0
    assert c[4] == "1" and c[5] == "0"                  # page 1 is inside both [1,2) and [0,4)
    assert [x.split()[:12] for x in c] == [x.split() for x in ln]
