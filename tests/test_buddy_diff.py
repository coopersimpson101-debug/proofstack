"""Differential test: orbit-os buddy.c (compiled with zig cc) vs the verified Lean model.

Both programs receive the same random operation sequences and must print identical results
for every command: returned page index of each allocation, return code of each free, and the
complete counter state (free_pages, nfree[0..10]) after each operation.
"""
import os
import random

from drivers import c_buddy, lean_model, run

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


def test_overlapping_add_sequences_agree():
    """Overlapping adds (fixed in orbit-os 1a8385b): the model and the C code agree on every line
    of whole sessions, the C self-check passes after every operation, and no session ever has
    more free pages than the span."""
    rng = random.Random(99)
    cmds = []
    for _ in range(SEQS // 3):
        cmds += random_session(rng, overlapping=True)
    c_out, _ = compare(cmds)
    n = 0
    for cmd, line in zip(cmds, c_out):
        if cmd.startswith("init"):
            n = int(cmd.split()[1])
        if cmd == "state":
            f = line.split()
            assert f[-1] == "0" and int(f[0]) <= n


def test_overlapping_add_range_fixed():
    """Regression for the bug proofstack found in buddy_add_range (orbit-os <= 49ede1e):
    re-adding a range that starts inside an existing free block managed its pages twice --
    add(0,4) then add(1,1) gave 5 free pages and page 1 was handed out twice (Lean:
    Buddy.bug_state_free / bug_double_allocation on addRangeV1). Fixed in orbit-os 1a8385b
    (Lean: Buddy.fixed_state_free / fixed_no_double_allocation, Buddy.addRange_inv)."""
    cmds = ["init 4", "add 0 4", "add 1 1", "state", "alloc 0", "alloc 2", "state"]
    c = run([c_buddy()], cmds)
    ln = run([lean_model(), "buddy"], cmds)
    assert c[3] == "4 0 0 1 0 0 0 0 0 0 0 0 0"          # 4 free pages, one order-2 block
    assert c[4] == "0" and c[5] == "-1"                 # no second, overlapping allocation
    assert [x.split()[:12] for x in c] == [x.split() for x in ln]
