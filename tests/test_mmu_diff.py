"""Differential test: orbit-os mmu.c map_range()/mmu_init() vs the verified Lean model.

The C page tables are decoded by a software stage-1 walk (harness/mmu_driver.c); the Lean model
is walked by `Mmu.walk`. Both answer the same translation queries, which must agree exactly
(output address and attributes, or fault). Queries cover every range boundary (first and last
byte, one page before and after, the enclosing 2 MiB block boundaries) plus random addresses.
Whole-window exhaustiveness is covered against the intended mapping in test_mmu_bounded.py.
"""
import os
import random

from drivers import KVA, PROTS, QEMU_VIRT, RPI5, c_mmu, layout_cmd, lean_model, run

SEQS = int(os.environ.get("MMU_DIFF_SEQS", 100))
WIN = 32 << 20
M2 = 1 << 21


def edges(va, size):
    out = set()
    for x in (va, va + size - 1, va + size, va - 1):
        for d in (-4096, 0, 4096):
            out.add(x + d)
    for x in (va & ~(M2 - 1), (va + size) & ~(M2 - 1)):
        out |= {x - 1, x, x + M2 - 1, x + M2}
    return {x for x in out if 0 <= x < (1 << 48)}


def random_session(rng: random.Random):
    cmds, qs = ["reset"], set()
    for _ in range(rng.randint(1, 5)):
        if rng.random() < 0.4:   # 2 MiB-friendly ranges exercise block descriptors
            va = rng.randrange(0, WIN, M2)
            pa = rng.randrange(0, 1 << 32, M2) + (0 if rng.random() < 0.8 else 4096)
            size = rng.choice([1, 2]) * M2
            if rng.random() < 0.4:
                size += rng.randrange(0, 1 << 17, 4096)
        else:
            va = rng.randrange(0, WIN, 4096)
            pa = rng.randrange(0, 1 << 36, 4096)
            size = rng.randrange(4096, 1 << 18, 4096)
            if rng.random() < 0.3:   # straddle a 2 MiB boundary
                va = rng.randrange(M2, WIN, M2) - rng.randrange(4096, 1 << 17, 4096)
        if rng.random() < 0.2:   # unaligned arguments
            va += rng.randrange(4096)
            pa += rng.randrange(4096)
            size += rng.randrange(4096)
        prot = rng.choice(list(PROTS.values()))
        cmds.append(f"map {va:x} {pa:x} {size:x} {prot:x}")
        qs |= edges(va, size)
    qs |= {rng.randrange(0, WIN + (4 << 20)) for _ in range(24)}
    cmds += [f"query lo {q:x}" for q in sorted(qs)]
    return cmds


def answers(out):
    return [x for x in out if x != "ok"]


def test_map_range_agrees_with_model():
    rng = random.Random(4242)
    cmds = []
    for _ in range(SEQS):
        cmds += random_session(rng)
    c = answers(run([c_mmu()], cmds))
    ln = answers(run([lean_model(), "mmu"], cmds, timeout=3600))
    nq = sum(1 for x in cmds if x.startswith("query"))
    assert len(c) == len(ln) == nq
    mapped = sum(1 for x in c if not x.endswith("fault"))
    for k, (a, b) in enumerate(zip(c, ln)):
        assert a == b, f"query {k}: C={a} Lean={b}"
    assert mapped > nq // 4 and mapped < nq      # both mapped and unmapped addresses were probed


def test_prot_constants_match_model():
    out = run([c_mmu()], [f"prot {k}" for k in PROTS])
    assert [int(x, 16) for x in out] == list(PROTS.values())


def test_unaligned_range_fixed():
    """map_range(va=0x1800, size=0x1000) used to miss the page at 0x2000 (orbit-os <= 49ede1e,
    Lean: Mmu.unaligned_bug on mapRangeV1); fixed in orbit-os 1a8385b (Mmu.unaligned_fixed)."""
    k = PROTS["KDATA"]
    cmds = ["reset", f"map 1800 1800 1000 {k:x}", "query lo 1800", "query lo 27ff", "query lo 3000"]
    want = [f"1800 1800 {k:x}", f"27ff 27ff {k:x}", "3000 fault"]
    assert answers(run([c_mmu()], cmds)) == want
    assert answers(run([lean_model(), "mmu"], cmds)) == want


def layout_queries(L):
    qs = set()
    for k in ("ks", "uts", "ute", "te", "re", "uss", "use", "end"):
        qs |= {L[k] - 4096, L[k] - 1, L[k], L[k] + 4096}
    qs |= edges(L["ramb"], min(L["rams"], 4 << 30)) | edges(L["devb"], L["devs"])
    if L["dtb"]:
        qs |= edges(L["dtb"], L["dtbs"])
    qs = sorted(q for q in qs if q >= 0)
    hi = sorted({KVA + q for q in edges(L["ramb"], min(L["rams"], 4 << 30)) | edges(L["devb"], L["devs"])})
    return [f"query lo {q:x}" for q in qs] + [f"query hi {q:x}" for q in hi]


def test_mmu_init_layouts_agree_with_model():
    # RAM reduced to 32 MiB: the Lean executable evaluates the model naively and is too slow for a
    # 4 GiB linear map; the full-size layouts are checked exhaustively against the intended mapping
    # in test_mmu_bounded.py.
    for L0 in (QEMU_VIRT, RPI5):
        L = dict(L0, rams=32 << 20)
        cmds = [layout_cmd(L)] + layout_queries(L)
        c = answers(run([c_mmu()], cmds))
        ln = answers(run([lean_model(), "mmu"], cmds, timeout=3600))
        assert c == ln
        assert any(not x.endswith("fault") for x in c)
