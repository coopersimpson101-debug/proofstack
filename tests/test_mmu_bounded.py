"""Bounded exhaustive check of the real mmu_init(): every 4 KiB page of the low 4 GiB, of the
MMIO window and of the corresponding TTBR1 alias windows is translated by a software walk of
the C-built tables and compared with the intended mapping (first region wins, identity map,
attributes per section). Kernel/user separation and W^X are checked on the C tables directly."""
import random

from drivers import (KVA, PROTS, QEMU_VIRT, RPI5, c_mmu, intended_runs, layout_cmd, layout_regions,
                     parse_dumps, run)

EL0 = 1 << 6
RO = 1 << 7
PXN = 1 << 53
UXN = 1 << 54
STATS = {}


def windows(L):
    return [("lo", 0, 1 << 32), ("lo", L["devb"], L["devb"] + L["devs"]),
            ("hi", KVA, KVA + (1 << 32)), ("hi", KVA + L["devb"], KVA + L["devb"] + L["devs"])]


def check_layout(L):
    lo_regs, hi_regs = layout_regions(L)
    wins = windows(L)
    cmds = [layout_cmd(L)] + [f"dump {r} {a:x} {b:x}" for r, a, b in wins] + ["tables"]
    out = run([c_mmu()], cmds, timeout=1200)
    tables = int(out[-1])
    dumps = parse_dumps(out[:-1])
    walked = sum((b - a) // 4096 for _, a, b in wins)
    mapped = 0
    for (root, a, b), got in zip(wins, dumps):
        want = intended_runs(lo_regs if root == "lo" else hi_regs, a, b)
        assert got == want, f"{root} [{a:#x},{b:#x}) differs from the intended mapping"
        for va, pa, n, at in got:
            mapped += n
            if root == "lo":
                assert va == pa                                   # identity map
            el0 = bool(at & EL0)
            in_user = (L["uts"] <= va < L["ute"]) or (L["uss"] <= va < L["use"])
            assert el0 == (root == "lo" and in_user)              # no kernel/user aliasing
            assert (at & RO) or (at & PXN)                        # W^X at EL1
            assert not (el0 and not (at & RO) and not (at & UXN))  # W^X at EL0
    assert tables <= 48                                           # NTABLES pool never exhausted
    return walked, mapped, tables


def test_qemu_virt_exhaustive():
    STATS["qemu-virt"] = check_layout(QEMU_VIRT)


def test_rpi5_exhaustive():
    STATS["rpi5"] = check_layout(RPI5)


def test_random_layouts():
    rng = random.Random(5)
    for _ in range(25):
        base = rng.randrange(0, 1 << 31, 1 << 21)
        syms = [base + rng.randrange(0, 1 << 20, 4096)]
        for _ in range(7):
            syms.append(syms[-1] + rng.randrange(0, 64) * 4096)
        rams = rng.choice([128, 256, 1024, 4096, 8192]) << 20
        L = dict(zip(["ks", "uts", "ute", "te", "re", "uss", "use", "end"], syms),
                 ramb=base, rams=rams, devb=rng.randrange(0, 1 << 33, 1 << 21) | (1 << 34),
                 devs=rng.randrange(1, 64) << 20, dtb=0, dtbs=0)
        if rng.random() < 0.5:
            L["dtb"] = base + rng.randrange(0, rams // 2, 4096)
            L["dtbs"] = rng.randrange(4096, 1 << 20, 4096)
        check_layout(L)


def test_unaligned_dtb_outside_ram_is_fully_mapped():
    """mmu_init with a DTB outside the mapped RAM at an unaligned address. orbit-os <= 49ede1e
    left the last page of the blob unmapped (found here; Lean: Mmu.unaligned_bug); since
    1a8385b every page the blob touches is mapped (Mmu.mapRange_spec_unaligned)."""
    L = dict(QEMU_VIRT, rams=64 << 20, dtb=0x4F000800, dtbs=0x1000)
    lo_regs, _ = layout_regions(L)
    out = parse_dumps(run([c_mmu()], [layout_cmd(L), "dump lo 4f000000 4f004000"]))
    want = intended_runs(lo_regs, 0x4F000000, 0x4F004000)
    assert want == [(0x4F000000, 0x4F000000, 2, PROTS["KRO"])]
    assert out == [want]
