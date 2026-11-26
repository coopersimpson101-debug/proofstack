"""Locate and run the C drivers (harness/) and the Lean model executable (lean/)."""
from __future__ import annotations

import os
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
EXE = ".exe" if os.name == "nt" else ""
HARNESS = Path(os.environ.get("PROOFSTACK_HARNESS", ROOT / "build" / "harness"))
ORBITMODEL = Path(os.environ.get("ORBITMODEL", ROOT / "lean" / ".lake" / "build" / "bin" / f"orbitmodel{EXE}"))

KVA = 0xFFFF000000000000
PROTS = {"KDATA": 0x60000000000708, "KTEXT": 0x40000000000788, "KRO": 0x60000000000788,
         "UTEXT": 0x200000000007C8, "UDATA": 0x60000000000748, "DEVICE": 0x60000000000404}


def _need(p: Path, what: str) -> Path:
    if not p.exists():
        pytest.skip(f"{what} not built ({p}); see README 'Quickstart'")
    return p


def c_buddy() -> Path:
    return _need(HARNESS / f"buddy_driver{EXE}", "C buddy driver (python harness/build.py)")


def c_mmu() -> Path:
    return _need(HARNESS / f"mmu_driver{EXE}", "C MMU driver (python harness/build.py)")


def lean_model() -> Path:
    return _need(ORBITMODEL, "Lean model executable (cd lean && lake build)")


def run_raw(cmd, lines: list[str], timeout=600) -> tuple[int, list[str]]:
    p = subprocess.run([str(c) for c in cmd], input="\n".join(lines) + "\n", capture_output=True,
                       text=True, timeout=timeout)
    return p.returncode, p.stdout.splitlines()


def run(cmd, lines: list[str], timeout=600) -> list[str]:
    rc, out = run_raw(cmd, lines, timeout)
    if rc != 0:
        raise AssertionError(f"{cmd} exited with status {rc}")
    return out


def parse_dumps(out: list[str]) -> list[list[tuple[int, int, int, int]]]:
    """Split driver output into dumps; each dump is a list of (va, pa, npages, attrs) runs."""
    dumps, cur = [], None
    for line in out:
        if line == "end":
            dumps.append(cur or [])
            cur = None
        elif line == "ok":
            continue
        else:
            cur = cur or []
            cur.append(tuple(int(w, 16) for w in line.split()))
    return dumps


def intended_runs(regions, lo: int, hi: int):
    """The mapping the kernel intends: every 4 KiB page that overlaps [va, va+size) of the first
    region containing it maps to pa + offset with that region's attributes."""
    taken: list[tuple[int, int]] = []          # page-index intervals already mapped
    pieces = []
    for va, pa, size, prot in regions:
        if size == 0:
            continue
        a, b = va // 4096, -(-(va + size) // 4096)
        segs = [(a, b)]
        for (x, y) in taken:
            nxt = []
            for (s, e) in segs:
                if e <= x or y <= s:
                    nxt.append((s, e))
                else:
                    if s < x:
                        nxt.append((s, x))
                    if y < e:
                        nxt.append((y, e))
            segs = nxt
        for (s, e) in segs:
            pieces.append((s, e, pa // 4096 + (s - va // 4096), prot))
        taken.append((a, b))
    lo_p, hi_p = lo // 4096, hi // 4096
    clipped = []
    for s, e, p, prot in pieces:
        s2, e2 = max(s, lo_p), min(e, hi_p)
        if s2 < e2:
            clipped.append((s2, e2, p + (s2 - s), prot))
    clipped.sort()
    runs = []
    for s, e, p, prot in clipped:
        if runs and runs[-1][0] // 4096 + runs[-1][2] == s and runs[-1][1] // 4096 + runs[-1][2] == p \
                and runs[-1][3] == prot:
            rva, rpa, rn, rp = runs[-1]
            runs[-1] = (rva, rpa, rn + (e - s), rp)
        else:
            runs.append((s * 4096, p * 4096, e - s, prot))
    return runs


def layout_regions(L: dict):
    """mmu_init's region lists (TTBR0 identity map, TTBR1 alias) for a layout."""
    up = lambda x: (x + 4095) & ~4095  # noqa: E731
    ramm = min(L["rams"], 4 << 30)
    ident = []
    for a, b, p in [(L["ks"], L["uts"], "KTEXT"), (L["uts"], L["ute"], "UTEXT"), (L["ute"], L["te"], "KTEXT"),
                    (L["te"], L["re"], "KRO"), (L["re"], L["uss"], "KDATA"), (L["uss"], L["use"], "UDATA"),
                    (L["use"], up(L["end"]), "KDATA")]:
        if b > a:
            ident.append((a, a, b - a, PROTS[p]))
    lo = ident + [(L["ramb"], L["ramb"], ramm, PROTS["KDATA"])]
    if L["dtb"]:
        lo.append((L["dtb"], L["dtb"], L["dtbs"], PROTS["KRO"]))
    lo.append((L["devb"], L["devb"], L["devs"], PROTS["DEVICE"]))
    hi = [(KVA + L["ramb"], L["ramb"], ramm, PROTS["KDATA"]), (KVA + L["devb"], L["devb"], L["devs"], PROTS["DEVICE"])]
    return lo, hi


def layout_cmd(L: dict) -> str:
    keys = ["ks", "uts", "ute", "te", "re", "uss", "use", "end", "ramb", "rams", "devb", "devs", "dtb", "dtbs"]
    return "layout " + " ".join(f"{L[k]:x}" for k in keys)


# qemu-virt kernel image layout as documented in orbit-os docs/memory-map.md (`__text_end`
# is not listed there; 0x4008e000 lies between the documented neighbours).
QEMU_VIRT = dict(ks=0x40080000, uts=0x40081000, ute=0x40082000, te=0x4008E000, re=0x40091000,
                 uss=0x400C5000, use=0x400C9000, end=0x400CD000, ramb=0x40000000, rams=256 << 20,
                 devb=0x08000000, devs=0x08000000, dtb=0x48000000, dtbs=0x100000)
# Raspberry Pi 5 build: same image layout shifted to KERNEL_BASE = 0x80000, 4 GiB RAM at 0,
# SoC window 0x10_7c00_0000..0x10_8000_0000 (docs/memory-map.md).
RPI5 = {**{k: v - 0x40000000 for k, v in QEMU_VIRT.items() if k in
           ("ks", "uts", "ute", "te", "re", "uss", "use", "end")},
        "ramb": 0, "rams": 4 << 30, "devb": 0x107C000000, "devs": 0x4000000, "dtb": 0x2E000000, "dtbs": 0x10000}
