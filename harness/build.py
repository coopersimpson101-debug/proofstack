#!/usr/bin/env python3
"""Build the host drivers for orbit-os's buddy allocator and page-table code with zig cc.

    python harness/build.py --orbit-os PATH/TO/orbit-os [--out build/harness]

`buddy.c` and `lib/a64pt.c` are compiled unmodified. `arch/aarch64/mmu.c` is copied with exactly its three inline-asm
statements removed (TLBI / IC IALLU maintenance and the AT S1E1R probe in mmu_translate):
they cannot be assembled for x86-64 and do not read or write page-table memory.  The
generated kernel.h is the real one with the linker-script `extern char sym[]` declarations
replaced by run-time settable values; everything else (struct platform, ALIGN_* macros) is
taken verbatim.
"""
from __future__ import annotations

import argparse
import hashlib
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SYMS = ["__kernel_start", "__user_text_start", "__user_text_end", "__text_end", "__rodata_end",
        "__user_stack_start", "__user_stack_end", "_end"]
ASM = re.compile(r'__asm__ volatile\("(?:[^"\\]|\\.)*"(?:\s*:[^;]*)?\);')


def zig():
    return [sys.executable, "-m", "ziglang"]


def build(orbit: Path, out: Path) -> dict:
    out.mkdir(parents=True, exist_ok=True)
    inc = orbit / "kernel" / "include"
    gen = out / "gen"
    gen.mkdir(exist_ok=True)
    mmu_src = orbit / "kernel" / "arch" / "aarch64" / "mmu.c"
    a64pt = orbit / "kernel" / "lib" / "a64pt.c"
    if not (mmu_src.exists() and a64pt.exists()):
        raise SystemExit("expected orbit-os with kernel/arch/aarch64/mmu.c and kernel/lib/a64pt.c "
                         "(the commit pinned in CI); older layouts are not supported")
    mmu = mmu_src.read_text(encoding="utf-8")
    stripped, n = ASM.subn("/* inline asm removed for the host build */;", mmu)
    if n != 3:
        raise SystemExit(f"expected exactly 3 inline-asm statements in mmu.c, found {n}")
    (gen / "mmu_stripped.c").write_text(stripped, encoding="utf-8")
    kh = (inc / "kernel.h").read_text(encoding="utf-8")
    kh2, n = re.subn(r"extern char __kernel_start\[\][^;]*;\s*extern char __text_end\[\][^;]*;\s*"
                     r"extern char __user_stack_start\[\][^;]*;",
                     "extern uint64_t hs_sym[8];\n" + "\n".join(
                         f"#define {s} ((char *)(uintptr_t)hs_sym[{k}])" for k, s in enumerate(SYMS)),
                     kh, flags=re.S)
    if n != 1:
        raise SystemExit("could not find the linker-symbol declarations in kernel.h")
    (gen / "kernel.h").write_text(kh2, encoding="utf-8")
    exe = ".exe" if os.name == "nt" else ""
    flags = ["-std=gnu11", "-O2", "-Wall", "-Wno-unused-function", "-Wno-unused-variable"]
    cmds = {
        "buddy_driver": zig() + ["cc", *flags, f"-I{inc}", str(HERE / "buddy_driver.c"),
                                 str(orbit / "kernel" / "mm" / "buddy.c"), "-o", str(out / f"buddy_driver{exe}")],
        "mmu_driver": zig() + ["cc", *flags, f"-I{HERE / 'stubs'}", f"-I{gen}", f"-I{inc}",
                               str(HERE / "mmu_driver.c"), str(a64pt), "-o", str(out / f"mmu_driver{exe}")],
    }
    for name, cmd in cmds.items():
        r = subprocess.run(cmd, capture_output=True, text=True)
        if r.returncode:
            raise SystemExit(f"{name} failed:\n{r.stdout}{r.stderr}")
    src = {p: hashlib.sha256((orbit / p).read_bytes()).hexdigest()[:16]
           for p in ["kernel/mm/buddy.c", "kernel/arch/aarch64/mmu.c", "kernel/lib/a64pt.c",
                     "kernel/include/buddy.h", "kernel/include/list.h"]}
    return {"buddy_driver": str(out / f"buddy_driver{exe}"), "mmu_driver": str(out / f"mmu_driver{exe}"),
            "sources": src}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--orbit-os", required=True, type=Path)
    ap.add_argument("--out", type=Path, default=HERE.parent / "build" / "harness")
    a = ap.parse_args()
    print(build(a.orbit_os.resolve(), a.out.resolve()))


if __name__ == "__main__":
    main()
