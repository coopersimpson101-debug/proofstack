#!/usr/bin/env python3
"""Run TLC on named models of tla/RaftStore.tla and record the real output.

    python scripts/run_tlc.py core3 snapshots3 ...     # or --all / --xcheck
Env: JAVA (default "java"), TLA2TOOLS (path to tla2tools.jar), TLC_WORKERS (default 8).
Writes tla/models/<name>.cfg, results/tlc/<name>.log (TLC stdout, local paths scrubbed)
and results/tlc/<name>.json (states generated / distinct, depth, seconds, verdict).
"""
from __future__ import annotations

import argparse
import json
import os
import platform
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from proofstack.models import MODELS, cfg_text, model  # noqa: E402

TLA = ROOT / "tla"
RES = ROOT / "results" / "tlc"


def scrub(text: str) -> str:
    text = re.sub(r"Parsing file .*?([A-Za-z]+\.tla)", r"Parsing file \1", text)
    text = re.sub(r"\[pid: \d+\] \(.*?\)", "", text)
    text = re.sub(r"(?i)[A-Z]:\\[^\s]*|/(?:home|Users|tmp)/[^\s]*", "<path>", text)
    return text


def parse(out: str) -> dict:
    d = {}
    m = re.findall(r"([\d,]+) states generated, ([\d,]+) distinct states found, ([\d,]+) states left on queue", out)
    if m:
        g, dist, left = m[-1]
        d.update(generated=int(g.replace(",", "")), distinct=int(dist.replace(",", "")),
                 left=int(left.replace(",", "")))
    m = re.search(r"The depth of the complete state graph search is (\d+)", out)
    if m:
        d["depth"] = int(m.group(1))
    m = re.search(r"Error: Invariant (\w+) is violated", out)
    d["violated"] = m.group(1) if m else None
    d["no_error"] = "Model checking completed. No error has been found." in out
    d["trace_states"] = len(re.findall(r"^State \d+:", out, re.M))
    m = re.findall(r"Progress\(\d+\) at [^:]+:\d+:\d+: ([\d,]+) states generated \([^)]*\), ([\d,]+) distinct", out)
    if m and "distinct" not in d:   # incomplete run: last progress report
        d["generated"] = int(m[-1][0].replace(",", ""))
        d["distinct_so_far"] = int(m[-1][1].replace(",", ""))
    m = re.findall(r"Progress: ([\d,]+) states checked", out)
    if m:
        d["sim_states_checked"] = int(m[-1].replace(",", ""))
    d["finished"] = "Finished in" in out and "Error:" not in out
    m = re.findall(r"([\d,]+) states generated", out)
    if m and "generated" not in d:
        d["generated"] = int(m[-1].replace(",", ""))
    return d


def run(name: str, workers: int, timeout: float | None = None) -> dict:
    (TLA / "models").mkdir(exist_ok=True)
    cfg = TLA / "models" / f"{name}.cfg"
    cfg.write_text(cfg_text(name), encoding="utf-8", newline="\n")
    java = os.environ.get("JAVA", "java")
    jar = os.environ.get("TLA2TOOLS", "tla2tools.jar")
    with tempfile.TemporaryDirectory() as meta:
        cmd = [java, "-XX:+UseParallelGC", "-cp", jar, "tlc2.TLC", "-workers", str(workers),
               "-metadir", meta, "-config", str(cfg), "-deadlock"]
        if model(name)["simulate"]:
            # random behaviours up to depth 100; stops at the first invariant violation
            cmd += ["-simulate", f"num={model(name)['sim_traces']}", "-depth", "100", "-seed", "1"]
        cmd.append(str(TLA / "MCRaftStore.tla"))
        t0 = time.time()
        try:
            p = subprocess.run(cmd, cwd=TLA, capture_output=True, text=True, timeout=timeout)
            out, rc = p.stdout + p.stderr, p.returncode
        except subprocess.TimeoutExpired as e:
            out = ((e.stdout or b"").decode() if isinstance(e.stdout, bytes) else (e.stdout or ""))
            out += f"\n*** stopped by run_tlc.py after {timeout:.0f} s (incomplete) ***\n"
            rc = -1
        secs = time.time() - t0
    RES.mkdir(parents=True, exist_ok=True)
    (RES / f"{name}.log").write_text(scrub(out), encoding="utf-8", newline="\n")
    d = parse(out)
    d.update(model=name, seconds=round(secs, 1), workers=workers, exit=rc,
             machine=f"{platform.system()} {platform.machine()}, {os.cpu_count()} logical CPUs",
             date=time.strftime("%Y-%m-%d"))
    (RES / f"{name}.json").write_text(json.dumps(d, indent=1) + "\n", encoding="utf-8", newline="\n")
    return d


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("names", nargs="*")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--xcheck", action="store_true")
    ap.add_argument("--workers", type=int, default=int(os.environ.get("TLC_WORKERS", 8)))
    ap.add_argument("--timeout", type=float, default=None, help="seconds per model")
    a = ap.parse_args()
    names = list(MODELS) if a.all else [n for n in MODELS if n.startswith("xcheck")] if a.xcheck else a.names
    rc = 0
    for n in names:
        # cross-check models run single-threaded: TLC's reported depth is exact only with one worker
        d = run(n, 1 if n.startswith("xcheck") else a.workers, a.timeout)
        want_bug = n.startswith("mut-")
        if want_bug:
            ok = d["violated"] is not None
        elif model(n)["simulate"]:
            ok = d["finished"] and d["exit"] == 0
        else:
            ok = d["no_error"]
        print(f"{'OK  ' if ok else 'FAIL'} {n}: {d}", flush=True)
        rc |= not ok
    return rc


if __name__ == "__main__":
    sys.exit(main())
