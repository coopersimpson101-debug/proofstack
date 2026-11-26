#!/usr/bin/env python3
"""Validate a corpus of raftstore traces against the spec and write a summary.

    python scripts/validate_traces.py --sim traces/sim --cluster traces/cluster --out results/tracecheck.json
"""
from __future__ import annotations

import argparse
import glob
import json
import os
import platform
import sys
import time
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from proofstack.tracecheck import Violation, check_cluster, check_file  # noqa: E402

KEYS = ("events", "messages_checked", "elections", "restarts", "reads_released", "ev_propose",
        "ev_step", "ev_tick", "ev_compact", "ev_read_index", "ev_transfer_leadership",
        "ev_propose_conf_change", "committed_entries", "restart_commit_rollback", "restart_torn_batch")


def one(job):
    kind, path = job
    t0 = time.time()
    try:
        st = check_file(path) if kind == "sim" else check_cluster(path)
        return kind, path, None, {k: st.get(k, 0) for k in KEYS}, time.time() - t0
    except Violation as e:
        return kind, path, str(e)[:500], {}, time.time() - t0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sim")
    ap.add_argument("--cluster")
    ap.add_argument("--out", required=True)
    ap.add_argument("--jobs", type=int, default=os.cpu_count() // 2 or 1)
    a = ap.parse_args()
    jobs = []
    if a.sim:
        jobs += [("sim", p) for p in sorted(glob.glob(os.path.join(a.sim, "*.jsonl")))]
    if a.cluster:
        jobs += [("cluster", p) for p in sorted(glob.glob(os.path.join(a.cluster, "run-*")))]
    t0 = time.time()
    with ProcessPoolExecutor(a.jobs) as ex:
        results = list(ex.map(one, jobs))
    by = {}
    failures = []
    for kind, path, err, st, secs in results:
        scen = os.path.basename(path).rsplit("-", 1)[0] if kind == "sim" else "multi-process (kill -9 leader x2)"
        agg = by.setdefault(scen, Counter())
        agg["traces"] += 1
        agg["ok"] += err is None
        agg.update(st)
        if err:
            failures.append({"trace": os.path.basename(path), "error": err})
    total = sum(by.values(), Counter())
    summary = {"date": time.strftime("%Y-%m-%d"),
               "machine": f"{platform.system()} {platform.machine()}, {os.cpu_count()} logical CPUs",
               "seconds": round(time.time() - t0, 1), "total": dict(total),
               "by_scenario": {k: dict(v) for k, v in by.items()}, "failures": failures}
    os.makedirs(os.path.dirname(os.path.abspath(a.out)), exist_ok=True)
    with open(a.out, "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=1)
    print(json.dumps({"traces": total["traces"], "ok": total["ok"], "events": total["events"],
                      "failures": len(failures), "seconds": summary["seconds"]}))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
