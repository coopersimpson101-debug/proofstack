#!/usr/bin/env python3
"""Record execution traces from real multi-process raftstore clusters on localhost.

    python scripts/gen_cluster_traces.py --raftstore ../raftstore --out traces/cluster --runs 20

Each run starts three `raftstore serve` processes (raftstore.devcluster.DevCluster) with
RAFTSTORE_TRACE_DIR set, drives concurrent linearizable reads and writes from four client
threads, SIGKILLs (TerminateProcess on Windows) the leader twice and restarts it from its
WAL, and leaves one `<node>.jsonl` trace per process in `<out>/run-NNN/`.
"""
from __future__ import annotations

import argparse
import json
import os
import random
import shutil
import sys
import tempfile
import threading
import time


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--raftstore", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--runs", type=int, default=20)
    ap.add_argument("--seconds", type=float, default=10.0)
    a = ap.parse_args()
    sys.path.insert(0, os.path.abspath(a.raftstore))
    from raftstore.client import Client  # noqa: E402
    from raftstore.devcluster import DevCluster  # noqa: E402

    os.makedirs(a.out, exist_ok=True)
    index = []
    for run in range(a.runs):
        tdir = os.path.abspath(os.path.join(a.out, f"run-{run:03d}"))
        shutil.rmtree(tdir, ignore_errors=True)
        os.makedirs(tdir)
        os.environ["RAFTSTORE_TRACE_DIR"] = tdir
        work = tempfile.mkdtemp(prefix="rs-")
        dc = DevCluster(work, tick_ms=50, extra={"snapshot_every": 60})
        stats = {"writes": 0, "reads": 0, "errors": 0, "kills": 0}
        lock = threading.Lock()
        try:
            dc.start_all()
            dc.wait_leader(30)
            deadline = time.monotonic() + a.seconds

            def client(cid):
                rng = random.Random(run * 100 + cid)
                cl = Client(dc.urls(), timeout=3, retries=10)
                while time.monotonic() < deadline:
                    key = rng.choice("xyz")
                    try:
                        if rng.random() < 0.5:
                            cl.put(key, str(rng.random()).encode())
                            k = "writes"
                        else:
                            cl.get(key)
                            k = "reads"
                    except Exception:  # noqa: BLE001 - outcome unknown during failover
                        k = "errors"
                    with lock:
                        stats[k] += 1

            threads = [threading.Thread(target=client, args=(i,)) for i in range(4)]
            for t in threads:
                t.start()
            for _ in range(2):
                time.sleep(a.seconds / 4)
                lead = dc.leader()
                if lead:
                    dc.kill(lead)
                    stats["kills"] += 1
                    time.sleep(1.0)
                    dc.start(lead)
            for t in threads:
                t.join()
            dc.wait_converged(timeout=30)
        finally:
            dc.stop_all()
            shutil.rmtree(work, ignore_errors=True)
        index.append({"run": run, **stats})
        print(f"run {run}: {stats}", flush=True)
    os.environ.pop("RAFTSTORE_TRACE_DIR", None)
    with open(os.path.join(a.out, "index.json"), "w", encoding="utf-8") as f:
        json.dump(index, f, indent=1)


if __name__ == "__main__":
    main()
