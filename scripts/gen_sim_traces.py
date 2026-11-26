#!/usr/bin/env python3
"""Record execution traces from raftstore's deterministic simulator.

    python scripts/gen_sim_traces.py --raftstore ../raftstore --out traces/sim --seeds 40 --steps 1500

Runs the simulator scenarios of raftstore's own test-suite (minus lease reads, which the TLA+
model does not cover) with `SimCluster(..., trace_path=...)`, one JSON-lines file per run.
Each run also passes raftstore's own end-of-run checks (linearizability, no acked write lost).
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time

SCENARIOS = {
    "lossy-net+crashes+partitions": dict(),
    "five-nodes+leadership-transfer": dict(nodes=5, p_transfer=0.005),
    "membership-changes": dict(p_membership=0.01, p_transfer=0.005),
    "no-prevote/no-checkquorum": dict(raft={"prevote": False, "check_quorum": False}),
    "real-WAL-on-faulty-disk+drive-pulls": dict(storage="disk", p_pull_drive=0.003),
    "everything-at-once": dict(storage="disk", p_pull_drive=0.002, p_membership=0.008, p_transfer=0.004),
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--raftstore", required=True, help="path to a raftstore checkout (main at 3a545c8 or later)")
    ap.add_argument("--out", required=True)
    ap.add_argument("--seeds", type=int, default=40)
    ap.add_argument("--steps", type=int, default=1500)
    a = ap.parse_args()
    sys.path.insert(0, os.path.abspath(a.raftstore))
    from raftstore.sim.cluster import SimCluster, SimConfig  # noqa: E402

    os.makedirs(a.out, exist_ok=True)
    index = []
    t0 = time.time()
    for name, kw in SCENARIOS.items():
        slug = name.replace("/", "_").replace("+", "_")
        for seed in range(a.seeds):
            path = os.path.join(a.out, f"{slug}-{seed:03d}.jsonl")
            if os.path.exists(path):
                os.remove(path)
            c = SimCluster(seed, SimConfig(**kw), trace_path=path)
            c.run(a.steps)
            c.heal()
            ok = c.check_linearizable().ok
            acked = c.check_no_acked_write_lost()
            c.close_trace()
            s = c.summary()
            index.append({"file": os.path.basename(path), "scenario": name, "seed": seed,
                          "linearizable": ok, "acked_writes": acked, **{k: s[k] for k in
                          ("steps", "crashes", "partitions", "transfers", "member_adds", "member_removes",
                           "msgs_dropped", "msgs_duplicated")}})
    with open(os.path.join(a.out, "index.json"), "w", encoding="utf-8") as f:
        json.dump(index, f, indent=1)
    print(f"{len(index)} traces in {time.time() - t0:.0f}s -> {a.out}")


if __name__ == "__main__":
    main()
