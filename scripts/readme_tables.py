#!/usr/bin/env python3
"""Fill the result tables in README.md from results/ (never edit those tables by hand)."""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from proofstack.models import MODELS, model  # noqa: E402

LABEL = {
    "lossy-net_crashes_partitions": "simulator: lossy net + crashes + partitions",
    "five-nodes_leadership-transfer": "simulator: 5 nodes + leadership transfer",
    "membership-changes": "simulator: membership changes",
    "no-prevote_no-checkquorum": "simulator: no PreVote / no CheckQuorum",
    "real-WAL-on-faulty-disk_drive-pulls": "simulator: real WAL on faulty disk + drive pulls",
    "everything-at-once": "simulator: everything at once",
    "multi-process (kill -9 leader x2)": "real 3-process clusters, leader `kill -9` ×2",
}


def bounds(name):
    m = model(name)
    parts = [f"{len(m['servers'])} srv" + (f" ({len(m['voters'])} voters)" if m["voters"] != m["servers"] else ""),
             f"term≤{m['MaxTerm']}", f"log≤{m['MaxLogLen']}", f"msgs≤{m['MaxMsgs']}"]
    for k, lab in [("MaxValues", "writes"), ("MaxCrashes", "crashes"), ("MaxReads", "reads"),
                   ("MaxTransfers", "transfers"), ("MaxCompactions", "compactions"),
                   ("MaxConfChanges", "conf changes")]:
        if m[k]:
            parts.append(f"{lab}≤{m[k]}")
    flags = [f for f in ("LossyCommit", "UnsafeCommitAnyTerm", "SkipTermStartCheck", "MutNoNoop", "MutVoteAnyLog")
             if m[f]]
    if not m["PreVote"]:
        flags.append("no PreVote")
    if not m["CheckQuorum"]:
        flags.append("no CheckQuorum")
    if m["symmetry"]:
        flags.append("symmetry")
    return ", ".join(parts + flags)


def tlc_table():
    rows = ["| model | bounds | mode | result | states generated | distinct states | depth | time (s) |",
            "|---|---|---|---|---:|---:|---:|---:|"]
    for name in MODELS:
        p = ROOT / "results" / "tlc" / f"{name}.json"
        if not p.exists():
            continue
        r = json.loads(p.read_text())
        m = model(name)
        if m["simulate"]:
            mode = f"simulation, {m['sim_traces']:,} behaviours ≤ depth 100"
            res = "no violation" if r.get("finished") else ("**" + str(r.get("violated")) + "**" if r.get("violated")
                                                            else "stopped (time limit)")
            gen, dist, depth = r.get("sim_states_checked", 0), "—", "—"
        else:
            mode = "BFS" + (" (stops at counterexample)" if name.startswith("mut-") else "")
            if r.get("violated"):
                res = f"**{r['violated']} violated** ({r['trace_states']}-state trace)"
            elif r.get("no_error") and name.startswith("mut-"):
                res = "**not refuted**: no violation, complete"
            elif r.get("no_error"):
                res = "no violation, complete"
            else:
                res = "stopped (time limit), no violation so far"
            if "distinct" in r:
                dist = f"{r['distinct']:,}"
            else:
                dist = f"≥ {r.get('distinct_so_far', 0):,} (incomplete)"
            gen, depth = r.get("generated", 0), r.get("depth", "—")
        rows.append(f"| `{name}` | {bounds(name)} | {mode} | {res} | {gen:,} | {dist} | {depth} | {r['seconds']:.0f} |")
    return "\n".join(rows)


def trace_table():
    d = json.loads((ROOT / "results" / "tracecheck.json").read_text())
    rows = ["| source | traces (ok) | events | messages | elections | restarts (torn batch) | reads released | conf changes | transfers |",
            "|---|---:|---:|---:|---:|---:|---:|---:|---:|"]
    for k, v in d["by_scenario"].items():
        rows.append(f"| {LABEL.get(k, k)} | {v['traces']} ({v['ok']}) | {v.get('events', 0):,} | "
                    f"{v.get('messages_checked', 0):,} | {v.get('elections', 0):,} | {v.get('restarts', 0):,} "
                    f"({v.get('restart_torn_batch', 0)}) | {v.get('reads_released', 0):,} | "
                    f"{v.get('ev_propose_conf_change', 0):,} | {v.get('ev_transfer_leadership', 0):,} |")
    t = d["total"]
    rows.append(f"| **total** | **{t['traces']} ({t['ok']})** | **{t['events']:,}** | **{t['messages_checked']:,}** | "
                f"**{t['elections']:,}** | **{t['restarts']:,} ({t.get('restart_torn_batch', 0)})** | "
                f"**{t['reads_released']:,}** | **{t.get('ev_propose_conf_change', 0):,}** | "
                f"**{t.get('ev_transfer_leadership', 0):,}** |")
    rows.append("")
    rows.append(f"<sub>{d['machine']}, {d['date']}; validation took {d['seconds']:.0f} s with 6 processes.</sub>")
    return "\n".join(rows)


def main():
    p = ROOT / "README.md"
    t = p.read_text(encoding="utf-8")
    for tag, body in (("TLC-TABLE", tlc_table()), ("TRACE-TABLE", trace_table())):
        t = re.sub(rf"<!-- {tag} -->.*?<!-- /{tag} -->", f"<!-- {tag} -->\n{body}\n<!-- /{tag} -->", t, flags=re.S)
    p.write_text(t, encoding="utf-8", newline="\n")
    print("README tables updated")


if __name__ == "__main__":
    main()
