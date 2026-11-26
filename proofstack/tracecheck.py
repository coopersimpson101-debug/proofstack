"""Refinement checker: replay raftstore execution traces against the RaftStore spec.

Approach (a Python refinement checker, not TLC trace validation): the checker keeps one
*spec* local state per node, built only from spec actions (``proofstack.raftspec``, the
transcription of tla/RaftStore.tla).  For every traced call of the implementation it
enumerates the successors the spec allows for that node and that input -- the
nondeterminism is exactly the spec's: whether a timer fired, whether leader stickiness
ignored a vote, which tick branch ran -- and requires that one of them reproduces the
implementation's logged

* post-state: term, vote, role, leader, commit, snapshot point, last index/term, voter set,
  config index, vote tally, per-peer match/next/acked-ctx, term-start index, transfer target,
  read sequence number, pending and waiting ReadIndex requests;
* log: the entries after the snapshot point, reconstructed from the logged log mutations;
* sent messages, as a set, field by field (entries included);
* released ReadIndex results.

Inputs are linked across nodes: a delivered message must be one that its sender's checked
event emitted (so the spec message, including the snapshot image, is known).  Restarts must
resume from a state the node had at one of its last `ready` (persist) points.  On top of the
per-step refinement, the checker tracks the spec's history variables over the whole run and
checks Election Safety, State Machine Safety, Leader Completeness, linearizable ReadIndex
(index >= global commit at call time) and, at the end, Log Matching between all nodes.

    python -m proofstack.tracecheck TRACE.jsonl [TRACE2.jsonl ...]
    python -m proofstack.tracecheck --cluster DIR      # one <node>.jsonl per process
"""
from __future__ import annotations

import argparse
import glob
import json
import os
import sys
from collections import Counter, defaultdict

from .raftspec import E, Flags, M, Ret, Spec

ROLE = {"follower": "F", "pre-candidate": "PC", "candidate": "C", "leader": "L"}
KIND = {0: "normal", 1: "config", 2: "noop"}


class Violation(Exception):
    pass


def load_lines(path):
    out = []
    with open(path, encoding="utf-8") as f:
        lines = f.read().split("\n")
    for k, line in enumerate(lines):
        if not line.strip():
            continue
        try:
            out.append(json.loads(line))
        except json.JSONDecodeError:
            if k >= len(lines) - 2:      # torn final line of a SIGKILLed process
                continue
            raise
    return out


class Checker:
    def __init__(self, events_by_node: dict, ordered: list | None = None):
        self.by_node = events_by_node
        self.ordered = ordered
        ids, voters, opts = set(), None, None
        for evs in events_by_node.values():
            for ev in evs:
                if "n" in ev:
                    ids.add(ev["n"])
                if ev.get("ev") == "init":
                    opts = opts or ev["args"]["options"]
                    for e in ev["args"]["entries"]:
                        if e[2] == 1 and e[3]["op"] == "bootstrap":
                            voters = voters or frozenset(e[3]["voters"])
                for m in ev.get("out", []):
                    ids.add(m["dst"])
        if opts is None:
            raise Violation("trace has no init event")
        if opts["read_only"] != "safe":
            raise Violation("lease-mode traces are outside the model (ReadIndex only)")
        self.boot_voters = voters or frozenset()
        self.sp = Spec(sorted(ids), self.boot_voters,
                       Flags(prevote=opts["prevote"], check_quorum=opts["check_quorum"],
                             unsafe_commit_any_term=opts["unsafe_commit_any_term"]))
        self.r = {}              # spec local state per node
        self.ready_hist = defaultdict(list)
        self.mirror = {}         # impl log after snapshot: (snap, snap_term, {index: E})
        self.pool = defaultdict(list)   # message key -> spec messages
        self.committed = {}      # idx -> (E, term)
        self.leaders = {}        # term -> node
        self.read_gc = {}        # (node, ctx) -> global commit at call time
        self.stats = Counter()

    # ---------------------------------------------------------------- conversions
    def ent(self, j) -> E:
        term, _idx, kind, payload = j
        if kind == 1:
            op = payload["op"]
            if op == "bootstrap":
                if frozenset(payload["voters"]) != self.boot_voters:
                    raise Violation("two different bootstrap configurations")
                return E(term, "config", 0, "boot", None)
            return E(term, "config", 0, op, payload["id"])
        if kind == 2:
            return E(term, "noop")
        return E(term, "normal", payload)

    def ikey(self, m: dict):
        ents = tuple(self.ent(e) for e in m["entries"])
        for k, e in enumerate(m["entries"]):
            if e[1] != m["index"] + 1 + k:
                raise Violation(f"non-contiguous entries in message {m}")
        snap = (m["snapshot"]["index"], m["snapshot"]["term"]) if "snapshot" in m else None
        return (m["type"], m["src"], m["dst"], m["term"], m["index"], m["log_term"], ents, m["commit"],
                m["reject"], m["hint_index"], m["hint_term"], m["ctx"], snap, m["transfer"])

    @staticmethod
    def skey(m: M):
        snap = (m.snap.index, m.snap.term) if m.type == "snapshot" else None
        return (m.type, m.src, m.dst, m.term, m.index, m.logTerm, m.entries, m.commit, m.reject,
                m.hintIndex, m.hintTerm, m.ctx, snap, m.transfer)

    # ---------------------------------------------------------------- comparison
    def diff(self, i, cand: Ret, ev) -> str | None:
        sp, r, p = self.sp, cand.r, ev["post"]
        want = {
            "term": r["term"], "vote": r["vote"], "state": r["state"], "leader": r["leader"],
            "commit": r["commit"], "snap": r["snap"], "snap_term": sp.snap_term(r),
            "last": sp.last_index(r), "last_term": sp.last_term(r), "voters": sorted(r["cfg"]),
            "cidx": r["cidx"],
            "votes": {**{v: True for v in r["vg"]}, **{v: False for v in r["vr"]}},
            "progress": {v: [sp.fget(r["mat"], v), sp.fget(r["nxt"], v), sp.fget(r["ack"], v)]
                         for v in r["prog"]},
            "tstart": r["tstart"], "xfer": r["xfer"], "rseq": r["rseq"],
            "pend": [list(x) for x in r["pend"]], "wait": list(r["wait"]),
        }
        got = dict(p)
        got["state"] = ROLE[p["state"]]
        for k, v in want.items():
            if got[k] != v:
                return f"{k}: impl={got[k]!r} spec={v!r}"
        out_i = {self.ikey(m) for m in ev["out"]}
        out_s = {self.skey(m) for m in cand.out}
        if out_i != out_s:
            return f"messages: impl-only={sorted(map(str, out_i - out_s))[:3]} spec-only={sorted(map(str, out_s - out_i))[:3]}"
        if Counter((c, x) for c, x in ev["reads"]) != Counter((tag, idx) for idx, tag in cand.rel):
            return f"reads: impl={ev['reads']} spec={cand.rel}"
        if cand.err != (ev.get("err") == "AssertionError"):
            return "implementation assertion mismatch"
        return None

    def check_log(self, i, r):
        sn, st, ents = self.mirror[i]
        sp = self.sp
        if sn != r["snap"] or st != sp.snap_term(r):
            raise Violation(f"{i}: snapshot point impl=({sn},{st}) spec=({r['snap']},{sp.snap_term(r)})")
        last = len(r["log"])
        if max(ents, default=sn) != last or len(ents) != last - sn:
            raise Violation(f"{i}: log length impl={max(ents, default=sn)} spec={last}")
        for k in range(sn + 1, last + 1):
            if ents[k] != r["log"][k - 1]:
                raise Violation(f"{i}: log entry {k} impl={ents[k]} spec={r['log'][k - 1]}")

    def apply_logops(self, i, ops):
        sn, st, ents = self.mirror[i]
        for op in ops:
            if op[0] == "append":
                first = op[1]
                for k in [k for k in ents if k >= first]:
                    del ents[k]
                for e in op[2]:
                    ents[e[1]] = self.ent(e)
            elif op[0] == "compact":
                sn, st = op[1], op[2]
                for k in [k for k in ents if k <= sn]:
                    del ents[k]
            elif op[0] == "restore":
                sn, st = op[1], op[2]
                ents = {}
        self.mirror[i] = (sn, st, ents)

    # ---------------------------------------------------------------- history
    def global_commit(self):
        return max(self.committed, default=0)

    def after(self, i, before, after):
        if after["commit"] > before["commit"]:
            for k in range(before["commit"] + 1, after["commit"] + 1):
                e = after["log"][k - 1]
                old = self.committed.get(k)
                if old is not None and old[0] != e:
                    raise Violation(f"State Machine Safety: index {k} committed as {old[0]} and {e}")
                if old is None or after["term"] < old[1]:
                    self.committed[k] = (e, after["term"])
        if after["state"] == "L" and not (before["state"] == "L" and before["term"] == after["term"]):
            t = after["term"]
            if self.leaders.setdefault(t, i) != i:
                raise Violation(f"Election Safety: {self.leaders[t]} and {i} both led term {t}")
            for k, (e, ct) in self.committed.items():
                if ct <= t and (k > len(after["log"]) or after["log"][k - 1] != e):
                    raise Violation(f"Leader Completeness: {i} leads term {t} without committed entry {k}")
            self.stats["elections"] += 1

    # ---------------------------------------------------------------- events
    def candidates(self, i, ev):
        sp, r, name, a = self.sp, self.r[i], ev["ev"], ev["args"]
        err = ev.get("err")
        same = Ret(r)
        if name == "tick":
            yield same
            if r["state"] != "L" and i in r["cfg"]:
                yield sp.campaign(i, r, sp.f.prevote, False)
            if r["state"] == "L":
                for sd, ab, hb in [(True, False, False), (False, True, False), (False, False, True),
                                   (False, True, True)]:
                    if sd and not sp.f.check_quorum:
                        continue
                    yield sp.leader_tick(i, r, sd, ab, hb)
        elif name == "step":
            key = self.ikey(a["m"])
            if not self.pool.get(key):
                raise Violation(f"{i} received a message nobody sent: {a['m']}")
            m = self.pool[key][0]
            yield sp.step(i, r, m, False)
            if sp.can_ignore(r, m):
                yield sp.step(i, r, m, True)
        elif name == "propose":
            if err:
                ok = (err == "NotLeader" and r["state"] != "L") or \
                     (err == "ProposalDropped" and r["state"] == "L" and r["xfer"] is not None)
                if ok:
                    yield same
                return
            if not sp.can_propose(r):
                return
            if a["kind"] == 1:
                c = a["conf"]
                e = E(r["term"], "config", 0, c["op"], c.get("id"))
            else:
                e = E(r["term"], "normal" if a["kind"] == 0 else "noop",
                      a["digest"] if a["kind"] == 0 else 0)
            yield sp.propose(i, r, e)
        elif name == "propose_conf_change":
            c = a["conf"]
            allowed = sp.can_conf_change(i, r, c.get("op"), c.get("id"))
            if err:
                if not allowed:
                    yield same
                return
            if allowed:
                yield sp.propose(i, r, E(r["term"], "config", 0, c["op"], c["id"]))
        elif name == "read_index":
            if err:
                if err == "NotLeader" and r["state"] != "L":
                    yield same
                return
            if r["state"] == "L":
                self.read_gc[(i, a["ctx"])] = self.global_commit()
                yield sp.read_index(i, r, a["ctx"])
        elif name == "transfer_leadership":
            t = a["target"]
            if err:
                if r["state"] != "L" or t == i or t not in r["prog"]:
                    yield same
                return
            if r["state"] == "L" and t != i and t in r["prog"]:
                yield sp.transfer(i, r, t)
        elif name == "compact":
            idx = a["index"]
            if err:
                if not (r["snap"] < idx <= r["commit"]):
                    yield same
                return
            if r["snap"] < idx <= r["commit"]:
                yield Ret(dict(r, snap=idx))
        else:
            raise Violation(f"unknown event {name}")

    def on_init(self, i, ev):
        a = ev["args"]
        sn = a["snapshot"]
        ents = {e[1]: self.ent(e) for e in a["entries"]}
        snap_i, snap_t = (sn["index"], sn["term"]) if sn else (0, 0)
        self.mirror[i] = (snap_i, snap_t, ents)
        if i not in self.r:
            r0 = self.sp.init_local(i)
            if a["hard_state"][0] == 0 and not ents and sn is None:
                r0 = dict(r0, term=0, log=(), commit=0, cfg=frozenset(), cidx=0)
            self.r[i] = r0
            self.check_log(i, r0)
            if self.diff(i, Ret(r0), ev):
                raise Violation(f"{i}: initial state {self.diff(i, Ret(r0), ev)}")
            self.ready_hist[i] = [r0]
            self.stats["starts"] += 1
            return
        # Restart: the node must resume from what was durable. That is the state at one of its
        # recent persist (`ready`) points -- or, when the crash hit while the last batch was being
        # written, the previous persisted state extended by a *prefix* of that batch's log
        # (torn WAL tail). The latter is outside the TLA+ Restart action; it is safe because the
        # batch's acknowledgements are only sent after the batch is durable, and it is counted
        # separately as `restart_torn_batch`.
        hs_term, hs_vote, hs_commit = a["hard_state"]
        errs = []
        hist = self.ready_hist[i][-5:] + [self.r[i]]
        last = max(ents, default=snap_i)
        for pos in range(len(hist) - 1, -1, -1):
            cand = hist[pos]
            prev = hist[pos - 1] if pos > 0 else cand
            if (cand["term"], cand["vote"]) != (hs_term, hs_vote) and (prev["term"], prev["vote"]) != (hs_term, hs_vote):
                errs.append("hard state")
                continue
            lcp = 0
            while lcp < min(len(prev["log"]), len(cand["log"])) and prev["log"][lcp] == cand["log"][lcp]:
                lcp += 1
            torn = last != len(cand["log"])
            if torn and not (lcp <= last < len(cand["log"])):
                errs.append("log shape")
                continue
            if snap_i > last or (snap_i and cand["log"][snap_i - 1].term != snap_t):
                errs.append("snapshot")
                continue
            if any(cand["log"][k - 1] != e for k, e in ents.items()):
                errs.append("log contents")
                continue
            c = ev["post"]["commit"]
            if not (snap_i <= c <= max(min(cand["commit"], last), snap_i)):
                errs.append("commit")
                continue
            base = dict(cand, snap=snap_i, log=cand["log"][:last], term=hs_term, vote=hs_vote)
            r1 = self.sp.restarted(i, base, c)
            d = self.diff(i, Ret(r1), ev)
            if d:
                errs.append(d)
                continue
            if c < cand["commit"]:
                self.stats["restart_commit_rollback"] += 1
            if torn:
                self.stats["restart_torn_batch"] += 1
            self.r[i] = r1
            self.ready_hist[i] = [r1]
            self.stats["restarts"] += 1
            return
        raise Violation(f"{i}: restart state matches no persisted state ({errs})")

    def on_event(self, ev):
        name = ev.get("ev")
        if name in (None, "meta"):
            return
        i = ev["n"]
        self.stats["events"] += 1
        if name == "init":
            self.on_init(i, ev)
            return
        if name == "ready":
            self.ready_hist[i].append(self.r[i])
            if len(self.ready_hist[i]) > 8:
                del self.ready_hist[i][:-8]
            return
        before = self.r[i]
        self.apply_logops(i, ev["logops"])
        tried = []
        for cand in self.candidates(i, ev):
            d = self.diff(i, cand, ev)
            if d is None:
                self.check_log(i, cand.r)
                for m in cand.out:
                    self.pool[self.skey(m)].append(m)
                for idx, tag in cand.rel:
                    gc = self.read_gc.get((i, tag), 0)
                    if idx < gc:
                        raise Violation(f"linearizable read: {i} released ctx {tag} at {idx} < commit {gc}")
                    self.stats["reads_released"] += 1
                self.r[i] = cand.r
                self.after(i, before, cand.r)
                self.stats["ev_" + name] += 1
                self.stats["messages_checked"] += len(cand.out)
                return
            tried.append(d)
        raise Violation(f"{i} event #{ev.get('i')} {name}: no spec successor matches "
                        f"({'; '.join(tried) or 'action not enabled in spec'})")

    def needs(self, ev):
        if ev.get("ev") == "step":
            return self.ikey(ev["args"]["m"])
        return None

    def run(self):
        if self.ordered is not None:
            for ev in self.ordered:
                self.on_event(ev)
        else:
            heads = {n: 0 for n in self.by_node}
            while True:
                ready = []
                for n, k in heads.items():
                    evs = self.by_node[n]
                    if k < len(evs):
                        key = self.needs(evs[k])
                        if key is None or self.pool.get(key):
                            ready.append((evs[k].get("ts", 0), n))
                if not ready:
                    if any(k < len(self.by_node[n]) for n, k in heads.items()):
                        stuck = {n: self.by_node[n][k] for n, k in heads.items() if k < len(self.by_node[n])}
                        raise Violation(f"received messages that no traced event sent: "
                                        f"{ {n: e.get('args', {}).get('m') for n, e in stuck.items()} }")
                    break
                _, n = min(ready)
                self.on_event(self.by_node[n][heads[n]])
                heads[n] += 1
        self.final_checks()
        return self.stats

    def final_checks(self):
        logs = {i: r["log"] for i, r in self.r.items()}
        ids = sorted(logs)
        for a in ids:
            for b in ids:
                la, lb = logs[a], logs[b]
                for k in range(min(len(la), len(lb)), 0, -1):
                    if la[k - 1].term == lb[k - 1].term:
                        if la[:k] != lb[:k]:
                            raise Violation(f"Log Matching between {a} and {b} at {k}")
                        break
        self.stats["committed_entries"] = len(self.committed)


def check_file(path) -> Counter:
    evs = load_lines(path)
    by = defaultdict(list)
    for ev in evs:
        if "n" in ev:
            by[ev["n"]].append(ev)
    return Checker(by, ordered=evs).run()


def check_cluster(directory) -> Counter:
    by = {}
    for p in sorted(glob.glob(os.path.join(directory, "*.jsonl"))):
        evs = load_lines(p)
        if evs:
            by[evs[0]["n"]] = [e for e in evs if "n" in e]
    return Checker(by).run()


def main(argv=None):
    ap = argparse.ArgumentParser(description="check raftstore traces against the RaftStore spec")
    ap.add_argument("paths", nargs="*")
    ap.add_argument("--cluster", action="append", default=[], help="directory of per-node traces")
    a = ap.parse_args(argv)
    total, bad = Counter(), 0
    for p in a.paths:
        try:
            total += check_file(p)
            print(f"OK   {p}")
        except Violation as e:
            bad += 1
            print(f"FAIL {p}: {e}")
    for d in a.cluster:
        try:
            total += check_cluster(d)
            print(f"OK   {d}")
        except Violation as e:
            bad += 1
            print(f"FAIL {d}: {e}")
    print(dict(total))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
