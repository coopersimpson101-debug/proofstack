"""Breadth-first explorer for the global system of tla/RaftStore.tla, built on raftspec.

This mirrors `Next` (and TLC's handling of `CONSTRAINT`: successor states that violate the
constraint are discarded, not counted).  It is deliberately simple; it is only used on small
models, to check that the Python transcription generates *exactly* the state graph TLC does
(same number of distinct states), and as a second, independent invariant checker.
"""
from __future__ import annotations

import argparse
import time
from collections import deque
from dataclasses import dataclass

from .raftspec import BOOT, E, Flags, Ret, Spec, freeze, thaw


@dataclass(frozen=True)
class Bounds:
    max_term: int = 2
    max_log_len: int = 3
    max_values: int = 1
    max_crashes: int = 0
    max_reads: int = 0
    max_conf_changes: int = 0
    max_transfers: int = 0
    max_compactions: int = 0
    max_msgs: int = 3
    max_seq: int = 2


class System:
    def __init__(self, servers, init_voters, flags: Flags, b: Bounds):
        self.sp = Spec(servers, init_voters, flags)
        self.b = b
        self.servers = self.sp.servers

    def init(self):
        locs = tuple(freeze(self.sp.init_local(i)) for i in self.servers)
        return (locs, frozenset(), frozenset(), frozenset({(1, BOOT, 1)}), True, True, (0, 0, 0, 0, 0, 0))

    # ------------------------------------------------------------------ helpers
    def global_commit(self, st):
        return max(c[0] for c in st[3])

    def install(self, st, i, res: Ret, net, ctr=None):
        locs, _, elected, committed, reads_ok, impl_ok, c0 = st
        k = self.sp.pos[i]
        a = thaw(locs[k])
        b = res.r
        new_locs = locs[:k] + (freeze(b),) + locs[k + 1:]
        newc = committed
        if b["commit"] > a["commit"]:
            newc = committed | {(x, b["log"][x - 1], b["term"]) for x in range(a["commit"] + 1, b["commit"] + 1)}
        el = elected
        if b["state"] == "L" and not (a["state"] == "L" and a["term"] == b["term"]):
            el = elected | {(b["term"], i)}
        ro = reads_ok and all(idx >= tag for idx, tag in res.rel)
        return (new_locs, net | res.out, el, newc, ro, impl_ok and not res.err, c0 if ctr is None else ctr)

    def constraint(self, st):
        if len(st[1]) > self.b.max_msgs:
            return False
        for t in st[0]:
            r = thaw(t)
            if r["term"] > self.b.max_term or len(r["log"]) > self.b.max_log_len or r["rseq"] > self.b.max_seq:
                return False
        return True

    # ------------------------------------------------------------------ Next
    def successors(self, st):
        sp, b = self.sp, self.b
        locs, msgs, _, _, _, _, ctr = st
        vals, crashes, reads, confs, xfers, compacts = ctr
        for i in self.servers:
            r = thaw(locs[sp.pos[i]])
            # Timeout
            if r["state"] != "L" and i in r["cfg"]:
                yield self.install(st, i, sp.campaign(i, r, sp.f.prevote, False), msgs)
            # Tick
            if r["state"] == "L":
                for sd in ((False, True) if sp.f.check_quorum else (False,)):
                    for ab in (False, True):
                        for hb in (False, True):
                            if not (sd or ab or hb) or (sd and (ab or hb)) or (ab and r["xfer"] is None):
                                continue
                            yield self.install(st, i, sp.leader_tick(i, r, sd, ab, hb), msgs)
            # ClientWrite
            if sp.can_propose(r) and vals < b.max_values and len(r["log"]) < b.max_log_len:
                yield self.install(st, i, sp.propose(i, r, E(r["term"], "normal", vals + 1)), msgs,
                                   (vals + 1, crashes, reads, confs, xfers, compacts))
            # ConfChange
            if confs < b.max_conf_changes and len(r["log"]) < b.max_log_len:
                for op in ("add", "remove"):
                    for x in self.servers:
                        if sp.can_conf_change(i, r, op, x):
                            yield self.install(st, i, sp.propose(i, r, E(r["term"], "config", 0, op, x)), msgs,
                                               (vals, crashes, reads, confs + 1, xfers, compacts))
            # ClientRead
            if r["state"] == "L" and reads < b.max_reads:
                yield self.install(st, i, sp.read_index(i, r, self.global_commit(st)), msgs,
                                   (vals, crashes, reads + 1, confs, xfers, compacts))
            # TransferLeadership
            if r["state"] == "L" and xfers < b.max_transfers:
                for t in r["prog"]:
                    yield self.install(st, i, sp.transfer(i, r, t), msgs,
                                       (vals, crashes, reads, confs, xfers + 1, compacts))
            # Compact
            if compacts < b.max_compactions:
                for idx in range(r["snap"] + 1, r["commit"] + 1):
                    yield self.install(st, i, Ret(dict(r, snap=idx)), msgs,
                                       (vals, crashes, reads, confs, xfers, compacts + 1))
            # Restart
            if crashes < b.max_crashes:
                cs = range(r["snap"], r["commit"] + 1) if sp.f.lossy_commit else (r["commit"],)
                for c in cs:
                    yield self.install(st, i, Ret(sp.restarted(i, r, c)), msgs,
                                       (vals, crashes + 1, reads, confs, xfers, compacts))
        for m in msgs:
            i = m.dst
            r = thaw(locs[sp.pos[i]])
            for keep in (False, True):
                for ign in (False, True):
                    if ign and not sp.can_ignore(r, m):
                        continue
                    yield self.install(st, i, sp.step(i, r, m, ign), msgs if keep else msgs - {m})
            yield (locs, msgs - {m}) + st[2:]

    # ------------------------------------------------------------------ invariants
    def check(self, st):
        locs, _, elected, committed, reads_ok, impl_ok, _ = st
        rs = [thaw(t) for t in locs]
        bad = []
        terms = {}
        for t, i in elected:
            if terms.setdefault(t, i) != i:
                bad.append("ElectionSafety")
        for a in rs:
            for c in rs:
                for k in range(1, min(len(a["log"]), len(c["log"])) + 1):
                    if a["log"][k - 1].term == c["log"][k - 1].term and a["log"][:k] != c["log"][:k]:
                        bad.append("LogMatching")
        byidx = {}
        for idx, ent, t in committed:
            if byidx.setdefault(idx, ent) != ent:
                bad.append("StateMachineSafety")
        for r in rs:
            for k in range(1, r["commit"] + 1):
                if k in byidx and r["log"][k - 1] != byidx[k]:
                    bad.append("StateMachineSafety")
            if r["state"] == "L":
                for idx, ent, t in committed:
                    if t <= r["term"] and (idx > len(r["log"]) or r["log"][idx - 1] != ent):
                        bad.append("LeaderCompleteness")
            if r["cfg"] != self.sp.config(r["log"]):
                bad.append("ConfigMatchesLog")
        if not reads_ok:
            bad.append("LinearizableReads")
        if not impl_ok:
            bad.append("NoImplAssertion")
        return sorted(set(bad))


def bfs(system: System, limit: int | None = None):
    t0 = time.time()
    init = system.init()
    seen = {init}
    q = deque([(init, 0)])
    generated = 1
    depth = 0
    violations = []
    v = system.check(init)
    if v:
        violations.append((v, init))
    xfer_leaders = 0   # explored (state, leader with a transfer target) pairs; see docs/raft-spec.md
    while q:
        st, d = q.popleft()
        depth = max(depth, d)
        xfer_leaders += sum(1 for t in st[0] if thaw(t)["state"] == "L" and thaw(t)["xfer"] is not None)
        for nx in system.successors(st):
            generated += 1
            if not system.constraint(nx) or nx in seen:
                continue
            seen.add(nx)
            v = system.check(nx)
            if v:
                violations.append((v, nx))
            q.append((nx, d + 1))
            if limit and len(seen) >= limit:
                return dict(distinct=len(seen), generated=generated, depth=depth, complete=False,
                            violations=violations, seconds=time.time() - t0, xfer_leaders=xfer_leaders)
    return dict(distinct=len(seen), generated=generated, depth=depth + 1, complete=True,
                violations=violations, seconds=time.time() - t0, xfer_leaders=xfer_leaders)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--servers", type=int, default=3)
    ap.add_argument("--max-term", type=int, default=2)
    ap.add_argument("--max-log", type=int, default=3)
    ap.add_argument("--max-values", type=int, default=1)
    ap.add_argument("--max-msgs", type=int, default=2)
    ap.add_argument("--max-crashes", type=int, default=0)
    ap.add_argument("--max-seq", type=int, default=2)
    ap.add_argument("--no-prevote", action="store_true")
    ap.add_argument("--limit", type=int, default=None)
    a = ap.parse_args(argv)
    servers = [f"n{k + 1}" for k in range(a.servers)]
    sysm = System(servers, servers, Flags(prevote=not a.no_prevote),
                  Bounds(max_term=a.max_term, max_log_len=a.max_log, max_values=a.max_values,
                         max_msgs=a.max_msgs, max_crashes=a.max_crashes, max_seq=a.max_seq))
    res = bfs(sysm, a.limit)
    print({k: v for k, v in res.items() if k != "violations"}, "violations:", len(res["violations"]), flush=True)


if __name__ == "__main__":
    main()
