"""Line-by-line Python transcription of tla/RaftStore.tla.

Every function here corresponds to the TLA+ operator of the same name (CamelCase there,
snake_case here) and returns the same `Ret` record.  It exists for two reasons:

* the trace checker (`proofstack.tracecheck`) replays real raftstore executions through these
  per-node actions and demands that the implementation's logged post-state and sent messages
  are one of the successors the spec allows;
* `proofstack.explore` enumerates the full state graph of small models with it, and the test
  suite compares the distinct-state count with TLC's for the same model, which ties this
  transcription to the TLA+ text.

Values: TLA+ `Nil` is Python ``None``; `-1` stands for ``term_at() is None``; sets are
frozensets; sequences are tuples; functions over `Server` are tuples indexed like
``Spec.servers``.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import NamedTuple


class E(NamedTuple):
    """A log entry: [term, kind, val, op, id]."""
    term: int
    kind: str          # "normal" | "noop" | "config"
    val: object = 0    # client value (normal entries)
    op: str = ""       # "boot" | "add" | "remove" (config entries)
    id: object = None


BOOT = E(1, "config", 0, "boot", None)


class Snap(NamedTuple):
    index: int
    term: int
    data: tuple        # the log prefix 1..index (stands for the state-machine image)


NOSNAP = Snap(0, 0, ())


class M(NamedTuple):
    type: str
    src: object
    dst: object
    term: int
    index: int = 0
    logTerm: int = 0
    entries: tuple = ()
    commit: int = 0
    reject: bool = False
    hintIndex: int = 0
    hintTerm: int = 0
    ctx: int = 0
    snap: Snap = NOSNAP
    transfer: bool = False


class Ret(NamedTuple):
    r: dict
    out: frozenset = frozenset()
    rel: tuple = ()      # released reads: ((idx, tag), ...)
    err: bool = False
    ok: bool = False     # only meaningful for MaybeCommit


def then(a: Ret, b: Ret) -> Ret:
    return Ret(b.r, a.out | b.out, a.rel + b.rel, a.err or b.err)


def upd(r: dict, **kw) -> dict:
    n = dict(r)
    n.update(kw)
    return n


@dataclass(frozen=True)
class Flags:
    prevote: bool = True
    check_quorum: bool = True
    lossy_commit: bool = False
    unsafe_commit_any_term: bool = False
    skip_term_start_check: bool = False
    no_noop: bool = False          # mutation: no no-op entry on election
    vote_any_log: bool = False     # mutation: no up-to-date check when voting


class Spec:
    def __init__(self, servers, init_voters, flags: Flags | None = None):
        self.servers = tuple(servers)
        self.pos = {x: k for k, x in enumerate(self.servers)}
        self.init_voters = frozenset(init_voters)
        self.f = flags or Flags()
        self.zero = (0,) * len(self.servers)

    # ------------------------------------------------------------------ functions over Server
    def fget(self, f: tuple, j) -> int:
        return f[self.pos[j]]

    def fset(self, f: tuple, j, v: int) -> tuple:
        k = self.pos[j]
        return f[:k] + (v,) + f[k + 1:]

    # ------------------------------------------------------------------ configuration
    def config(self, lg: tuple) -> frozenset:
        c = frozenset()
        for e in lg:
            if e.kind != "config":
                continue
            if e.op == "boot":
                c = self.init_voters
            elif e.op == "add":
                c = c | {e.id}
            else:
                c = c - {e.id}
        return c

    # ------------------------------------------------------------------ RaftLog
    @staticmethod
    def last_index(r):
        return len(r["log"])

    @staticmethod
    def snap_term(r):
        return 0 if r["snap"] == 0 else r["log"][r["snap"] - 1].term

    def last_term(self, r):
        return self.snap_term(r) if len(r["log"]) == r["snap"] else r["log"][-1].term

    def term_at(self, r, k):
        if k == r["snap"]:
            return self.snap_term(r)
        if k < r["snap"] or k > len(r["log"]):
            return -1
        return r["log"][k - 1].term

    def up_to_date(self, r, idx, t):
        lt = self.last_term(r)
        return t > lt or (t == lt and idx >= self.last_index(r))

    @staticmethod
    def first_index_of_term(r, t, upto):
        sn = r["snap"]
        hi = sn + max(0, upto - sn)
        return sn + 1 + sum(1 for k in range(sn + 1, hi + 1) if r["log"][k - 1].term < t)

    def last_index_of_term(self, r, t, upto):
        sn = r["snap"]
        hi = max(0, min(upto, self.last_index(r)) - sn)
        pos = sum(1 for k in range(sn + 1, sn + hi + 1) if r["log"][k - 1].term <= t)
        if pos > 0 and r["log"][sn + pos - 1].term == t:
            return sn + pos
        if pos == 0 and self.snap_term(r) == t:
            return sn
        return -1

    def snap_of(self, r) -> Snap:
        return Snap(r["snap"], self.snap_term(r), r["log"][: r["snap"]])

    # ------------------------------------------------------------------ helpers
    @staticmethod
    def quorum(r):
        return len(r["cfg"]) // 2 + 1

    def recompute(self, i, r):
        lg = r["log"]
        cks = [k for k in range(r["snap"] + 1, len(lg) + 1) if lg[k - 1].kind == "config"]
        cfg = self.config(lg)
        cidx = r["snap"] if not cks else max(cks)
        r1 = upd(r, cfg=cfg, cidx=cidx)
        if r["state"] != "L":
            return r1
        newp = (cfg - {i}) - r["prog"]
        keep = r["prog"] & cfg
        nxt = tuple(len(lg) + 1 if j in newp else (self.fget(r["nxt"], j) if j in keep else 0)
                    for j in self.servers)
        mat = tuple(self.fget(r["mat"], j) if j in keep else 0 for j in self.servers)
        ack = tuple(self.fget(r["ack"], j) if j in keep else 0 for j in self.servers)
        return upd(r1, prog=keep | newp, nxt=nxt, mat=mat, ack=ack)

    def reset(self, r):
        return upd(r, vg=frozenset(), vr=frozenset(), xfer=None, prog=frozenset(), nxt=self.zero,
                   mat=self.zero, ack=self.zero, pend=(), wait=())

    def become_follower(self, r, t, ld):
        r1 = upd(r, term=t, vote=None) if t > r["term"] else r
        return self.reset(upd(r1, state="F", leader=ld))

    def send_append(self, i, r, to, ae) -> Ret:
        last = self.last_index(r)
        nx = last + 1 if self.fget(r["nxt"], to) > last + 1 else self.fget(r["nxt"], to)
        prev = nx - 1
        pt = self.term_at(r, prev)
        if pt == -1:
            return Ret(upd(r, nxt=self.fset(r["nxt"], to, r["snap"] + 1)),
                       frozenset({M("snapshot", i, to, r["term"], snap=self.snap_of(r))}))
        ents = r["log"][nx - 1: last]
        if not ents and not ae:
            return Ret(upd(r, nxt=self.fset(r["nxt"], to, nx)))
        return Ret(upd(r, nxt=self.fset(r["nxt"], to, last + 1 if ents else nx)),
                   frozenset({M("append", i, to, r["term"], index=prev, logTerm=pt, entries=ents,
                                commit=r["commit"], ctx=r["rseq"])}))

    def bcast(self, i, r, ae) -> Ret:
        res = {p: self.send_append(i, r, p, ae) for p in r["prog"]}
        nxt = tuple(self.fget(res[q].r["nxt"], q) if q in r["prog"] else self.fget(r["nxt"], q)
                    for q in self.servers)
        out = frozenset().union(*[x.out for x in res.values()]) if res else frozenset()
        return Ret(upd(r, nxt=nxt), out)

    def register_read(self, i, r, tag) -> Ret:
        if r["cfg"] == frozenset({i}):
            return Ret(r, frozenset(), ((r["commit"], tag),))
        r1 = upd(r, rseq=r["rseq"] + 1, pend=r["pend"] + ((r["rseq"] + 1, r["commit"], tag),))
        return self.bcast(i, r1, True)

    def register_all(self, i, r, ws) -> Ret:
        acc = Ret(r)
        for w in ws:
            a = self.register_read(i, acc.r, w)
            acc = then(acc, a)
        return acc

    def maybe_commit(self, i, r) -> Ret:
        elig = [v for v in r["cfg"] if v == i or v in r["prog"]]
        q = self.quorum(r)
        no = Ret(r, ok=False)
        if not r["cfg"] or len(elig) < q:
            return no

        def mo(v):
            return self.last_index(r) if v == i else self.fget(r["mat"], v)
        top = max(mo(v) for v in elig)
        n = max(k for k in range(0, top + 1) if sum(1 for v in elig if mo(v) >= k) >= q)
        if n <= r["commit"]:
            return no
        if self.term_at(r, n) != r["term"] and not self.f.unsafe_commit_any_term:
            return no
        r1 = upd(r, commit=n)
        if r1["wait"] and n >= r1["tstart"]:
            a = self.register_all(i, upd(r1, wait=()), r1["wait"])
        else:
            a = Ret(r1)
        if i not in a.r["cfg"] and a.r["commit"] >= a.r["cidx"]:
            return Ret(self.become_follower(a.r, a.r["term"], None), a.out, a.rel, False, False)
        return Ret(a.r, a.out, a.rel, False, True)

    def become_leader(self, i, r) -> Ret:
        r1 = self.reset(upd(r, state="L", leader=i))
        last = self.last_index(r1)
        peers = r1["cfg"] - {i}
        r2 = upd(r1, prog=peers,
                 nxt=tuple(last + 1 if j in peers else 0 for j in self.servers),
                 log=r1["log"] if self.f.no_noop else r1["log"] + (E(r1["term"], "noop"),), tstart=last + 1)
        mc = self.maybe_commit(i, r2)
        return then(mc, self.bcast(i, mc.r, True))

    @staticmethod
    def poll(r, src, granted):
        if src in r["vg"] or src in r["vr"]:
            return r
        if granted:
            return upd(r, vg=r["vg"] | {src})
        return upd(r, vr=r["vr"] | {src})

    def poll_result(self, r):
        g = len(r["vg"] & r["cfg"])
        j = len(r["vr"] & r["cfg"])
        q = self.quorum(r)
        if g >= q:
            return "won"
        if j > len(r["cfg"]) - q:
            return "lost"
        return "pending"

    def campaign(self, i, r, pre, transfer) -> Ret:
        if pre:
            r1 = self.reset(upd(r, state="PC", leader=None))
            vt, mt = r1["term"] + 1, "prevote"
        else:
            r1 = self.reset(upd(r, term=r["term"] + 1, vote=i, state="C", leader=None))
            vt, mt = r1["term"], "vote"
        r2 = self.poll(r1, i, True)
        if self.poll_result(r2) == "won":
            return self.campaign(i, r2, False, transfer) if pre else self.become_leader(i, r2)
        return Ret(r2, frozenset(M(mt, i, v, vt, index=self.last_index(r2), logTerm=self.last_term(r2),
                                   transfer=transfer) for v in r2["cfg"] - {i}))

    # ------------------------------------------------------------------ handlers
    def handle_vote(self, i, r, m) -> Ret:
        can = (r["vote"] == m.src or (r["vote"] is None and r["leader"] is None)
               or (m.type == "prevote" and m.term > r["term"]))
        rt = "vote_resp" if m.type == "vote" else "prevote_resp"
        if can and (self.f.vote_any_log or self.up_to_date(r, m.index, m.logTerm)):
            return Ret(upd(r, vote=m.src) if m.type == "vote" else r, frozenset({M(rt, i, m.src, m.term)}))
        return Ret(r, frozenset({M(rt, i, m.src, r["term"], reject=True)}))

    def handle_append(self, i, r, m) -> Ret:
        skip = r["commit"] - m.index
        adj = m.index < r["commit"]
        prev = r["commit"] if adj else m.index
        pterm = self.term_at(r, r["commit"]) if adj else m.logTerm
        if not adj:
            ents = m.entries
        else:
            ents = m.entries[skip:] if skip < len(m.entries) else ()
        t = self.term_at(r, prev)
        if t != pterm:
            hi = self.last_index(r) + 1 if t == -1 else self.first_index_of_term(r, t, prev)
            ht = 0 if t == -1 else t
            return Ret(r, frozenset({M("append_resp", i, m.src, r["term"], reject=True, index=m.index,
                                       hintIndex=hi, hintTerm=ht, ctx=m.ctx)}))
        last_new = prev + len(ents)
        p0 = 0
        for p in range(1, len(ents) + 1):
            if self.term_at(r, prev + p) != ents[p - 1].term:
                p0 = p
                break
        first = prev + p0
        rest = ents[p0 - 1:] if p0 else ()
        bad = p0 != 0 and first <= r["commit"]
        truncating = p0 != 0 and self.term_at(r, first) != -1
        r1 = r if (p0 == 0 or bad) else upd(r, log=r["log"][: first - 1] + rest)
        need = p0 != 0 and not bad and (any(e.kind == "config" for e in rest)
                                         or (truncating and first <= r["cidx"]))
        r2 = self.recompute(i, r1) if need else r1
        nc = min(m.commit, last_new)
        r3 = upd(r2, commit=nc) if nc > r2["commit"] else r2
        return Ret(r3, frozenset({M("append_resp", i, m.src, r["term"], index=last_new, ctx=m.ctx)}),
                   (), bad)

    def handle_snapshot(self, i, r, m) -> Ret:
        sn = m.snap
        if sn.index <= r["commit"]:
            return Ret(r, frozenset({M("append_resp", i, m.src, r["term"], index=r["commit"])}))
        if self.term_at(r, sn.index) == sn.term:
            return Ret(upd(r, commit=sn.index),
                       frozenset({M("append_resp", i, m.src, r["term"], index=sn.index)}))
        return Ret(self.recompute(i, upd(r, log=sn.data, snap=sn.index, commit=sn.index)),
                   frozenset({M("append_resp", i, m.src, r["term"], index=sn.index)}))

    def release_reads(self, i, r) -> Ret:
        if not r["pend"]:
            return Ret(r)
        elig = [v for v in r["cfg"] if v == i or v in r["prog"]]

        def val(v):
            return r["rseq"] if v == i else self.fget(r["ack"], v)
        q = self.quorum(r)
        ok = [a for a in {val(v) for v in elig} if sum(1 for v in elig if val(v) >= a) >= q]
        acked = max(ok) if ok else -1
        done = tuple((x[1], x[2]) for x in r["pend"] if x[0] <= acked)
        keep = tuple(x for x in r["pend"] if x[0] > acked)
        return Ret(upd(r, pend=keep), frozenset(), done)

    def handle_append_resp(self, i, r, m) -> Ret:
        if m.src not in r["prog"]:
            return Ret(r)
        src = m.src
        r0 = upd(r, ack=self.fset(r["ack"], src, m.ctx)) if m.ctx > self.fget(r["ack"], src) else r
        last = self.last_index(r0)
        mat0 = self.fget(r0["mat"], src)
        if m.reject:
            if m.index > mat0:
                idx = self.last_index_of_term(r0, m.hintTerm, m.index)
                if m.hintTerm != 0:
                    new = idx + 1 if idx != -1 else m.hintIndex
                else:
                    new = m.hintIndex
                nx = max(mat0 + 1, min(new, min(m.index, last + 1)))
                a = self.send_append(i, upd(r0, nxt=self.fset(r0["nxt"], src, nx)), src, True)
                return then(a, self.release_reads(i, a.r))
            return self.release_reads(i, r0)
        nxt0 = self.fget(r0["nxt"], src)
        r1 = upd(r0, mat=self.fset(r0["mat"], src, m.index),
                 nxt=self.fset(r0["nxt"], src, m.index + 1 if nxt0 <= m.index else nxt0))
        if m.index <= mat0:
            a = Ret(r0)
        else:
            mc = self.maybe_commit(i, r1)
            if mc.ok:
                a = then(mc, self.bcast(i, mc.r, True))
            elif mc.r["state"] != "L":
                return Ret(mc.r, mc.out, mc.rel)
            elif self.fget(mc.r["nxt"], src) <= last:
                a = then(mc, self.send_append(i, mc.r, src, False))
            else:
                a = mc
        tn = frozenset()
        if src == a.r["xfer"] and self.fget(a.r["mat"], src) == last:
            tn = frozenset({M("timeout_now", i, src, a.r["term"])})
        b = self.release_reads(i, a.r)
        return Ret(b.r, a.out | tn, a.rel + b.rel)

    def step_follower(self, i, r, m) -> Ret:
        if m.type == "append":
            return self.handle_append(i, upd(r, leader=m.src), m)
        if m.type == "snapshot":
            return self.handle_snapshot(i, upd(r, leader=m.src), m)
        if m.type == "timeout_now":
            return self.campaign(i, r, False, True) if i in r["cfg"] else Ret(r)
        return Ret(r)

    def can_ignore(self, r, m) -> bool:
        return (m.term > r["term"] and m.type in ("vote", "prevote") and self.f.check_quorum
                and r["leader"] is not None and not m.transfer)

    def step(self, i, r0, m, ignore) -> Ret:
        if ignore and self.can_ignore(r0, m):
            return Ret(r0)
        if m.term < r0["term"]:
            if m.type in ("append", "snapshot"):
                return Ret(r0, frozenset({M("append_resp", i, m.src, r0["term"], reject=True)}))
            if m.type == "prevote":
                return Ret(r0, frozenset({M("prevote_resp", i, m.src, r0["term"], reject=True)}))
            return Ret(r0)
        if m.term > r0["term"] and not (m.type == "prevote" or (m.type == "prevote_resp" and not m.reject)):
            r = self.become_follower(r0, m.term, m.src if m.type in ("append", "snapshot") else None)
        else:
            r = r0
        t = m.type
        if t in ("vote", "prevote"):
            return self.handle_vote(i, r, m)
        if r["state"] == "L":
            return self.handle_append_resp(i, r, m) if t == "append_resp" else Ret(r)
        if r["state"] in ("C", "PC"):
            if t in ("append", "snapshot"):
                return self.step_follower(i, self.become_follower(r, m.term, m.src), m)
            if (t == "prevote_resp" and r["state"] == "PC") or (t == "vote_resp" and r["state"] == "C"):
                r2 = self.poll(r, m.src, not m.reject)
                res = self.poll_result(r2)
                if res == "won":
                    return self.campaign(i, r2, False, False) if r2["state"] == "PC" else self.become_leader(i, r2)
                if res == "lost":
                    return Ret(self.become_follower(r2, r2["term"], None))
                return Ret(r2)
            return Ret(r)
        return self.step_follower(i, r, m)

    def leader_tick(self, i, r, stepdown, abort, hb) -> Ret:
        if stepdown:
            return Ret(self.become_follower(r, r["term"], None))
        r1 = upd(r, xfer=None) if abort else r
        if hb:
            return self.bcast(i, upd(r1, rseq=r1["rseq"] + 1), True)
        return Ret(r1)

    def propose(self, i, r, e: E) -> Ret:
        r1 = upd(r, log=r["log"] + (e,))
        r2 = self.recompute(i, r1) if e.kind == "config" else r1
        mc = self.maybe_commit(i, r2)
        return then(mc, self.bcast(i, mc.r, False))

    @staticmethod
    def can_propose(r):
        return r["state"] == "L" and r["xfer"] is None

    def can_conf_change(self, i, r, op, x):
        if not self.can_propose(r):
            return False
        if not (self.f.skip_term_start_check or r["commit"] >= r["tstart"]):
            return False
        if r["cidx"] > r["commit"]:
            return False
        if op == "add":
            return x not in r["cfg"]
        return x in r["cfg"] and len(r["cfg"]) > 1

    def read_index(self, i, r, tag) -> Ret:
        if r["commit"] < r["tstart"]:
            return Ret(upd(r, wait=r["wait"] + (tag,)))
        return self.register_read(i, r, tag)

    def transfer(self, i, r, t) -> Ret:
        r1 = upd(r, xfer=t)
        if self.fget(r1["mat"], t) == self.last_index(r1):
            return Ret(r1, frozenset({M("timeout_now", i, t, r1["term"])}))
        return self.send_append(i, r1, t, True)

    def restarted(self, i, r, c):
        base = upd(r, state="F", leader=None, commit=c, tstart=0, rseq=0)
        return self.recompute(i, self.reset(base))

    def init_local(self, i):
        boot = i in self.init_voters
        return dict(term=1 if boot else 0, vote=None, state="F", leader=None,
                    log=(BOOT,) if boot else (), snap=0, commit=1 if boot else 0,
                    cfg=self.init_voters if boot else frozenset(), cidx=1 if boot else 0,
                    vg=frozenset(), vr=frozenset(), prog=frozenset(), nxt=self.zero, mat=self.zero,
                    ack=self.zero, tstart=0, xfer=None, rseq=0, pend=(), wait=())


LOCAL_KEYS = ("term", "vote", "state", "leader", "log", "snap", "commit", "cfg", "cidx", "vg", "vr",
              "prog", "nxt", "mat", "ack", "tstart", "xfer", "rseq", "pend", "wait")


def freeze(r: dict) -> tuple:
    return tuple(r[k] for k in LOCAL_KEYS)


def thaw(t: tuple) -> dict:
    return dict(zip(LOCAL_KEYS, t))
