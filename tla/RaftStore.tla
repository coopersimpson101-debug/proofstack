----------------------------- MODULE RaftStore -----------------------------
(***************************************************************************)
(* Raft *as implemented* in raftstore/raft/core.py -- not textbook Raft.    *)
(*                                                                         *)
(* Every per-node operator below is a transcription of one method of the   *)
(* `Raft` class, with the same control flow and the same arithmetic       *)
(* (fast-backtracking hints are computed with the same bisect semantics). *)
(* An operator takes the node's local state record `r` and returns         *)
(*   [r |-> new local state, out |-> messages sent,                        *)
(*    rel |-> ReadIndex results released, err |-> impl assertion fired]    *)
(* so a handler is a pure function, exactly like core.Raft.step().         *)
(*                                                                         *)
(* Modelled: PreVote, CheckQuorum + leader stickiness (as nondeterminism),*)
(* AppendEntries with optimistic pipelining and fast backtracking         *)
(* (hint_index / hint_term), the "commit only current-term entries" rule, *)
(* log compaction + InstallSnapshot, single-server membership changes     *)
(* (config takes effect on append; one change at a time; leader must have *)
(* committed in its term), leadership transfer (TimeoutNow), ReadIndex    *)
(* with heartbeat-ctx quorum acks, crash/restart with persisted state,    *)
(* and a network that drops, duplicates and reorders.                     *)
(*                                                                         *)
(* Abstracted: clocks. Election timeouts, heartbeat timers and the        *)
(* CheckQuorum "recently active" bookkeeping are replaced by              *)
(* nondeterministic choices that include every timing the code allows.    *)
(* Lease reads (read_only="lease") are not modelled; ReadIndex ("safe")   *)
(* is. Message size caps are larger than any bounded log here.            *)
(*                                                                         *)
(* Snapshot trick: a node keeps its full log; entries <= snap are         *)
(* "compacted" and no operator reads their terms (TermAt returns -1, like *)
(* term_at() returning None). The retained prefix plays the role of the   *)
(* snapshot's state-machine data, which makes State Machine Safety across *)
(* snapshots directly checkable.                                           *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS Server,          \* all node ids that may ever exist
          InitVoters,      \* bootstrap configuration (subset of Server)
          Nil,
          MaxTerm, MaxLogLen, MaxValues, MaxCrashes, MaxReads,
          MaxConfChanges, MaxTransfers, MaxCompactions, MaxMsgs,
          MaxSeq,          \* bound on read_seq (every heartbeat increments it)
          PreVote,         \* raftstore default TRUE
          CheckQuorum,     \* raftstore default TRUE (enables leader stickiness)
          LossyCommit,     \* commit index is persisted without fsync: may roll back on restart
          UnsafeCommitAnyTerm, \* mutation switch (core.py: unsafe_commit_any_term)
          SkipTermStartCheck,  \* mutation switch: drop the "committed in my term" guard on conf changes
          MutNoNoop,           \* mutation switch: a new leader does not append its no-op entry
          MutVoteAnyLog        \* mutation switch: grant votes without the up-to-date log check

VARIABLES s,          \* s[i]: local state of node i (fields mirror core.Raft attributes)
          msgs,       \* the network: a set of messages (receive may keep a copy => duplication)
          elected,    \* history: set of <<term, node>> that ever became leader
          committed,  \* history: set of [idx, ent, t] ever committed by a node at term t
          readsOK,    \* history: every released ReadIndex was >= the commit point at call time
          implOK,     \* history: no AssertionError inside RaftLog.append was ever triggered
          ctr         \* bounded counters for the model

vars == <<s, msgs, elected, committed, readsOK, implOK, ctr>>

-----------------------------------------------------------------------------
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min2(a, b) == IF a < b THEN a ELSE b
Max2(a, b) == IF a > b THEN a ELSE b
Range(f) == {f[x] : x \in DOMAIN f}

Ent(t, k, v, o, x) == [term |-> t, kind |-> k, val |-> v, op |-> o, id |-> x]
BootEnt == Ent(1, "config", 0, "boot", Nil)
NoSnap == [index |-> 0, term |-> 0, data |-> <<>>]

RECURSIVE CfgUpTo(_, _)
CfgUpTo(lg, n) ==
  IF n = 0 THEN {} ELSE
  LET c == CfgUpTo(lg, n - 1) IN
  IF lg[n].kind # "config" THEN c
  ELSE IF lg[n].op = "boot" THEN InitVoters
  ELSE IF lg[n].op = "add" THEN c \cup {lg[n].id}
  ELSE c \ {lg[n].id}
Config(lg) == CfgUpTo(lg, Len(lg))

Zero == [j \in Server |-> 0]

Msg(t, src, dst, term) ==
  [type |-> t, src |-> src, dst |-> dst, term |-> term, index |-> 0, logTerm |-> 0,
   entries |-> <<>>, commit |-> 0, reject |-> FALSE, hintIndex |-> 0, hintTerm |-> 0,
   ctx |-> 0, snap |-> NoSnap, transfer |-> FALSE]

Ret(r, out) == [r |-> r, out |-> out, rel |-> <<>>, err |-> FALSE]
\* sequential composition: run F's result `a`, then feed a.r to the continuation result `b`
Then(a, b) == [r |-> b.r, out |-> a.out \cup b.out, rel |-> a.rel \o b.rel, err |-> a.err \/ b.err]

\* ======== RaftLog ========
LastIndex(r) == Len(r.log)
SnapTerm(r) == IF r.snap = 0 THEN 0 ELSE r.log[r.snap].term
LastTerm(r) == IF Len(r.log) = r.snap THEN SnapTerm(r) ELSE r.log[Len(r.log)].term
\* term_at(): -1 stands for None
TermAt(r, k) == IF k = r.snap THEN SnapTerm(r)
                ELSE IF k < r.snap \/ k > Len(r.log) THEN -1
                ELSE r.log[k].term
UpToDate(r, idx, t) == t > LastTerm(r) \/ (t = LastTerm(r) /\ idx >= LastIndex(r))
\* first_index_of_term(): snap + 1 + bisect_left(entries[:max(0, upto - snap)], term)
FirstIndexOfTerm(r, t, upto) ==
  r.snap + 1 + Cardinality({k \in (r.snap + 1)..(r.snap + Max2(0, upto - r.snap)) : r.log[k].term < t})
\* last_index_of_term(): bisect_right over entries[:max(0, min(upto, last) - snap)]
LastIndexOfTerm(r, t, upto) ==
  LET hi == Max2(0, Min2(upto, LastIndex(r)) - r.snap)
      pos == Cardinality({k \in (r.snap + 1)..(r.snap + hi) : r.log[k].term <= t})
  IN IF pos > 0 /\ r.log[r.snap + pos].term = t THEN r.snap + pos
     ELSE IF pos = 0 /\ SnapTerm(r) = t THEN r.snap
     ELSE -1
SnapOf(r) == [index |-> r.snap, term |-> SnapTerm(r), data |-> SubSeq(r.log, 1, r.snap)]

\* ======== Raft helpers ========
Quorum(r) == Cardinality(r.cfg) \div 2 + 1

\* _recompute_config()
Recompute(i, r) ==
  LET lg == r.log
      cks == {k \in (r.snap + 1)..Len(lg) : lg[k].kind = "config"}
      cfg == Config(lg)
      cidx == IF cks = {} THEN r.snap ELSE Max(cks)
      r1 == [r EXCEPT !.cfg = cfg, !.cidx = cidx]
  IN IF r.state # "L" THEN r1
     ELSE LET newp == (cfg \ {i}) \ r.prog
              keep == r.prog \cap cfg
          IN [r1 EXCEPT !.prog = keep \cup newp,
                        !.nxt = [j \in Server |-> IF j \in newp THEN Len(lg) + 1
                                                ELSE IF j \in keep THEN r.nxt[j] ELSE 0],
                        !.mat = [j \in Server |-> IF j \in keep THEN r.mat[j] ELSE 0],
                        !.ack = [j \in Server |-> IF j \in keep THEN r.ack[j] ELSE 0]]

\* _reset() (timers are not modelled; failed reads simply disappear)
Reset(r) == [r EXCEPT !.vg = {}, !.vr = {}, !.xfer = Nil, !.prog = {}, !.nxt = Zero,
                      !.mat = Zero, !.ack = Zero, !.pend = <<>>, !.wait = <<>>]

BecomeFollower(r, t, ld) ==
  LET r1 == IF t > r.term THEN [r EXCEPT !.term = t, !.vote = Nil] ELSE r
  IN Reset([r1 EXCEPT !.state = "F", !.leader = ld])

\* _send_append(to, allow_empty)
SendAppend(i, r, to, ae) ==
  LET last == LastIndex(r)
      nx == IF r.nxt[to] > last + 1 THEN last + 1 ELSE r.nxt[to]
      prev == nx - 1
      pt == TermAt(r, prev)
  IN IF pt = -1 THEN
       Ret([r EXCEPT !.nxt[to] = r.snap + 1],
           {[Msg("snapshot", i, to, r.term) EXCEPT !.snap = SnapOf(r)]})
     ELSE
       LET ents == SubSeq(r.log, nx, last) IN
       IF ents = <<>> /\ ~ae THEN Ret([r EXCEPT !.nxt[to] = nx], {})
       ELSE Ret([r EXCEPT !.nxt[to] = IF ents # <<>> THEN last + 1 ELSE nx],
                {[Msg("append", i, to, r.term) EXCEPT !.index = prev, !.logTerm = pt,
                   !.entries = ents, !.commit = r.commit, !.ctx = r.rseq]})

\* _bcast_append(): every peer's send only touches nxt[peer], so they commute
Bcast(i, r, ae) ==
  LET res == [p \in r.prog |-> SendAppend(i, r, p, ae)]
  IN [r |-> [r EXCEPT !.nxt = [q \in Server |-> IF q \in r.prog THEN res[q].r.nxt[q] ELSE r.nxt[q]]],
      out |-> UNION {res[p].out : p \in r.prog}, rel |-> <<>>, err |-> FALSE]

\* _register_read(ctx)
RegisterRead(i, r, tag) ==
  IF r.cfg = {i} THEN [r |-> r, out |-> {}, rel |-> <<[idx |-> r.commit, tag |-> tag]>>, err |-> FALSE]
  ELSE LET r1 == [r EXCEPT !.rseq = r.rseq + 1,
                           !.pend = Append(r.pend, [seq |-> r.rseq + 1, idx |-> r.commit, tag |-> tag])]
       IN Bcast(i, r1, TRUE)

RECURSIVE RegisterAll(_, _, _)
RegisterAll(i, r, ws) ==
  IF ws = <<>> THEN Ret(r, {})
  ELSE LET a == RegisterRead(i, r, Head(ws)) IN Then(a, RegisterAll(i, a.r, Tail(ws)))

\* _maybe_commit(): result record has an extra field `ok`
MaybeCommit(i, r) ==
  LET elig == {v \in r.cfg : v = i \/ v \in r.prog}
      mo(v) == IF v = i THEN LastIndex(r) ELSE r.mat[v]
      q == Quorum(r)
      no == [r |-> r, out |-> {}, rel |-> <<>>, err |-> FALSE, ok |-> FALSE]
  IN IF r.cfg = {} \/ Cardinality(elig) < q THEN no
     ELSE
     LET n == Max({k \in 0..Max({mo(v) : v \in elig}) : Cardinality({v \in elig : mo(v) >= k}) >= q})
     IN IF n <= r.commit THEN no
        ELSE IF TermAt(r, n) # r.term /\ ~UnsafeCommitAnyTerm THEN no
        ELSE
        LET r1 == [r EXCEPT !.commit = n]
            a == IF r1.wait # <<>> /\ n >= r1.tstart
                 THEN RegisterAll(i, [r1 EXCEPT !.wait = <<>>], r1.wait) ELSE Ret(r1, {})
        IN IF i \notin a.r.cfg /\ a.r.commit >= a.r.cidx
           THEN [r |-> BecomeFollower(a.r, a.r.term, Nil), out |-> a.out, rel |-> a.rel,
                 err |-> FALSE, ok |-> FALSE]
           ELSE [r |-> a.r, out |-> a.out, rel |-> a.rel, err |-> FALSE, ok |-> TRUE]

\* _become_leader()
BecomeLeader(i, r) ==
  LET r1 == Reset([r EXCEPT !.state = "L", !.leader = i])
      last == LastIndex(r1)
      peers == r1.cfg \ {i}
      r2 == [r1 EXCEPT !.prog = peers,
                       !.nxt = [j \in Server |-> IF j \in peers THEN last + 1 ELSE 0],
                       !.log = IF MutNoNoop THEN r1.log ELSE Append(r1.log, Ent(r1.term, "noop", 0, "", Nil)),
                       !.tstart = last + 1]
      mc == MaybeCommit(i, r2)
  IN Then(mc, Bcast(i, mc.r, TRUE))

Poll(r, src, granted) ==
  IF src \in r.vg \cup r.vr THEN r
  ELSE IF granted THEN [r EXCEPT !.vg = r.vg \cup {src}] ELSE [r EXCEPT !.vr = r.vr \cup {src}]
PollResult(r) ==
  LET g == Cardinality(r.vg \cap r.cfg)
      j == Cardinality(r.vr \cap r.cfg)
  IN IF g >= Quorum(r) THEN "won" ELSE IF j > Cardinality(r.cfg) - Quorum(r) THEN "lost" ELSE "pending"

\* _campaign(pre, transfer)
RECURSIVE Campaign(_, _, _, _)
Campaign(i, r, pre, transfer) ==
  LET r1 == IF pre THEN Reset([r EXCEPT !.state = "PC", !.leader = Nil])
            ELSE Reset([r EXCEPT !.term = r.term + 1, !.vote = i, !.state = "C", !.leader = Nil])
      vt == IF pre THEN r1.term + 1 ELSE r1.term
      mt == IF pre THEN "prevote" ELSE "vote"
      r2 == Poll(r1, i, TRUE)
  IN IF PollResult(r2) = "won" THEN
        (IF pre THEN Campaign(i, r2, FALSE, transfer) ELSE BecomeLeader(i, r2))
     ELSE Ret(r2, {[Msg(mt, i, v, vt) EXCEPT !.index = LastIndex(r2), !.logTerm = LastTerm(r2),
                                             !.transfer = transfer] : v \in r2.cfg \ {i}})

\* ======== handlers ========
HandleVote(i, r, m) ==
  LET can == r.vote = m.src \/ (r.vote = Nil /\ r.leader = Nil)
             \/ (m.type = "prevote" /\ m.term > r.term)
      rt == IF m.type = "vote" THEN "vote_resp" ELSE "prevote_resp"
  IN IF can /\ (MutVoteAnyLog \/ UpToDate(r, m.index, m.logTerm))
     THEN Ret(IF m.type = "vote" THEN [r EXCEPT !.vote = m.src] ELSE r, {Msg(rt, i, m.src, m.term)})
     ELSE Ret(r, {[Msg(rt, i, m.src, r.term) EXCEPT !.reject = TRUE]})

\* _handle_append() (the follower has already recorded m.src as its leader)
HandleAppend(i, r, m) ==
  LET skip == r.commit - m.index
      adj == m.index < r.commit
      prev == IF adj THEN r.commit ELSE m.index
      pterm == IF adj THEN TermAt(r, r.commit) ELSE m.logTerm
      ents == IF ~adj THEN m.entries
              ELSE IF skip < Len(m.entries) THEN SubSeq(m.entries, skip + 1, Len(m.entries)) ELSE <<>>
      t == TermAt(r, prev)
  IN IF t # pterm THEN
       LET hi == IF t = -1 THEN LastIndex(r) + 1 ELSE FirstIndexOfTerm(r, t, prev)
           ht == IF t = -1 THEN 0 ELSE t
       IN Ret(r, {[Msg("append_resp", i, m.src, r.term) EXCEPT !.reject = TRUE, !.index = m.index,
                   !.hintIndex = hi, !.hintTerm = ht, !.ctx = m.ctx]})
     ELSE
       LET lastNew == prev + Len(ents)
           conf == {p \in 1..Len(ents) : TermAt(r, prev + p) # ents[p].term}
           p0 == IF conf = {} THEN 0 ELSE CHOOSE p \in conf : \A q \in conf : p <= q
           first == prev + p0
           rest == IF p0 = 0 THEN <<>> ELSE SubSeq(ents, p0, Len(ents))
           bad == p0 # 0 /\ first <= r.commit
           truncating == p0 # 0 /\ TermAt(r, first) # -1
           r1 == IF p0 = 0 \/ bad THEN r ELSE [r EXCEPT !.log = SubSeq(r.log, 1, first - 1) \o rest]
           need == p0 # 0 /\ ~bad /\ ((\E k \in 1..Len(rest) : rest[k].kind = "config")
                                      \/ (truncating /\ first <= r.cidx))
           r2 == IF need THEN Recompute(i, r1) ELSE r1
           nc == Min2(m.commit, lastNew)
           r3 == IF nc > r2.commit THEN [r2 EXCEPT !.commit = nc] ELSE r2
       IN [r |-> r3, out |-> {[Msg("append_resp", i, m.src, r.term) EXCEPT !.index = lastNew, !.ctx = m.ctx]},
           rel |-> <<>>, err |-> bad]

HandleSnapshot(i, r, m) ==
  LET sn == m.snap IN
  IF sn.index <= r.commit THEN
     Ret(r, {[Msg("append_resp", i, m.src, r.term) EXCEPT !.index = r.commit]})
  ELSE IF TermAt(r, sn.index) = sn.term THEN
     Ret([r EXCEPT !.commit = sn.index], {[Msg("append_resp", i, m.src, r.term) EXCEPT !.index = sn.index]})
  ELSE
     Ret(Recompute(i, [r EXCEPT !.log = sn.data, !.snap = sn.index, !.commit = sn.index]),
         {[Msg("append_resp", i, m.src, r.term) EXCEPT !.index = sn.index]})

\* _release_reads()
ReleaseReads(i, r) ==
  IF r.pend = <<>> THEN Ret(r, {})
  ELSE
  LET elig == {v \in r.cfg : v = i \/ v \in r.prog}
      val(v) == IF v = i THEN r.rseq ELSE r.ack[v]
      q == Quorum(r)
      ok == {a \in {val(v) : v \in elig} : Cardinality({v \in elig : val(v) >= a}) >= q}
      acked == IF ok = {} THEN -1 ELSE Max(ok)
      done == SelectSeq(r.pend, LAMBDA x : x.seq <= acked)
      keep == SelectSeq(r.pend, LAMBDA x : x.seq > acked)
  IN [r |-> [r EXCEPT !.pend = keep], out |-> {},
      rel |-> [k \in 1..Len(done) |-> [idx |-> done[k].idx, tag |-> done[k].tag]], err |-> FALSE]

\* _handle_append_resp()
HandleAppendResp(i, r, m) ==
  IF m.src \notin r.prog THEN Ret(r, {})
  ELSE
  LET src == m.src
      r0 == IF m.ctx > r.ack[src] THEN [r EXCEPT !.ack[src] = m.ctx] ELSE r
      last == LastIndex(r0)
  IN IF m.reject THEN
       IF m.index > r0.mat[src] THEN
         LET idx == LastIndexOfTerm(r0, m.hintTerm, m.index)
             new == IF m.hintTerm # 0 THEN (IF idx # -1 THEN idx + 1 ELSE m.hintIndex) ELSE m.hintIndex
             nx == Max2(r0.mat[src] + 1, Min2(new, Min2(m.index, last + 1)))
             a == SendAppend(i, [r0 EXCEPT !.nxt[src] = nx], src, TRUE)
         IN Then(a, ReleaseReads(i, a.r))
       ELSE ReleaseReads(i, r0)
     ELSE
       LET r1 == [r0 EXCEPT !.mat[src] = m.index,
                            !.nxt[src] = IF r0.nxt[src] <= m.index THEN m.index + 1 ELSE r0.nxt[src]]
           mc == MaybeCommit(i, r1)
           a == IF m.index <= r0.mat[src] THEN Ret(r0, {})
                ELSE IF mc.ok THEN Then(mc, Bcast(i, mc.r, TRUE))
                ELSE IF mc.r.state # "L" THEN mc
                ELSE IF mc.r.nxt[src] <= last THEN Then(mc, SendAppend(i, mc.r, src, FALSE))
                ELSE mc
           stopped == m.index > r0.mat[src] /\ ~mc.ok /\ mc.r.state # "L"
       IN IF stopped THEN [r |-> a.r, out |-> a.out, rel |-> a.rel, err |-> FALSE]
          ELSE
          LET tn == IF src = a.r.xfer /\ a.r.mat[src] = last
                    THEN {Msg("timeout_now", i, src, a.r.term)} ELSE {}
              b == ReleaseReads(i, a.r)
          IN [r |-> b.r, out |-> a.out \cup tn, rel |-> a.rel \o b.rel, err |-> FALSE]

StepFollower(i, r, m) ==
  IF m.type = "append" THEN HandleAppend(i, [r EXCEPT !.leader = m.src], m)
  ELSE IF m.type = "snapshot" THEN HandleSnapshot(i, [r EXCEPT !.leader = m.src], m)
  ELSE IF m.type = "timeout_now" THEN
     (IF i \in r.cfg THEN Campaign(i, r, FALSE, TRUE) ELSE Ret(r, {}))
  ELSE Ret(r, {})

\* step(m). `ignore` resolves the timing-dependent leader-stickiness check.
Step(i, r0, m, ignore) ==
  IF m.term > r0.term /\ m.type \in {"vote", "prevote"} /\ CheckQuorum /\ r0.leader # Nil
     /\ ignore /\ ~m.transfer
  THEN Ret(r0, {})
  ELSE IF m.term < r0.term THEN
     (IF m.type \in {"append", "snapshot"}
      THEN Ret(r0, {[Msg("append_resp", i, m.src, r0.term) EXCEPT !.reject = TRUE]})
      ELSE IF m.type = "prevote"
      THEN Ret(r0, {[Msg("prevote_resp", i, m.src, r0.term) EXCEPT !.reject = TRUE]})
      ELSE Ret(r0, {}))
  ELSE
  LET r == IF m.term > r0.term /\ ~(m.type = "prevote" \/ (m.type = "prevote_resp" /\ ~m.reject))
           THEN BecomeFollower(r0, m.term, IF m.type \in {"append", "snapshot"} THEN m.src ELSE Nil)
           ELSE r0
      t == m.type
  IN IF t \in {"vote", "prevote"} THEN HandleVote(i, r, m)
     ELSE IF r.state = "L" THEN (IF t = "append_resp" THEN HandleAppendResp(i, r, m) ELSE Ret(r, {}))
     ELSE IF r.state \in {"C", "PC"} THEN
       (IF t \in {"append", "snapshot"} THEN StepFollower(i, BecomeFollower(r, m.term, m.src), m)
        ELSE IF (t = "prevote_resp" /\ r.state = "PC") \/ (t = "vote_resp" /\ r.state = "C") THEN
          LET r2 == Poll(r, m.src, ~m.reject) IN
          IF PollResult(r2) = "won" THEN
             (IF r2.state = "PC" THEN Campaign(i, r2, FALSE, FALSE) ELSE BecomeLeader(i, r2))
          ELSE IF PollResult(r2) = "lost" THEN Ret(BecomeFollower(r2, r2.term, Nil), {})
          ELSE Ret(r2, {})
        ELSE Ret(r, {}))
     ELSE StepFollower(i, r, m)

\* tick() on a leader: the election-timeout branch (CheckQuorum step-down or abort of a
\* pending transfer) and the heartbeat branch, each enabled nondeterministically
LeaderTick(i, r, stepdown, abort, hb) ==
  IF stepdown THEN Ret(BecomeFollower(r, r.term, Nil), {})
  ELSE LET r1 == IF abort THEN [r EXCEPT !.xfer = Nil] ELSE r
       IN IF hb THEN Bcast(i, [r1 EXCEPT !.rseq = r1.rseq + 1], TRUE) ELSE Ret(r1, {})

\* propose(data, kind)
Propose(i, r, e) ==
  LET r1 == [r EXCEPT !.log = Append(r.log, e)]
      r2 == IF e.kind = "config" THEN Recompute(i, r1) ELSE r1
      mc == MaybeCommit(i, r2)
  IN Then(mc, Bcast(i, mc.r, FALSE))

CanPropose(r) == r.state = "L" /\ r.xfer = Nil

CanConfChange(i, r, op, x) ==
  /\ CanPropose(r)
  /\ (SkipTermStartCheck \/ r.commit >= r.tstart)
  /\ r.cidx <= r.commit
  /\ IF op = "add" THEN x \notin r.cfg ELSE x \in r.cfg /\ Cardinality(r.cfg) > 1

ReadIndex(i, r, tag) ==
  IF r.commit < r.tstart THEN Ret([r EXCEPT !.wait = Append(r.wait, tag)], {})
  ELSE RegisterRead(i, r, tag)

Transfer(i, r, t) ==
  LET r1 == [r EXCEPT !.xfer = t] IN
  IF r1.mat[t] = LastIndex(r1) THEN Ret(r1, {Msg("timeout_now", i, t, r1.term)})
  ELSE SendAppend(i, r1, t, TRUE)

\* Raft.__init__ after a restart: persistent state survives, everything else is reset
Restarted(i, r, c) ==
  LET base == [r EXCEPT !.state = "F", !.leader = Nil, !.commit = c, !.tstart = 0, !.rseq = 0]
  IN Recompute(i, Reset(base))

\* ======== the system ========
InitLocal(i) ==
  LET boot == i \in InitVoters IN
  [term |-> IF boot THEN 1 ELSE 0, vote |-> Nil, state |-> "F", leader |-> Nil,
   log |-> IF boot THEN <<BootEnt>> ELSE <<>>, snap |-> 0, commit |-> IF boot THEN 1 ELSE 0,
   cfg |-> IF boot THEN InitVoters ELSE {}, cidx |-> IF boot THEN 1 ELSE 0,
   vg |-> {}, vr |-> {}, prog |-> {}, nxt |-> Zero, mat |-> Zero, ack |-> Zero,
   tstart |-> 0, xfer |-> Nil, rseq |-> 0, pend |-> <<>>, wait |-> <<>>]

Init ==
  /\ s = [i \in Server |-> InitLocal(i)]
  /\ msgs = {}
  /\ elected = {}
  /\ committed = {[idx |-> 1, ent |-> BootEnt, t |-> 1]}
  /\ readsOK = TRUE
  /\ implOK = TRUE
  /\ ctr = [vals |-> 0, crashes |-> 0, reads |-> 0, confs |-> 0, xfers |-> 0, compacts |-> 0]

GlobalCommit == Max({c.idx : c \in committed})

NewCommits(a, b) ==
  {[idx |-> k, ent |-> b.log[k], t |-> b.term] : k \in (a.commit + 1)..b.commit}

\* install handler result `res` for node i; `net` is the network before adding res.out
Install(i, res, net) ==
  /\ s' = [s EXCEPT ![i] = res.r]
  /\ msgs' = net \cup res.out
  /\ committed' = committed \cup NewCommits(s[i], res.r)
  /\ elected' = IF res.r.state = "L" /\ ~(s[i].state = "L" /\ s[i].term = res.r.term)
                THEN elected \cup {<<res.r.term, i>>} ELSE elected
  /\ readsOK' = (readsOK /\ \A k \in 1..Len(res.rel) : res.rel[k].idx >= res.rel[k].tag)
  /\ implOK' = (implOK /\ ~res.err)

Timeout(i) ==
  /\ s[i].state # "L" /\ i \in s[i].cfg
  /\ Install(i, Campaign(i, s[i], PreVote, FALSE), msgs)
  /\ UNCHANGED ctr

Tick(i) ==
  /\ s[i].state = "L"
  /\ \E sd \in (IF CheckQuorum THEN BOOLEAN ELSE {FALSE}), ab \in BOOLEAN, hb \in BOOLEAN :
       /\ (sd \/ ab \/ hb)
       /\ ~(sd /\ (ab \/ hb))
       /\ (ab => s[i].xfer # Nil)
       /\ Install(i, LeaderTick(i, s[i], sd, ab, hb), msgs)
  /\ UNCHANGED ctr

Receive(m) ==
  LET i == m.dst IN
  /\ \E keep \in BOOLEAN, ign \in BOOLEAN :
       /\ (ign => (m.term > s[i].term /\ m.type \in {"vote", "prevote"} /\ CheckQuorum
                   /\ s[i].leader # Nil /\ ~m.transfer))
       /\ Install(i, Step(i, s[i], m, ign), IF keep THEN msgs ELSE msgs \ {m})
  /\ UNCHANGED ctr

Drop(m) ==
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<s, elected, committed, readsOK, implOK, ctr>>

ClientWrite(i) ==
  /\ CanPropose(s[i]) /\ ctr.vals < MaxValues /\ Len(s[i].log) < MaxLogLen
  /\ Install(i, Propose(i, s[i], Ent(s[i].term, "normal", ctr.vals + 1, "", Nil)), msgs)
  /\ ctr' = [ctr EXCEPT !.vals = ctr.vals + 1]

ConfChange(i) ==
  /\ ctr.confs < MaxConfChanges /\ Len(s[i].log) < MaxLogLen
  /\ \E op \in {"add", "remove"}, x \in Server :
       /\ CanConfChange(i, s[i], op, x)
       /\ Install(i, Propose(i, s[i], Ent(s[i].term, "config", 0, op, x)), msgs)
  /\ ctr' = [ctr EXCEPT !.confs = ctr.confs + 1]

ClientRead(i) ==
  /\ s[i].state = "L" /\ ctr.reads < MaxReads
  /\ Install(i, ReadIndex(i, s[i], GlobalCommit), msgs)
  /\ ctr' = [ctr EXCEPT !.reads = ctr.reads + 1]

TransferLeadership(i) ==
  /\ s[i].state = "L" /\ ctr.xfers < MaxTransfers
  /\ \E t \in s[i].prog : Install(i, Transfer(i, s[i], t), msgs)
  /\ ctr' = [ctr EXCEPT !.xfers = ctr.xfers + 1]

Compact(i) ==
  /\ ctr.compacts < MaxCompactions
  /\ \E idx \in (s[i].snap + 1)..s[i].commit :
       Install(i, Ret([s[i] EXCEPT !.snap = idx], {}), msgs)
  /\ ctr' = [ctr EXCEPT !.compacts = ctr.compacts + 1]

Restart(i) ==
  /\ ctr.crashes < MaxCrashes
  /\ \E c \in (IF LossyCommit THEN s[i].snap..s[i].commit ELSE {s[i].commit}) :
       Install(i, Ret(Restarted(i, s[i], c), {}), msgs)
  /\ ctr' = [ctr EXCEPT !.crashes = ctr.crashes + 1]

Next ==
  \/ \E i \in Server : Timeout(i) \/ Tick(i) \/ ClientWrite(i) \/ ConfChange(i) \/ ClientRead(i)
                       \/ TransferLeadership(i) \/ Compact(i) \/ Restart(i)
  \/ \E m \in msgs : Receive(m) \/ Drop(m)

Spec == Init /\ [][Next]_vars

StateConstraint ==
  /\ Cardinality(msgs) <= MaxMsgs
  /\ \A i \in Server : s[i].term <= MaxTerm /\ Len(s[i].log) <= MaxLogLen /\ s[i].rseq <= MaxSeq

\* ======== properties ========
ElectionSafety == \A a, b \in elected : a[1] = b[1] => a[2] = b[2]

LogMatching ==
  \A i, j \in Server : \A k \in 1..Min2(Len(s[i].log), Len(s[j].log)) :
     s[i].log[k].term = s[j].log[k].term => SubSeq(s[i].log, 1, k) = SubSeq(s[j].log, 1, k)

LeaderCompleteness ==
  \A i \in Server : s[i].state = "L" =>
     \A c \in committed : c.t <= s[i].term => (c.idx <= Len(s[i].log) /\ s[i].log[c.idx] = c.ent)

StateMachineSafety ==
  /\ \A c1, c2 \in committed : c1.idx = c2.idx => c1.ent = c2.ent
  /\ \A i \in Server : \A k \in 1..s[i].commit : \A c \in committed : c.idx = k => s[i].log[k] = c.ent

LinearizableReads == readsOK

NoImplAssertion == implOK

\* lemma the implementation relies on: the cached voter set equals the log's configuration
ConfigMatchesLog == \A i \in Server : s[i].cfg = Config(s[i].log)

IndexSanity == \A i \in Server :
  /\ s[i].snap <= s[i].commit /\ s[i].commit <= Len(s[i].log)
  /\ (s[i].state = "L" => \A j \in s[i].prog : s[i].mat[j] <= Len(s[i].log))

Safety == ElectionSafety /\ LogMatching /\ LeaderCompleteness /\ StateMachineSafety
          /\ LinearizableReads /\ NoImplAssertion
=============================================================================
