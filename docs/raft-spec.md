# The RaftStore TLA+ spec and trace validation

`tla/RaftStore.tla` specifies Raft **as implemented in raftstore** (`raftstore/raft/core.py`,
commit `69c2968`, merged into `main` as `3a545c8`; protocol code identical to `main` `f1fc71f` apart from the
opt-in trace hooks). Each per-node operator is a transcription of one method, with the same
control flow and arithmetic, and returns the new local state plus the messages it sends:

| spec operator | core.py | notes |
|---|---|---|
| `Campaign(i, r, pre, transfer)` | `_campaign` | PreVote asks for `term+1` without changing the term; a single voter wins immediately |
| `Step(i, r, m, ignore)` | `step` | higher-term handling, stale-term replies, dispatch by role; `ignore` = leader stickiness (CheckQuorum) |
| `HandleVote` | `_handle_vote` | `can` condition and `is_up_to_date` exactly as in the code |
| `HandleAppend` | `_handle_append` | skips the already-committed prefix, conflict detection, fast-backtracking hint via `FirstIndexOfTerm` (bisect_left semantics), config recompute on truncation |
| `HandleAppendResp` | `_handle_append_resp` | hint resolution via `LastIndexOfTerm` (bisect_right semantics), `next = max(match+1, min(new, m.index, last+1))`, commit, TimeoutNow when the transferee caught up, ReadIndex release |
| `HandleSnapshot` | `_handle_snapshot` | the three cases: stale, matching entry, restore |
| `MaybeCommit` | `_maybe_commit` | quorum-th match, **current-term rule** (switchable: `UnsafeCommitAnyTerm`), registers waiting reads, step-down after own removal |
| `BecomeLeader` | `_become_leader` | progress reset, no-op entry (switchable: `MutNoNoop`) |
| `SendAppend` / `Bcast` | `_send_append` / `_bcast_append` | optimistic pipelining (`next = last+1`), snapshot when `prev` was compacted |
| `RegisterRead` / `ReleaseReads` | `_register_read` / `_release_reads` | ReadIndex: new `read_seq`, heartbeat ctx, quorum of `acked_ctx` |
| `Recompute` | `_recompute_config` | voters and config index from the log; leader progress for added / removed voters |
| `LeaderTick` | `_tick_leader` | CheckQuorum step-down, abort of a stalled transfer, heartbeat — each a nondeterministic choice |
| `Propose`, `CanConfChange` | `propose`, `propose_conf_change` | single-server change only after the leader committed in its term and the previous change committed (switchable: `SkipTermStartCheck`) |
| `Transfer` | `transfer_leadership` | TimeoutNow immediately if the target is caught up, else an append |
| `Restarted` | `Raft.__init__` after a crash | persistent state survives; with `LossyCommit` the commit index may roll back (it is written without fsync) |

**Abstractions.** Clocks are replaced by nondeterminism that includes every timing the code
allows: any non-leader voter may time out at any moment; a leader tick may step down (CheckQuorum),
abort a transfer and/or send heartbeats; a node that knows a leader may ignore a higher-term
(pre)vote request. Lease reads (`read_only="lease"`) are not modelled. Message size caps
(64 entries / 1 MiB) are larger than any bounded log. The network is a set of messages: delivery
may keep the message (duplication), `Drop` loses it, and any message can be delivered at any time
(reordering). Crash + restart is one atomic step; a crashed node's time off is indistinguishable
from it not being scheduled.

**Snapshot trick.** A node keeps its whole log; entries at or below `snap` are compacted and no
operator reads them (`TermAt` returns `-1`, like `term_at()` returning `None`). The retained prefix
stands for the snapshot's state-machine image, so State Machine Safety across snapshots is a
direct comparison of log prefixes.

## Properties (checked as TLC invariants)

* `ElectionSafety` — at most one leader per term, over the whole history.
* `LogMatching` — same index and term ⇒ identical prefixes, for every pair of nodes.
* `LeaderCompleteness` — every entry committed at a term `≤ T` is in the log of every leader of term `T`.
* `StateMachineSafety` — no index is ever committed with two different entries, and every node's
  committed prefix agrees with the commit history.
* `LinearizableReads` — every ReadIndex result is `≥` the highest index committed anywhere when
  the read was requested (so a read observes every write acknowledged before it started).
* `NoImplAssertion` — the code's `AssertionError` guards in `RaftLog.append` (overwriting a
  committed entry, leaving a gap) can never fire.
* `ConfigMatchesLog` — the cached voter set always equals the configuration computed from the log
  (the implementation relies on this).
* `IndexSanity` — `snap ≤ commit ≤ last`, and a leader's `match` never exceeds its log.

## Model checking

`proofstack/models.py` defines every bounded model once; `scripts/run_tlc.py` writes the `.cfg`
into `tla/models/`, runs TLC and stores the raw output in `results/tlc/`. The bounds are on terms,
log length, client values, crashes, reads, membership changes, transfers, compactions,
messages in flight and `read_seq` (every heartbeat increments it, so it must be bounded).

The `xcheck-*` models are also explored by `proofstack/explore.py`, a breadth-first search over the
Python transcription that the trace checker uses. `tests/test_spec_vs_tlc.py` requires the same
number of distinct states and the same BFS depth as TLC (single-worker run, where TLC's depth is
exact), and the same number of generated transitions up to one documented TLC artefact: on the
models without leadership transfer the generated counts are identical (e.g. 9,026,505 generated /
975,216 distinct on both sides for `xcheck-snapshots`); with transfer enabled TLC reports exactly one
extra generated transition per explored state in which a leader has a transfer target. Printing the
bindings with `PrintT` shows why: TLC evaluates `Tick`'s binding `sd = FALSE, ab = TRUE, hb = TRUE`
twice there and generates the same successor twice (on a Tick-only closure both tools reach the same
6 states; TLC counts 15 transitions, the explorer 13). The test asserts
`TLC generated = explorer generated + #(state, leader with transfer target)`, which holds exactly.

The `mut-*` models switch on one deliberate bug each:

| model | deliberate bug | TLC result (`results/tlc/`) |
|---|---|---|
| `mut-vote-any-log` | grant votes without the up-to-date check | `LeaderCompleteness` violated, 13-state counterexample, 3 s |
| `mut-figure8` | no leader no-op **and** commit old-term entries by counting | `LeaderCompleteness` violated, 35-state counterexample (the Raft paper's Figure 8), 305 s |
| `mut-membership` | allow a membership change before the leader committed in its term | **no violation** at these bounds (4 nodes, terms ≤ 3, log ≤ 4, 2 changes; 21,185,127 states, complete) — the known single-server-change anomaly needs more terms and entries than this model allows, so this mutant is *not* refuted here |

### Finding: the current-term commit rule is (almost) redundant in raftstore

With `UnsafeCommitAnyTerm` alone (no-op kept), neither TLC nor 30 mutated simulator seeds produced
a violation. The reason is structural: a new leader appends its no-op immediately, and
`_send_append` always ships *everything* from `next` to the end of the log, so every success ack in
a term covers the no-op; the quorum-th match can only stop at an older-term index when an append
is cut by the 64-entry / 1 MiB message cap (not modelled) or comes from a snapshot response
(whose index is already committed). The rule in `_maybe_commit` is still the right defence-in-depth,
and the paper's anomaly reappears as soon as the no-op is removed (`mut-figure8`).

## Trace validation

raftstore (since `3a545c8`) can record every public `Raft` call as a JSON line
(input, queued messages, released reads, log mutations, resulting state). `proofstack/tracecheck.py`
is a **refinement checker written in Python against the Python transcription of the spec's
actions** (not TLC trace validation). For every traced call it enumerates the spec's successors
for that node and input — the nondeterminism is exactly the spec's — and requires one of them to
reproduce the logged post-state (term, vote, role, leader, commit, snapshot point, last
index/term, voters, config index, vote tally, per-peer match/next/acked ctx, term-start index,
transfer target, read sequence, pending and waiting reads), the logged log suffix, the exact set of
sent messages and the released reads. Deliveries are linked to the sender's checked event, so a
received message must have been sent. Restarts must resume from a state the node had at one of its
recent persist (`ready`) points. Over the whole trace the checker tracks the spec's history
variables and checks Election Safety, State Machine Safety, Leader Completeness, linearizable
ReadIndex and, at the end, Log Matching.

Why a Python checker rather than TLC trace validation: the traces are long (≈9,000 events per
simulator run) and the state per node includes logs of hundreds of entries; one Python pass per
trace takes about a second, and the transcription is tied to the TLA+ text by the state-graph
equality test above. Multi-process traces (one file per process, no global order) are merged by
wall-clock timestamp with causal waiting: an event that receives a message is processed only
after the event that sent it.

### Finding: a crash in the middle of persisting one Ready batch leaves a torn suffix

In the disk-backed simulator scenarios a node can restart with only part of the last batch it was
writing (e.g. entries 97 of 97–99): the WAL is appended record by record and the drive was pulled
or power was cut in between. That state is not any state the node had at a persist point, so the
first version of the checker rejected 10 of 260 traces. It is safe — the acknowledgement for the
batch is only sent after `save()` returns, so nobody has seen the lost suffix — and the checker now
accepts exactly "previous persisted state + a prefix of the last batch" (`restart_torn_batch` in
`results/tracecheck.json`). The TLA+ `Restart` action does not include this case; it is an
implementation behaviour that the checker validates separately.

### The checker rejects wrong implementations

`tests/test_tracecheck.py` runs the simulator with a deliberately broken `Raft` and requires the
checker to reject the trace: votes without the log check, PreVote that bumps the term, an
off-by-one fast-backtracking hint, ReadIndex released without a quorum, and a restart that forgets
the persisted vote.
