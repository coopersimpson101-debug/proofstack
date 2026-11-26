# Changelog

All notable changes to this project are documented here. The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [0.1.0] - 2026-11-26

First public release.

### Added
- `tla/RaftStore.tla`: TLA+ specification of raftstore's Raft as implemented (PreVote, CheckQuorum,
  fast backtracking, current-term commit rule, snapshots, single-server membership changes,
  leadership transfer, ReadIndex, crash/restart) with eight safety invariants, bounded TLC models
  and deliberately broken variants that TLC must refute.
- `proofstack/raftspec.py`: Python transcription of the spec, tied to the TLA+ text by identical
  TLC / Python state-graph sizes on the cross-check models.
- `proofstack/tracecheck.py`: refinement checker for raftstore execution traces (simulator and
  real multi-process clusters), with mutation tests.
- `lean/`: Lean 4 models and proofs for orbit-os's buddy allocator (invariant preservation, no
  overlap, alignment, free + allocated = managed, complete coalescing, alloc-then-free roundtrip)
  and stage-1 page tables (`map_range` correctness, first-mapping-wins, kernel/user separation,
  higher-half alias, W^X), plus the `orbitmodel` executable.
- `harness/`: host builds of orbit-os's `buddy.c` and `mmu.c` with zig; differential tests against
  the Lean model and a bounded exhaustive check of `mmu_init`.
- Findings: overlapping `buddy_add_range` double-manages pages (orbit-os, latent); unaligned
  `map_range` arguments lose the last page (orbit-os, latent); a torn last Ready batch on restart
  (raftstore, safe); the current-term commit rule is almost redundant given the leader no-op
  (raftstore, observation).

[0.1.0]: https://github.com/coopersimpson101-debug/proofstack/releases/tag/v0.1.0
