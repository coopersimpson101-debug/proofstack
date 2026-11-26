## What does this change?

<!-- One or two sentences. Link the issue if there is one. -->

## How is it tested?

- [ ] `cd lean && lake build` (no `sorry`, no new axioms)
- [ ] `python scripts/run_tlc.py --xcheck` and `python -m pytest -q`
- [ ] trace validation: `python scripts/validate_traces.py ...`
- [ ] differential tests against the C code (`tests/test_*_diff.py`, `tests/test_mmu_bounded.py`)

## Claims checklist

- [ ] every number in README/docs comes from a run in this PR or is unchanged
- [ ] "proved" is only used for statements checked by Lean or exhaustively by TLC; everything else says "tested"
- [ ] if the C code or raftstore changed upstream, the pinned commits in CI were updated deliberately
