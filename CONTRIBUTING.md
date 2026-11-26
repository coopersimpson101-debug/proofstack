# Contributing to proofstack

proofstack holds specifications, proofs and checkers for two other repositories
([raftstore](https://github.com/coopersimpson101-debug/raftstore) and
[orbit-os](https://github.com/coopersimpson101-debug/orbit-os)). Contributions are welcome as long as
they keep the distinction between *proved*, *model-checked* and *tested* sharp.

## Ground rules

- **Lean:** no `sorry`, `admit`, `native_decide` or new `axiom`s. `lake build` must succeed with the
  toolchain pinned in `lean/lean-toolchain`.
- **TLA+:** the spec transcribes `raftstore/raft/core.py`. If you change an action, change the Python
  transcription (`proofstack/raftspec.py`) the same way; `tests/test_spec_vs_tlc.py` checks that both
  generate the same number of distinct states for the cross-check models.
- **Faithfulness:** models of C code are tied to the C code by differential tests. If you change a model,
  rerun `tests/test_buddy_diff.py`, `tests/test_mmu_diff.py` and `tests/test_mmu_bounded.py`.
- **Honesty:** every number in the README comes from `results/` produced by the scripts in `scripts/`.

## Development setup

```sh
pip install -e ".[test]" ziglang            # Python checkers, pytest, the zig C compiler
python harness/build.py --orbit-os ../orbit-os   # C drivers for buddy.c / mmu.c
(cd lean && lake build)                      # proofs + the `orbitmodel` executable
python scripts/run_tlc.py --xcheck           # needs Java and tla2tools.jar (TLA2TOOLS=...)
python -m pytest -q
```

By contributing you agree that your contributions are licensed under the MIT License.
