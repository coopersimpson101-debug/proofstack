"""Trace validation of raftstore against the RaftStore spec, including mutation tests that show
the checker rejects implementations that deviate from the spec.

Needs a raftstore checkout with trace export (main at 3a545c8 or later): $RAFTSTORE_DIR (default:
../raftstore next to this repository)."""
import os
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
RS = Path(os.environ.get("RAFTSTORE_DIR", ROOT.parent / "raftstore"))
if not (RS / "raftstore" / "raft" / "trace.py").exists():
    pytest.skip(f"raftstore with trace export not found at {RS}", allow_module_level=True)
sys.path.insert(0, str(RS))

from proofstack.tracecheck import Violation, check_file  # noqa: E402
from raftstore.raft import core  # noqa: E402
from raftstore.sim.cluster import SimCluster, SimConfig  # noqa: E402

SEEDS = int(os.environ.get("TRACECHECK_SEEDS", 6))


def record(tmp_path, seed, cfg=None, steps=1200, name="t"):
    p = tmp_path / f"{name}-{seed}.jsonl"
    c = SimCluster(seed, cfg or SimConfig(), trace_path=str(p))
    c.run(steps)
    c.heal()
    c.close_trace()
    return p


@pytest.mark.parametrize("cfg", [
    SimConfig(),
    SimConfig(nodes=5, p_transfer=0.01),
    SimConfig(p_membership=0.01, p_transfer=0.005),
    SimConfig(storage="disk", p_pull_drive=0.003),
    SimConfig(raft={"prevote": False, "check_quorum": False}),
], ids=["lossy", "transfer5", "membership", "disk", "noprevote"])
def test_simulator_traces_refine_the_spec(tmp_path, cfg):
    for seed in range(SEEDS):
        stats = check_file(record(tmp_path, seed, cfg))
        assert stats["events"] > 1000 and stats["elections"] >= 1


def detects(tmp_path, monkeypatch, patch, cfg=None, seeds=12):
    patch(monkeypatch)
    for seed in range(seeds):
        try:
            p = record(tmp_path, seed, cfg, name="mut")
        except AssertionError:
            continue  # the simulator's own invariant checker fired first; try another seed
        try:
            check_file(p)
        except Violation as e:
            return str(e)
    return None


def test_mutant_vote_without_log_check(tmp_path, monkeypatch):
    msg = detects(tmp_path, monkeypatch,
                  lambda mp: mp.setattr(core.RaftLog, "is_up_to_date", lambda self, i, t: True))
    assert msg and "no spec successor matches" in msg


def test_mutant_prevote_bumps_term(tmp_path, monkeypatch):
    orig = core.Raft._become_pre_candidate

    def bump(self):
        orig(self)
        self.term += 1
    msg = detects(tmp_path, monkeypatch, lambda mp: mp.setattr(core.Raft, "_become_pre_candidate", bump))
    assert msg and "no spec successor matches" in msg


def test_mutant_fast_backtracking_hint(tmp_path, monkeypatch):
    orig = core.RaftLog.first_index_of_term
    msg = detects(tmp_path, monkeypatch, lambda mp: mp.setattr(
        core.RaftLog, "first_index_of_term", lambda self, t, upto: orig(self, t, upto) + 1), seeds=30)
    assert msg and "no spec successor matches" in msg


def test_mutant_read_index_without_quorum(tmp_path, monkeypatch):
    msg = detects(tmp_path, monkeypatch, lambda mp: mp.setattr(
        core.Raft, "_quorum_value", lambda self, mine, f: mine))
    assert msg and "no spec successor matches" in msg


def test_mutant_forgotten_vote_after_restart(tmp_path, monkeypatch):
    msg = detects(tmp_path, monkeypatch, lambda mp: None, cfg=SimConfig(bug_forget_vote=True, p_crash=0.02))
    assert msg and "restart" in msg
