"""The Python transcription of the spec generates exactly the state graph TLC generates.

For every cross-check model, the breadth-first explorer built on proofstack.raftspec must find
the same number of distinct states and the same BFS depth as TLC (results/tlc/<model>.json,
written by scripts/run_tlc.py, single-worker so the depth is exact), and the same number of
generated transitions once TLC's one known duplicate enumeration is accounted for.
"""
import json
import os
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from proofstack.explore import bfs  # noqa: E402
from proofstack.models import MODELS, cfg_text, system  # noqa: E402

XCHECK = [m for m in MODELS if m.startswith("xcheck")]
FAST = os.environ.get("PROOFSTACK_FAST") == "1"


@pytest.mark.parametrize("name", XCHECK)
def test_python_explorer_matches_tlc(name):
    res = ROOT / "results" / "tlc" / f"{name}.json"
    if not res.exists():
        pytest.skip(f"no TLC result for {name}; run scripts/run_tlc.py --xcheck")
    if FAST and name != "xcheck-core":
        pytest.skip("PROOFSTACK_FAST=1")
    tlc = json.loads(res.read_text())
    assert tlc["no_error"] and tlc["left"] == 0
    py = bfs(system(name))
    assert py["complete"] and not py["violations"]
    assert py["distinct"] == tlc["distinct"] and py["depth"] == tlc["depth"]
    # TLC evaluates Tick's (abort, heartbeat) binding twice when the leader has a transfer target,
    # producing one duplicate (identical) successor per such leader state; see docs/raft-spec.md.
    assert tlc["generated"] == py["generated"] + py["xfer_leaders"]


def test_cfg_files_are_generated_from_models():
    for name in MODELS:
        cfg = ROOT / "tla" / "models" / f"{name}.cfg"
        if cfg.exists():
            assert cfg.read_text(encoding="utf-8") == cfg_text(name), f"{cfg} is stale"
