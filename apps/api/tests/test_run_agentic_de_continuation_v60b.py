from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

from adeu_agentic_de import load_loop_state_ledger, load_task_residual_packet
from adeu_ir.repo import repo_root

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v56a",
    "packages/adeu_agentic_de/tests/fixtures/v56b",
    "packages/adeu_agentic_de/tests/fixtures/v56c",
    "packages/adeu_agentic_de/tests/fixtures/v59a",
    "packages/adeu_agentic_de/tests/fixtures/v59b",
    "packages/adeu_agentic_de/tests/fixtures/v60a",
    "packages/adeu_agentic_de/tests/fixtures/v60b",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v161/evidence_inputs/v59a_workspace_continuity_starter_evidence_v161.json",
    "artifacts/agent_harness/v162/evidence_inputs/v59b_workspace_continuity_restoration_evidence_v162.json",
    "artifacts/agent_harness/v164/evidence_inputs/v60a_continuation_starter_evidence_v164.json",
)


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _script_path() -> Path:
    return (
        _repo_root()
        / "apps"
        / "api"
        / "scripts"
        / "run_agentic_de_continuation_v60b.py"
    )


def _pythonpath_env() -> dict[str, str]:
    root = _repo_root()
    env = os.environ.copy()
    existing = env.get("PYTHONPATH")
    paths = [
        str(root / "apps" / "api" / "src"),
        str(root / "packages" / "adeu_agentic_de" / "src"),
        str(root / "packages" / "urm_runtime" / "src"),
    ]
    if existing:
        paths.append(existing)
    env["PYTHONPATH"] = os.pathsep.join(paths)
    env["TZ"] = "UTC"
    env["LC_ALL"] = "C"
    return env


def _copy_v60b_input_tree(tmp_path: Path) -> tuple[Path, Path]:
    repo_root_path = _repo_root()
    for relative_dir in FIXTURE_DIRS:
        shutil.copytree(
            repo_root_path / relative_dir,
            tmp_path / relative_dir,
            dirs_exist_ok=True,
        )
    for relative_path in EVIDENCE_FILES:
        source = repo_root_path / relative_path
        target = tmp_path / relative_path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    return (
        tmp_path,
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v60b",
    )


def _reanchor_v60a_chain_after_residual_mutation(v60a_root: Path) -> None:
    task_residual_path = v60a_root / "reference_agentic_de_task_residual_packet.json"
    loop_state_ledger_path = v60a_root / "reference_agentic_de_loop_state_ledger.json"
    continuation_decision_path = (
        v60a_root / "reference_agentic_de_continuation_decision_record.json"
    )

    residual = load_task_residual_packet(task_residual_path)
    loop_state_payload = json.loads(loop_state_ledger_path.read_text(encoding="utf-8"))
    loop_state_payload["task_residual_ref"] = residual.residual_id
    loop_state_payload["ledger_id"] = None
    loop_state_ledger_path.write_text(
        json.dumps(loop_state_payload, indent=2) + "\n",
        encoding="utf-8",
    )

    loop_state_ledger = load_loop_state_ledger(loop_state_ledger_path)
    continuation_decision_payload = json.loads(
        continuation_decision_path.read_text(encoding="utf-8")
    )
    continuation_decision_payload["loop_state_ledger_ref"] = loop_state_ledger.ledger_id
    continuation_decision_payload["decision_id"] = None
    continuation_decision_path.write_text(
        json.dumps(continuation_decision_payload, indent=2) + "\n",
        encoding="utf-8",
    )


def _run_script(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(_script_path()), *args],
        cwd=_repo_root(),
        check=False,
        capture_output=True,
        text=True,
        env=_pythonpath_env(),
    )


def test_default_cli_emits_continuation_refresh_decision_record(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v60b_input_tree(tmp_path)

    completed = _run_script("--repo-root", str(temp_root))

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["schema"] == "agentic_de_continuation_refresh_decision_record@1"
    assert payload["refresh_outcome"] == "continue_to_governed_act"
    assert completed.stderr == ""


def test_cli_can_write_all_v60b_outputs(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v60b_input_tree(tmp_path / "repo")
    task_residual_refresh_path = tmp_path / "task_residual_refresh.json"
    continuation_refresh_decision_path = tmp_path / "continuation_refresh_decision.json"

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--task-residual-refresh-output",
        str(task_residual_refresh_path),
        "--continuation-refresh-decision-output",
        str(continuation_refresh_decision_path),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert completed.stdout == ""
    assert json.loads(task_residual_refresh_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_task_residual_refresh_packet@1"
    )
    assert json.loads(
        continuation_refresh_decision_path.read_text(encoding="utf-8")
    )["schema"] == "agentic_de_continuation_refresh_decision_record@1"


def test_invalid_v60b_lane_drift_returns_clean_error(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v60b_input_tree(tmp_path / "repo")
    lane_drift_path = fixture_root / "reference_agentic_de_lane_drift_record.json"
    payload = json.loads(lane_drift_path.read_text(encoding="utf-8"))
    payload["entries"] = payload["entries"][:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    lane_drift_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    completed = _run_script("--repo-root", str(temp_root))

    assert completed.returncode == 2
    assert completed.stdout == ""
    assert completed.stderr.startswith("error: ")


def test_repo_root_rebases_default_v60a_residual_fixture(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v60b_input_tree(tmp_path / "repo")
    v60a_root = fixture_root.parent / "v60a"
    task_residual_path = v60a_root / "reference_agentic_de_task_residual_packet.json"
    payload = json.loads(task_residual_path.read_text(encoding="utf-8"))
    payload["blocker_summary"] = "current_frontier_requires_structured_reproposal"
    payload["residual_id"] = None
    task_residual_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    _reanchor_v60a_chain_after_residual_mutation(v60a_root)

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--continuation-refresh-decision-output",
        str(tmp_path / "continuation_refresh_decision.json"),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(
        (tmp_path / "continuation_refresh_decision.json").read_text(encoding="utf-8")
    )
    assert payload["refresh_outcome"] == "reproposal_required"
