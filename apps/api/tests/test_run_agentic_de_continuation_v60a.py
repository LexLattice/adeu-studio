from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

from adeu_ir.repo import repo_root

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v56a",
    "packages/adeu_agentic_de/tests/fixtures/v56b",
    "packages/adeu_agentic_de/tests/fixtures/v56c",
    "packages/adeu_agentic_de/tests/fixtures/v59a",
    "packages/adeu_agentic_de/tests/fixtures/v59b",
    "packages/adeu_agentic_de/tests/fixtures/v59c",
    "packages/adeu_agentic_de/tests/fixtures/v60a",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v152/evidence_inputs/v56a_agentic_de_interaction_governance_starter_evidence_v152.json",
    "artifacts/agent_harness/v153/evidence_inputs/v56b_bounded_live_gate_starter_evidence_v153.json",
    "artifacts/agent_harness/v154/evidence_inputs/v56c_harvest_calibration_migration_evidence_v154.json",
    "artifacts/agent_harness/v155/evidence_inputs/v57a_local_effect_observation_evidence_v155.json",
    "artifacts/agent_harness/v156/evidence_inputs/v57b_local_effect_restoration_evidence_v156.json",
    "artifacts/agent_harness/v157/evidence_inputs/v57c_local_effect_hardening_evidence_v157.json",
    "artifacts/agent_harness/v158/evidence_inputs/v58a_live_harness_bind_evidence_v158.json",
    "artifacts/agent_harness/v159/evidence_inputs/v58b_live_restoration_state_evidence_v159.json",
    "artifacts/agent_harness/v160/evidence_inputs/v58c_live_harness_hardening_evidence_v160.json",
    "artifacts/agent_harness/v161/evidence_inputs/v59a_workspace_continuity_starter_evidence_v161.json",
    "artifacts/agent_harness/v162/evidence_inputs/v59b_workspace_continuity_restoration_evidence_v162.json",
    "artifacts/agent_harness/v163/evidence_inputs/v59c_workspace_continuity_hardening_evidence_v163.json",
)


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _script_path() -> Path:
    return (
        _repo_root()
        / "apps"
        / "api"
        / "scripts"
        / "run_agentic_de_continuation_v60a.py"
    )


def _pythonpath_env() -> dict[str, str]:
    root = _repo_root()
    env = os.environ.copy()
    existing = env.get("PYTHONPATH")
    paths = [
        str(root / "apps" / "api" / "src"),
        str(root / "packages" / "urm_runtime" / "src"),
    ]
    if existing:
        paths.append(existing)
    env["PYTHONPATH"] = os.pathsep.join(paths)
    env["TZ"] = "UTC"
    env["LC_ALL"] = "C"
    return env


def _copy_v60a_input_tree(tmp_path: Path) -> tuple[Path, Path]:
    repo_root_path = _repo_root()
    for relative_dir in FIXTURE_DIRS:
        shutil.copytree(
            repo_root_path / relative_dir,
            tmp_path / relative_dir,
            dirs_exist_ok=True,
        )
    extra_paths = [
        *EVIDENCE_FILES,
        "artifacts/agentic_de/v59/workspace_continuity/.gitignore",
    ]
    for relative_path in extra_paths:
        source = repo_root_path / relative_path
        target = tmp_path / relative_path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    return (
        tmp_path,
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v60a",
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


def test_default_cli_emits_continuation_decision_record(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v60a_input_tree(tmp_path)

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--live-turn-snapshot",
        str(fixture_root / "reference_copilot_turn_snapshot.json"),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["schema"] == "agentic_de_continuation_decision_record@1"
    assert payload["continuation_outcome"] == "continue_to_governed_act"
    assert completed.stderr == ""


def test_cli_can_write_all_v60a_outputs(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v60a_input_tree(tmp_path / "repo")
    seed_intent_path = tmp_path / "seed_intent.json"
    task_charter_path = tmp_path / "task_charter.json"
    task_residual_path = tmp_path / "task_residual.json"
    loop_state_ledger_path = tmp_path / "loop_state_ledger.json"
    continuation_decision_path = tmp_path / "continuation_decision.json"

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--live-turn-snapshot",
        str(fixture_root / "reference_copilot_turn_snapshot.json"),
        "--seed-intent-output",
        str(seed_intent_path),
        "--task-charter-output",
        str(task_charter_path),
        "--task-residual-output",
        str(task_residual_path),
        "--loop-state-ledger-output",
        str(loop_state_ledger_path),
        "--continuation-decision-output",
        str(continuation_decision_path),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert completed.stdout == ""
    assert json.loads(seed_intent_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_seed_intent_record@1"
    )
    assert json.loads(task_charter_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_task_charter_packet@1"
    )
    assert json.loads(task_residual_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_task_residual_packet@1"
    )
    assert json.loads(loop_state_ledger_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_loop_state_ledger@1"
    )
    assert json.loads(
        continuation_decision_path.read_text(encoding="utf-8")
    )["schema"] == "agentic_de_continuation_decision_record@1"


def test_invalid_v60a_lane_drift_returns_clean_error(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v60a_input_tree(tmp_path / "repo")
    lane_drift_path = fixture_root / "reference_agentic_de_lane_drift_record.json"
    payload = json.loads(lane_drift_path.read_text(encoding="utf-8"))
    payload["entries"] = payload["entries"][:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    lane_drift_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--live-turn-snapshot",
        str(fixture_root / "reference_copilot_turn_snapshot.json"),
    )

    assert completed.returncode == 2
    assert completed.stdout == ""
    assert completed.stderr.startswith("error: ")


def test_repo_root_rebases_default_v60a_seed_fixture(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v60a_input_tree(tmp_path / "repo")
    seed_intent_path = fixture_root / "reference_agentic_de_seed_intent_record.json"
    payload = json.loads(seed_intent_path.read_text(encoding="utf-8"))
    payload["declared_completion_test_summary"] = "rebased-v60a-completion-test"
    payload["seed_intent_id"] = None
    seed_intent_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    task_charter_path = tmp_path / "task_charter.json"
    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--task-charter-output",
        str(task_charter_path),
        "--continuation-decision-output",
        str(tmp_path / "continuation_decision.json"),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    charter_payload = json.loads(task_charter_path.read_text(encoding="utf-8"))
    assert charter_payload["completion_test_summary"] == "rebased-v60a-completion-test"
