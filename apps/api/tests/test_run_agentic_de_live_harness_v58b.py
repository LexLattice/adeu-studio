from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

from adeu_ir.repo import repo_root


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _script_path() -> Path:
    return (
        _repo_root()
        / "apps"
        / "api"
        / "scripts"
        / "run_agentic_de_live_harness_v58b.py"
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


def _copy_v58b_input_tree(tmp_path: Path) -> tuple[Path, Path]:
    repo_root_path = _repo_root()
    relative_paths = [
        "packages/adeu_agentic_de/tests/fixtures/v56a/reference_agentic_de_domain_packet.json",
        "packages/adeu_agentic_de/tests/fixtures/v56a/reference_agentic_de_morph_ir.json",
        "packages/adeu_agentic_de/tests/fixtures/v56a/reference_agentic_de_interaction_contract.json",
        "packages/adeu_agentic_de/tests/fixtures/v56a/reference_agentic_de_action_proposal.json",
        "packages/adeu_agentic_de/tests/fixtures/v56a/reference_agentic_de_membrane_checkpoint.json",
        "packages/adeu_agentic_de/tests/fixtures/v56a/reference_agentic_de_morph_diagnostics.json",
        "packages/adeu_agentic_de/tests/fixtures/v56a/reference_agentic_de_conformance_report.json",
        "packages/adeu_agentic_de/tests/fixtures/v56b/reference_agentic_de_lane_drift_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v56b/reference_agentic_de_action_class_taxonomy.json",
        "packages/adeu_agentic_de/tests/fixtures/v56b/reference_agentic_de_runtime_state.json",
        "packages/adeu_agentic_de/tests/fixtures/v56b/reference_agentic_de_action_ticket.json",
        "packages/adeu_agentic_de/tests/fixtures/v56b/reference_agentic_de_morph_diagnostics.json",
        "packages/adeu_agentic_de/tests/fixtures/v56b/reference_agentic_de_conformance_report.json",
        "packages/adeu_agentic_de/tests/fixtures/v56c/reference_agentic_de_lane_drift_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v56c/reference_agentic_de_runtime_harvest_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v56c/reference_agentic_de_governance_calibration_register.json",
        "packages/adeu_agentic_de/tests/fixtures/v56c/reference_agentic_de_migration_decision_register.json",
        "packages/adeu_agentic_de/tests/fixtures/v57a/reference_agentic_de_lane_drift_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v57a/reference_agentic_de_local_effect_observation_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v57a/reference_agentic_de_local_effect_conformance_report.json",
        "packages/adeu_agentic_de/tests/fixtures/v57b/reference_agentic_de_lane_drift_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v57b/reference_agentic_de_local_effect_restoration_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v57c/reference_agentic_de_lane_drift_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v57c/reference_agentic_de_local_effect_hardening_register.json",
        "packages/adeu_agentic_de/tests/fixtures/v58a/reference_agentic_de_lane_drift_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v58a/reference_agentic_de_live_turn_admission_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v58a/reference_agentic_de_live_turn_handoff_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v58a/reference_agentic_de_live_turn_reintegration_report.json",
        "packages/adeu_agentic_de/tests/fixtures/v58b/reference_agentic_de_lane_drift_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v58b/reference_copilot_turn_snapshot.json",
        "artifacts/agent_harness/v152/evidence_inputs/v56a_agentic_de_interaction_governance_starter_evidence_v152.json",
        "artifacts/agent_harness/v153/evidence_inputs/v56b_bounded_live_gate_starter_evidence_v153.json",
        "artifacts/agent_harness/v154/evidence_inputs/v56c_harvest_calibration_migration_evidence_v154.json",
        "artifacts/agent_harness/v155/evidence_inputs/v57a_local_effect_observation_evidence_v155.json",
        "artifacts/agent_harness/v156/evidence_inputs/v57b_local_effect_restoration_evidence_v156.json",
        "artifacts/agent_harness/v157/evidence_inputs/v57c_local_effect_hardening_evidence_v157.json",
        "artifacts/agent_harness/v158/evidence_inputs/v58a_live_harness_bind_evidence_v158.json",
        "artifacts/agentic_de/v57/local_effect/.gitignore",
    ]
    for relative_path in relative_paths:
        source = repo_root_path / relative_path
        target = tmp_path / relative_path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    return (
        tmp_path,
        tmp_path
        / "packages"
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v58b",
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


def test_default_cli_emits_live_restoration_reintegration_report(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v58b_input_tree(tmp_path)

    completed = _run_script(
        "--repo-root",
        str(temp_root),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["schema"] == "agentic_de_live_restoration_reintegration_report@1"
    assert payload["restoration_reintegration_status"] == "reintegrated"
    assert completed.stderr == ""


def test_cli_can_write_all_v58b_outputs(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v58b_input_tree(tmp_path / "repo")
    handoff_path = tmp_path / "handoff.json"
    restoration_path = tmp_path / "restoration.json"
    reintegration_path = tmp_path / "reintegration.json"

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--live-turn-snapshot",
        str(fixture_root / "reference_copilot_turn_snapshot.json"),
        "--handoff-output",
        str(handoff_path),
        "--restoration-output",
        str(restoration_path),
        "--reintegration-output",
        str(reintegration_path),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert json.loads(handoff_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_live_restoration_handoff_record@1"
    )
    assert json.loads(restoration_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_local_effect_restoration_record@1"
    )
    assert json.loads(reintegration_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_live_restoration_reintegration_report@1"
    )


def test_invalid_v58b_lane_drift_returns_clean_error(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v58b_input_tree(tmp_path / "repo")
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


def test_invalid_v58a_lane_drift_returns_clean_error(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v58b_input_tree(tmp_path / "repo")
    lane_drift_path = (
        fixture_root.parent / "v58a" / "reference_agentic_de_lane_drift_record.json"
    )
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


def test_default_snapshot_path_follows_selected_repo_root(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v58b_input_tree(tmp_path / "repo")
    snapshot_path = fixture_root / "reference_copilot_turn_snapshot.json"
    payload = json.loads(snapshot_path.read_text(encoding="utf-8"))
    payload["writes_allowed"] = False
    snapshot_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    completed = _run_script("--repo-root", str(temp_root))

    assert completed.returncode == 2
    assert completed.stdout == ""
    assert completed.stderr.startswith("error: ")


def test_restoration_time_snapshot_mismatch_returns_clean_error(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v58b_input_tree(tmp_path / "repo")
    snapshot_path = fixture_root / "reference_copilot_turn_snapshot.json"
    payload = json.loads(snapshot_path.read_text(encoding="utf-8"))
    payload["writes_allowed"] = False
    snapshot_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--live-turn-snapshot",
        str(snapshot_path),
    )

    assert completed.returncode == 2
    assert completed.stdout == ""
    assert completed.stderr.startswith("error: ")
