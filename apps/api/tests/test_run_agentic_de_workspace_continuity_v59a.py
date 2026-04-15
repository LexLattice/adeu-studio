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
        / "run_agentic_de_workspace_continuity_v59a.py"
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


def _copy_v59a_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        "packages/adeu_agentic_de/tests/fixtures/v59a/reference_agentic_de_lane_drift_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v59a/reference_copilot_turn_snapshot.json",
        "artifacts/agent_harness/v160/evidence_inputs/v58c_live_harness_hardening_evidence_v160.json",
        "artifacts/agentic_de/v59/workspace_continuity/.gitignore",
    ]
    for relative_path in relative_paths:
        source = repo_root_path / relative_path
        target = tmp_path / relative_path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    return (
        tmp_path,
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v59a",
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


def test_default_cli_emits_continuity_reintegration_report(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v59a_input_tree(tmp_path)

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--live-turn-snapshot",
        str(fixture_root / "reference_copilot_turn_snapshot.json"),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["schema"] == "agentic_de_workspace_continuity_reintegration_report@1"
    assert payload["continuity_reintegration_status"] == "reintegrated"
    assert completed.stderr == ""


def test_cli_can_write_all_v59a_outputs(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v59a_input_tree(tmp_path / "repo")
    region_path = tmp_path / "region.json"
    continuity_admission_path = tmp_path / "continuity_admission.json"
    occupancy_path = tmp_path / "occupancy.json"
    live_turn_admission_path = tmp_path / "live_turn_admission.json"
    live_turn_handoff_path = tmp_path / "live_turn_handoff.json"
    observation_path = tmp_path / "observation.json"
    conformance_path = tmp_path / "conformance.json"
    live_turn_reintegration_path = tmp_path / "live_turn_reintegration.json"
    continuity_reintegration_path = tmp_path / "continuity_reintegration.json"

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--live-turn-snapshot",
        str(fixture_root / "reference_copilot_turn_snapshot.json"),
        "--region-output",
        str(region_path),
        "--continuity-admission-output",
        str(continuity_admission_path),
        "--occupancy-output",
        str(occupancy_path),
        "--live-turn-admission-output",
        str(live_turn_admission_path),
        "--live-turn-handoff-output",
        str(live_turn_handoff_path),
        "--observation-output",
        str(observation_path),
        "--conformance-output",
        str(conformance_path),
        "--live-turn-reintegration-output",
        str(live_turn_reintegration_path),
        "--continuity-reintegration-output",
        str(continuity_reintegration_path),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert json.loads(region_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_workspace_continuity_region_declaration@1"
    )
    assert json.loads(continuity_admission_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_workspace_continuity_admission_record@1"
    )
    assert json.loads(occupancy_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_workspace_occupancy_report@1"
    )
    assert json.loads(live_turn_admission_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_live_turn_admission_record@1"
    )
    assert json.loads(live_turn_handoff_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_live_turn_handoff_record@1"
    )
    assert json.loads(observation_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_local_effect_observation_record@1"
    )
    assert json.loads(conformance_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_local_effect_conformance_report@1"
    )
    assert json.loads(live_turn_reintegration_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_live_turn_reintegration_report@1"
    )
    assert json.loads(
        continuity_reintegration_path.read_text(encoding="utf-8")
    )["schema"] == "agentic_de_workspace_continuity_reintegration_report@1"


def test_invalid_v59a_lane_drift_returns_clean_error(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v59a_input_tree(tmp_path / "repo")
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


def test_occupied_target_returns_clean_error(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v59a_input_tree(tmp_path / "repo")
    target_path = (
        temp_root
        / "artifacts"
        / "agentic_de"
        / "v59"
        / "workspace_continuity"
        / "runtime"
        / "reference_patch_candidate.diff"
    )
    target_path.parent.mkdir(parents=True, exist_ok=True)
    target_path.write_text("out-of-band target content\n", encoding="utf-8")

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--live-turn-snapshot",
        str(fixture_root / "reference_copilot_turn_snapshot.json"),
    )

    assert completed.returncode == 2
    assert completed.stdout == ""
    assert completed.stderr.startswith("error: ")


def test_repo_root_rebases_default_live_turn_snapshot(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v59a_input_tree(tmp_path / "repo")
    snapshot_path = fixture_root / "reference_copilot_turn_snapshot.json"
    payload = json.loads(snapshot_path.read_text(encoding="utf-8"))
    payload["session_id"] = "rebased-v59a-session"
    snapshot_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    completed = _run_script(
        "--repo-root",
        str(temp_root),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    output = json.loads(completed.stdout)
    assert output["continuity_witness_certificate_ref_or_equivalent"].startswith(
        "v59a_continuity_reintegration::rebased-v59a-session::"
    )
