from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

from adeu_agentic_de.workspace_continuity import DEFAULT_WORKSPACE_CONTINUITY_PAYLOAD_TEXT
from adeu_ir.repo import repo_root


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _script_path() -> Path:
    return (
        _repo_root()
        / "apps"
        / "api"
        / "scripts"
        / "run_agentic_de_workspace_continuity_v59b.py"
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


def _seed_prior_governed_target_state(temp_root: Path, fixture_root: Path) -> None:
    observation_path = (
        fixture_root.parent
        / "v59a"
        / "reference_agentic_de_local_effect_observation_record.json"
    )
    observation_payload = json.loads(observation_path.read_text(encoding="utf-8"))
    observed_write_set = observation_payload["observed_write_set"]
    observed_entry = observed_write_set[0]
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
    target_path.write_text(DEFAULT_WORKSPACE_CONTINUITY_PAYLOAD_TEXT, encoding="utf-8")
    marker_path = (
        temp_root
        / "artifacts"
        / "agentic_de"
        / "v59"
        / "workspace_continuity"
        / "_observer"
        / "reference_governed_target_lineage.json"
    )
    marker_path.parent.mkdir(parents=True, exist_ok=True)
    marker_payload = {
        "target_relative_path": "runtime/reference_patch_candidate.diff",
        "governed_observation_ref": observation_payload["observation_id"],
        "target_content_sha256": observed_entry["content_sha256"],
    }
    marker_path.write_text(json.dumps(marker_payload, indent=2) + "\n", encoding="utf-8")


def _copy_v59b_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        "packages/adeu_agentic_de/tests/fixtures/v59a/reference_agentic_de_workspace_continuity_region_declaration.json",
        "packages/adeu_agentic_de/tests/fixtures/v59a/reference_agentic_de_workspace_continuity_admission_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v59a/reference_agentic_de_workspace_occupancy_report.json",
        "packages/adeu_agentic_de/tests/fixtures/v59a/reference_agentic_de_live_turn_admission_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v59a/reference_agentic_de_live_turn_handoff_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v59a/reference_agentic_de_local_effect_observation_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v59a/reference_agentic_de_local_effect_conformance_report.json",
        "packages/adeu_agentic_de/tests/fixtures/v59a/reference_agentic_de_live_turn_reintegration_report.json",
        "packages/adeu_agentic_de/tests/fixtures/v59a/reference_agentic_de_workspace_continuity_reintegration_report.json",
        "packages/adeu_agentic_de/tests/fixtures/v59b/reference_agentic_de_lane_drift_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v59b/reference_copilot_turn_snapshot.json",
        "artifacts/agent_harness/v161/evidence_inputs/v59a_workspace_continuity_starter_evidence_v161.json",
        "artifacts/agentic_de/v59/workspace_continuity/.gitignore",
    ]
    for relative_path in relative_paths:
        source = repo_root_path / relative_path
        target = tmp_path / relative_path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    fixture_root = tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v59b"
    _seed_prior_governed_target_state(tmp_path, fixture_root)
    return tmp_path, fixture_root


def _run_script(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(_script_path()), *args],
        cwd=_repo_root(),
        check=False,
        capture_output=True,
        text=True,
        env=_pythonpath_env(),
    )


def test_default_cli_emits_continuity_restoration_reintegration_report(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v59b_input_tree(tmp_path)

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--live-turn-snapshot",
        str(fixture_root / "reference_copilot_turn_snapshot.json"),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["schema"] == (
        "agentic_de_workspace_continuity_restoration_reintegration_report@1"
    )
    assert payload["continuity_restoration_reintegration_status"] == "reintegrated"
    assert completed.stderr == ""


def test_cli_can_write_all_v59b_outputs(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v59b_input_tree(tmp_path / "repo")
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
        "agentic_de_workspace_continuity_restoration_handoff_record@1"
    )
    assert json.loads(restoration_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_local_effect_restoration_record@1"
    )
    assert json.loads(reintegration_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_workspace_continuity_restoration_reintegration_report@1"
    )


def test_invalid_v59b_lane_drift_returns_clean_error(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v59b_input_tree(tmp_path / "repo")
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


def test_repo_root_rebases_default_live_turn_snapshot(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v59b_input_tree(tmp_path / "repo")
    snapshot_path = fixture_root / "reference_copilot_turn_snapshot.json"
    payload = json.loads(snapshot_path.read_text(encoding="utf-8"))
    payload["profile_version"] = "profile.v2"
    snapshot_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    completed = _run_script(
        "--repo-root",
        str(temp_root),
    )

    assert completed.returncode == 2
    assert completed.stdout == ""
    assert (
        completed.stderr
        == (
            "error: V59-B restoration-time session capability snapshot must match "
            "the admitted V59-A continuation posture\n"
        )
    )
