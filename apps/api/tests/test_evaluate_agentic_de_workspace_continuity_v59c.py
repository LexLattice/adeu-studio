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
        / "evaluate_agentic_de_workspace_continuity_v59c.py"
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


def _copy_v59c_input_tree(tmp_path: Path) -> Path:
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
        "packages/adeu_agentic_de/tests/fixtures/v59b/reference_agentic_de_workspace_continuity_restoration_handoff_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v59b/reference_agentic_de_local_effect_restoration_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v59b/reference_agentic_de_workspace_continuity_restoration_reintegration_report.json",
        "packages/adeu_agentic_de/tests/fixtures/v59c/reference_agentic_de_lane_drift_record.json",
        "artifacts/agent_harness/v161/evidence_inputs/v59a_workspace_continuity_starter_evidence_v161.json",
        "artifacts/agent_harness/v162/evidence_inputs/v59b_workspace_continuity_restoration_evidence_v162.json",
    ]
    for relative_path in relative_paths:
        source = repo_root_path / relative_path
        target = tmp_path / relative_path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    return tmp_path


def _run_script(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(_script_path()), *args],
        cwd=_repo_root(),
        check=False,
        capture_output=True,
        text=True,
        env=_pythonpath_env(),
    )


def test_default_cli_emits_workspace_continuity_hardening_register(tmp_path: Path) -> None:
    temp_root = _copy_v59c_input_tree(tmp_path)

    completed = _run_script("--repo-root", str(temp_root))

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["schema"] == "agentic_de_workspace_continuity_hardening_register@1"
    assert payload["entries"][0]["recommended_outcome"] == (
        "candidate_for_later_continuity_hardening"
    )
    assert completed.stderr == ""


def test_cli_can_write_v59c_output_file(tmp_path: Path) -> None:
    temp_root = _copy_v59c_input_tree(tmp_path / "repo")
    output_path = tmp_path / "hardening.json"

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--hardening-output",
        str(output_path),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert json.loads(output_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_workspace_continuity_hardening_register@1"
    )
    assert completed.stdout == ""


def test_invalid_v59c_lane_drift_returns_clean_error(tmp_path: Path) -> None:
    temp_root = _copy_v59c_input_tree(tmp_path / "repo")
    lane_drift_path = (
        temp_root
        / "packages"
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v59c"
        / "reference_agentic_de_lane_drift_record.json"
    )
    payload = json.loads(lane_drift_path.read_text(encoding="utf-8"))
    payload["entries"] = payload["entries"][:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    lane_drift_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    completed = _run_script("--repo-root", str(temp_root))

    assert completed.returncode == 2
    assert completed.stdout == ""
    assert completed.stderr.startswith("error: ")


def test_explicit_v59c_lane_drift_override_is_used(tmp_path: Path) -> None:
    temp_root = _copy_v59c_input_tree(tmp_path / "repo")
    lane_drift_path = (
        temp_root
        / "packages"
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v59c"
        / "alt_lane_drift.json"
    )
    source = (
        temp_root
        / "packages"
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v59c"
        / "reference_agentic_de_lane_drift_record.json"
    )
    shutil.copyfile(source, lane_drift_path)

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--v59c-lane-drift",
        str(lane_drift_path),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["schema"] == "agentic_de_workspace_continuity_hardening_register@1"
