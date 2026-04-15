from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import run_agentic_de_workspace_continuity_v59b
from adeu_agentic_de.workspace_continuity import DEFAULT_WORKSPACE_CONTINUITY_PAYLOAD_TEXT
from adeu_ir.repo import repo_root
from urm_runtime import CopilotTurnSnapshot

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v59b"


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _seed_prior_governed_target_state(temp_root: Path, fixture_root: Path) -> None:
    observation_payload = _load_json(
        fixture_root.parent / "v59a",
        "reference_agentic_de_local_effect_observation_record.json",
    )
    assert isinstance(observation_payload, dict)
    observed_write_set = observation_payload["observed_write_set"]
    assert isinstance(observed_write_set, list) and len(observed_write_set) == 1
    observed_entry = observed_write_set[0]
    assert isinstance(observed_entry, dict)
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
    repo_root_path = _repo_root_path()
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


def _load_snapshot(root: Path) -> CopilotTurnSnapshot:
    return CopilotTurnSnapshot.model_validate(
        _load_json(root, "reference_copilot_turn_snapshot.json")
    )


def test_reference_outputs_match_live_v59b_runner(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v59b_input_tree(tmp_path)

    handoff, restoration, reintegration = run_agentic_de_workspace_continuity_v59b(
        repo_root_path=temp_root,
        live_turn_snapshot=_load_snapshot(fixture_root),
    )

    assert handoff.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_workspace_continuity_restoration_handoff_record.json",
    )
    assert restoration.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_local_effect_restoration_record.json",
    )
    assert reintegration.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_workspace_continuity_restoration_reintegration_report.json",
    )


def test_v59b_outputs_remain_evidence_only_and_remove_selected_target(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v59b_input_tree(tmp_path)
    target_path = (
        temp_root
        / "artifacts"
        / "agentic_de"
        / "v59"
        / "workspace_continuity"
        / "runtime"
        / "reference_patch_candidate.diff"
    )

    handoff, restoration, reintegration = run_agentic_de_workspace_continuity_v59b(
        repo_root_path=temp_root,
        live_turn_snapshot=_load_snapshot(fixture_root),
    )

    assert handoff.target_arc == "vNext+162"
    assert handoff.target_path == "V59-B"
    assert handoff.restoration_time_continuation_verdict == "continued"
    assert (
        handoff.prior_governed_state_baseline_match_verdict == "matched"
    )
    assert restoration.target_arc == "vNext+162"
    assert restoration.target_path == "V59-B"
    assert restoration.restoration_outcome == "restoration_effect_observed"
    assert reintegration.continuity_restoration_reintegration_status == "reintegrated"
    assert (
        reintegration.continuity_restoration_reintegration_certificate_ref_or_equivalent
        is not None
    )
    assert not target_path.exists()


def test_v59b_baseline_content_mismatch_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v59b_input_tree(tmp_path)
    target_path = (
        temp_root
        / "artifacts"
        / "agentic_de"
        / "v59"
        / "workspace_continuity"
        / "runtime"
        / "reference_patch_candidate.diff"
    )
    target_path.write_text("drifted target content\n", encoding="utf-8")

    with pytest.raises(
        ValueError,
        match="requires current target state to match the shipped governed baseline",
    ):
        run_agentic_de_workspace_continuity_v59b(
            repo_root_path=temp_root,
            live_turn_snapshot=_load_snapshot(fixture_root),
        )


def test_v59b_capability_resnapshot_mismatch_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v59b_input_tree(tmp_path)
    payload = _load_json(fixture_root, "reference_copilot_turn_snapshot.json")
    assert isinstance(payload, dict)
    payload["profile_version"] = "profile.v2"

    with pytest.raises(
        ValueError,
        match="session capability snapshot must match the admitted V59-A continuation posture",
    ):
        run_agentic_de_workspace_continuity_v59b(
            repo_root_path=temp_root,
            live_turn_snapshot=CopilotTurnSnapshot.model_validate(payload),
        )


def test_v59b_can_residualize_when_no_restore_effect_is_materialized(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v59b_input_tree(tmp_path)
    target_path = (
        temp_root
        / "artifacts"
        / "agentic_de"
        / "v59"
        / "workspace_continuity"
        / "runtime"
        / "reference_patch_candidate.diff"
    )

    _handoff, restoration, reintegration = run_agentic_de_workspace_continuity_v59b(
        repo_root_path=temp_root,
        live_turn_snapshot=_load_snapshot(fixture_root),
        materialize_restoration_effect=False,
    )

    assert restoration.restoration_outcome == "no_restoration_effect_observed"
    assert reintegration.continuity_restoration_reintegration_status == "residualized"
    assert target_path.exists()
