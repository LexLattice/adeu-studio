from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import run_agentic_de_workspace_continuity_v59a
from adeu_ir.repo import repo_root
from urm_runtime import CopilotTurnSnapshot

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v59a"


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v59a_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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


def _load_snapshot(root: Path) -> CopilotTurnSnapshot:
    return CopilotTurnSnapshot.model_validate(
        _load_json(root, "reference_copilot_turn_snapshot.json")
    )


def test_reference_outputs_match_live_v59a_runner(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v59a_input_tree(tmp_path)

    (
        region,
        continuity_admission,
        occupancy,
        live_turn_admission,
        live_turn_handoff,
        observation,
        conformance,
        live_turn_reintegration,
        continuity_reintegration,
    ) = run_agentic_de_workspace_continuity_v59a(
        repo_root_path=temp_root,
        live_turn_snapshot=_load_snapshot(fixture_root),
    )

    assert region.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_workspace_continuity_region_declaration.json",
    )
    assert continuity_admission.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_workspace_continuity_admission_record.json",
    )
    assert occupancy.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_workspace_occupancy_report.json",
    )
    assert live_turn_admission.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_live_turn_admission_record.json",
    )
    assert live_turn_handoff.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_live_turn_handoff_record.json",
    )
    assert observation.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_local_effect_observation_record.json",
    )
    assert conformance.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_local_effect_conformance_report.json",
    )
    assert live_turn_reintegration.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_live_turn_reintegration_report.json",
    )
    assert continuity_reintegration.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_workspace_continuity_reintegration_report.json",
    )


def test_v59a_outputs_remain_evidence_only_and_unoccupied_target_bound(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v59a_input_tree(tmp_path)

    (
        region,
        continuity_admission,
        occupancy,
        live_turn_admission,
        live_turn_handoff,
        observation,
        conformance,
        live_turn_reintegration,
        continuity_reintegration,
    ) = run_agentic_de_workspace_continuity_v59a(
        repo_root_path=temp_root,
        live_turn_snapshot=_load_snapshot(fixture_root),
    )

    assert region.target_arc == "vNext+161"
    assert region.target_path == "V59-A"
    assert continuity_admission.continuity_verdict == "admitted"
    assert occupancy.occupancy_verdict == "unoccupied"
    assert occupancy.prior_governed_lineage_ref is None
    assert live_turn_admission.designated_sandbox_root == (
        "artifacts/agentic_de/v59/workspace_continuity"
    )
    assert live_turn_handoff.target_path == "V59-A"
    assert observation.designated_sandbox_root == (
        "artifacts/agentic_de/v59/workspace_continuity"
    )
    assert conformance.target_arc == "vNext+161"
    assert live_turn_reintegration.reintegration_status == "reintegrated"
    assert continuity_reintegration.continuity_reintegration_status == "reintegrated"
    assert (
        continuity_reintegration.continuity_witness_certificate_ref_or_equivalent
        is not None
    )


def test_non_admitted_live_turn_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v59a_input_tree(tmp_path)
    payload = _load_json(fixture_root, "reference_copilot_turn_snapshot.json")
    assert isinstance(payload, dict)
    payload["writes_allowed"] = False

    with pytest.raises(ValueError, match="live-turn admission must resolve to admitted"):
        run_agentic_de_workspace_continuity_v59a(
            repo_root_path=temp_root,
            live_turn_snapshot=CopilotTurnSnapshot.model_validate(payload),
        )


def test_occupied_target_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v59a_input_tree(tmp_path)
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

    with pytest.raises(ValueError, match="requires unoccupied target"):
        run_agentic_de_workspace_continuity_v59a(
            repo_root_path=temp_root,
            live_turn_snapshot=_load_snapshot(fixture_root),
        )


def test_non_target_occupants_remain_contextual_only(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v59a_input_tree(tmp_path)
    context_path = (
        temp_root
        / "artifacts"
        / "agentic_de"
        / "v59"
        / "workspace_continuity"
        / "runtime"
        / "context_only.txt"
    )
    context_path.parent.mkdir(parents=True, exist_ok=True)
    context_path.write_text("context only\n", encoding="utf-8")

    (
        _region,
        _continuity_admission,
        occupancy,
        _live_turn_admission,
        _live_turn_handoff,
        _observation,
        _conformance,
        _live_turn_reintegration,
        continuity_reintegration,
    ) = run_agentic_de_workspace_continuity_v59a(
        repo_root_path=temp_root,
        live_turn_snapshot=_load_snapshot(fixture_root),
    )

    assert occupancy.occupancy_verdict == "unoccupied"
    assert "contextual only" in occupancy.drift_posture_summary
    assert continuity_reintegration.continuity_reintegration_status == "reintegrated"


def test_missing_required_v59a_lane_drift_assumption_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v59a_input_tree(tmp_path)
    lane_drift_path = fixture_root / "reference_agentic_de_lane_drift_record.json"
    payload = _load_json(fixture_root, "reference_agentic_de_lane_drift_record.json")
    assert isinstance(payload, dict)
    entries = payload["entries"]
    assert isinstance(entries, list)
    payload["entries"] = entries[:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    lane_drift_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="required handoff posture"):
        run_agentic_de_workspace_continuity_v59a(
            repo_root_path=temp_root,
            live_turn_snapshot=_load_snapshot(fixture_root),
        )
