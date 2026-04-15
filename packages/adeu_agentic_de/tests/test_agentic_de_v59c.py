from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import (
    AgenticDeWorkspaceContinuityHardeningEntry,
    run_agentic_de_workspace_continuity_v59c,
)
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v59c"


def _load_json(name: str) -> object:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v59c_input_tree(tmp_path: Path) -> Path:
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


def test_reference_outputs_match_live_v59c_runner(tmp_path: Path) -> None:
    temp_root = _copy_v59c_input_tree(tmp_path)

    register = run_agentic_de_workspace_continuity_v59c(repo_root_path=temp_root)

    assert register.model_dump(mode="json") == _load_json(
        "reference_agentic_de_workspace_continuity_hardening_register.json"
    )


def test_v59c_output_remains_advisory_only_path_level_and_policy_anchored(
    tmp_path: Path,
) -> None:
    temp_root = _copy_v59c_input_tree(tmp_path)

    register = run_agentic_de_workspace_continuity_v59c(repo_root_path=temp_root)

    assert register.target_arc == "vNext+163"
    assert register.target_path == "V59-C"
    assert register.advisory_only is True
    assert register.candidate_only is True
    assert register.path_level_only is True
    assert register.exemplar_evidence_non_generalizing_by_default is True
    assert register.changes_live_behavior_by_default is False
    assert register.recommendation_function_extensional_and_replayable is True
    assert register.explicit_frozen_policy_anchor_required is True
    assert register.lineage_root_non_independence_dedup_applied is True
    entry = register.entries[0]
    assert (
        entry.selected_hardening_target_surface
        == "observed_and_restored_continuity_bound_create_new_exemplar_only"
    )
    assert (
        entry.frozen_policy_ref
        == "docs/LOCKED_CONTINUATION_vNEXT_PLUS163.md#machine-checkable-contract"
    )
    assert entry.recommended_outcome == "candidate_for_later_continuity_hardening"
    assert entry.continuity_reintegration_status == "reintegrated"
    assert entry.continuity_restoration_reintegration_status == "reintegrated"
    assert entry.prior_governed_state_baseline_match_verdict == "matched"
    assert entry.bounded_compensating_scope_match_verdict == "matched"
    assert len(entry.root_origin_ids) == len(set(entry.root_origin_ids))
    assert "non-independent escalation support" in entry.root_origin_dedup_summary


def test_v59c_recommendation_is_replayable_for_same_inputs(tmp_path: Path) -> None:
    temp_root = _copy_v59c_input_tree(tmp_path)

    first = run_agentic_de_workspace_continuity_v59c(repo_root_path=temp_root)
    second = run_agentic_de_workspace_continuity_v59c(repo_root_path=temp_root)

    assert first.model_dump(mode="json") == second.model_dump(mode="json")


def test_missing_required_v59c_lane_drift_assumption_fails_closed(tmp_path: Path) -> None:
    temp_root = _copy_v59c_input_tree(tmp_path)
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

    with pytest.raises(ValueError, match="V59-C lane drift record does not satisfy"):
        run_agentic_de_workspace_continuity_v59c(
            repo_root_path=temp_root,
            lane_drift_path=lane_drift_path,
        )


def test_invalid_v59b_evidence_fails_closed(tmp_path: Path) -> None:
    temp_root = _copy_v59c_input_tree(tmp_path)
    evidence_path = (
        temp_root
        / "artifacts"
        / "agent_harness"
        / "v162"
        / "evidence_inputs"
        / "v59b_workspace_continuity_restoration_evidence_v162.json"
    )
    payload = json.loads(evidence_path.read_text(encoding="utf-8"))
    payload["restoration_time_continuation_verdict_typed_witness_bearing_replayable"] = False
    evidence_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="restoration_time_continuation_verdict_typed"):
        run_agentic_de_workspace_continuity_v59c(repo_root_path=temp_root)


def test_candidate_outcome_requires_later_lock_reason_code() -> None:
    payload = _load_json("reference_agentic_de_workspace_continuity_hardening_register.json")
    assert isinstance(payload, dict)
    entry = payload["entries"][0]
    assert isinstance(entry, dict)

    with pytest.raises(ValueError, match="later_lock_required_for_scope"):
        AgenticDeWorkspaceContinuityHardeningEntry.model_validate(
            {
                **entry,
                "hardening_id": None,
                "reason_codes": [
                    code
                    for code in entry["reason_codes"]
                    if code != "later_lock_required_for_scope"
                ],
            }
        )
