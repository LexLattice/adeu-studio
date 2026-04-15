from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import (
    AgenticDeLiveHarnessHardeningEntry,
    run_agentic_de_live_harness_v58c,
)
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v58c"


def _load_json(name: str) -> object:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v58c_input_tree(tmp_path: Path) -> Path:
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
        "packages/adeu_agentic_de/tests/fixtures/v58b/reference_agentic_de_live_restoration_handoff_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v58b/reference_agentic_de_live_restoration_reintegration_report.json",
        "packages/adeu_agentic_de/tests/fixtures/v58c/reference_agentic_de_lane_drift_record.json",
        "artifacts/agent_harness/v152/evidence_inputs/v56a_agentic_de_interaction_governance_starter_evidence_v152.json",
        "artifacts/agent_harness/v153/evidence_inputs/v56b_bounded_live_gate_starter_evidence_v153.json",
        "artifacts/agent_harness/v154/evidence_inputs/v56c_harvest_calibration_migration_evidence_v154.json",
        "artifacts/agent_harness/v155/evidence_inputs/v57a_local_effect_observation_evidence_v155.json",
        "artifacts/agent_harness/v156/evidence_inputs/v57b_local_effect_restoration_evidence_v156.json",
        "artifacts/agent_harness/v157/evidence_inputs/v57c_local_effect_hardening_evidence_v157.json",
        "artifacts/agent_harness/v158/evidence_inputs/v58a_live_harness_bind_evidence_v158.json",
        "artifacts/agent_harness/v159/evidence_inputs/v58b_live_restoration_state_evidence_v159.json",
    ]
    for relative_path in relative_paths:
        source = repo_root_path / relative_path
        target = tmp_path / relative_path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    return tmp_path


def test_reference_outputs_match_live_v58c_runner(tmp_path: Path) -> None:
    temp_root = _copy_v58c_input_tree(tmp_path)

    register = run_agentic_de_live_harness_v58c(repo_root_path=temp_root)

    assert register.model_dump(mode="json") == _load_json(
        "reference_agentic_de_live_harness_hardening_register.json"
    )


def test_v58c_output_remains_advisory_only_and_path_level(tmp_path: Path) -> None:
    temp_root = _copy_v58c_input_tree(tmp_path)

    register = run_agentic_de_live_harness_v58c(repo_root_path=temp_root)

    assert register.target_arc == "vNext+160"
    assert register.target_path == "V58-C"
    assert register.advisory_only is True
    assert register.candidate_only is True
    assert register.path_level_only is True
    assert register.exemplar_evidence_non_generalizing_by_default is True
    assert register.changes_live_behavior_by_default is False
    assert register.recommendation_function_extensional_and_replayable is True
    assert register.lineage_root_non_independence_dedup_applied is True
    entry = register.entries[0]
    assert (
        entry.selected_hardening_target_surface
        == "observed_and_restored_live_harness_create_new_exemplar_only"
    )
    assert entry.recommended_outcome == "candidate_for_later_harness_hardening"
    assert entry.turn_reintegration_status == "reintegrated"
    assert entry.restoration_reintegration_status == "reintegrated"
    assert len(entry.root_origin_ids) == len(set(entry.root_origin_ids))
    assert "repeated lineage artifacts remain non-independent escalation support" in (
        entry.root_origin_dedup_summary
    )


def test_v58c_recommendation_is_replayable_for_same_inputs(tmp_path: Path) -> None:
    temp_root = _copy_v58c_input_tree(tmp_path)

    first = run_agentic_de_live_harness_v58c(repo_root_path=temp_root)
    second = run_agentic_de_live_harness_v58c(repo_root_path=temp_root)

    assert first.model_dump(mode="json") == second.model_dump(mode="json")


def test_missing_required_v58c_lane_drift_assumption_fails_closed(tmp_path: Path) -> None:
    temp_root = _copy_v58c_input_tree(tmp_path)
    lane_drift_path = (
        temp_root
        / "packages"
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v58c"
        / "reference_agentic_de_lane_drift_record.json"
    )
    payload = json.loads(lane_drift_path.read_text(encoding="utf-8"))
    payload["entries"] = payload["entries"][:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    lane_drift_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="V58-C lane drift record does not satisfy"):
        run_agentic_de_live_harness_v58c(
            repo_root_path=temp_root,
            v58c_lane_drift_path=lane_drift_path,
        )


def test_invalid_v58b_evidence_fails_closed(tmp_path: Path) -> None:
    temp_root = _copy_v58c_input_tree(tmp_path)
    evidence_path = (
        temp_root
        / "artifacts"
        / "agent_harness"
        / "v159"
        / "evidence_inputs"
        / "v58b_live_restoration_state_evidence_v159.json"
    )
    payload = json.loads(evidence_path.read_text(encoding="utf-8"))
    payload["selected_restoration_surface_for_v58b"] = "broader_restore_family"
    evidence_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="shipped restoration surface"):
        run_agentic_de_live_harness_v58c(repo_root_path=temp_root)


def test_non_reintegrated_v58b_reintegration_fails_closed(tmp_path: Path) -> None:
    temp_root = _copy_v58c_input_tree(tmp_path)
    reintegration_path = (
        temp_root
        / "packages"
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v58b"
        / "reference_agentic_de_live_restoration_reintegration_report.json"
    )
    payload = json.loads(reintegration_path.read_text(encoding="utf-8"))
    payload["restoration_reintegration_status"] = "blocked"
    payload["reason_codes"] = ["restoration_witness_missing"]
    payload["restoration_reintegration_certificate_ref_or_equivalent"] = None
    payload["report_id"] = None
    reintegration_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="reintegrated V58-B restoration posture"):
        run_agentic_de_live_harness_v58c(repo_root_path=temp_root)


def test_candidate_outcome_requires_later_lock_reason_code() -> None:
    payload = _load_json("reference_agentic_de_live_harness_hardening_register.json")
    assert isinstance(payload, dict)
    entry = payload["entries"][0]
    assert isinstance(entry, dict)

    with pytest.raises(ValueError, match="later_lock_required_for_scope"):
        AgenticDeLiveHarnessHardeningEntry.model_validate(
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
