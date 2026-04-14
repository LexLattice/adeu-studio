from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import (
    AgenticDeLocalEffectHardeningEntry,
    run_agentic_de_local_effect_v57c,
)
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v57c"


def _load_json(name: str) -> object:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v57c_input_tree(tmp_path: Path) -> Path:
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
        "artifacts/agent_harness/v152/evidence_inputs/v56a_agentic_de_interaction_governance_starter_evidence_v152.json",
        "artifacts/agent_harness/v153/evidence_inputs/v56b_bounded_live_gate_starter_evidence_v153.json",
        "artifacts/agent_harness/v154/evidence_inputs/v56c_harvest_calibration_migration_evidence_v154.json",
        "artifacts/agent_harness/v155/evidence_inputs/v57a_local_effect_observation_evidence_v155.json",
        "artifacts/agent_harness/v156/evidence_inputs/v57b_local_effect_restoration_evidence_v156.json",
    ]
    for relative_path in relative_paths:
        source = repo_root_path / relative_path
        target = tmp_path / relative_path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    return tmp_path


def test_reference_outputs_match_live_v57c_runner(tmp_path: Path) -> None:
    temp_root = _copy_v57c_input_tree(tmp_path)

    register = run_agentic_de_local_effect_v57c(repo_root_path=temp_root)

    assert register.model_dump(mode="json") == _load_json(
        "reference_agentic_de_local_effect_hardening_register.json"
    )


def test_v57c_output_remains_advisory_only_and_path_level(tmp_path: Path) -> None:
    temp_root = _copy_v57c_input_tree(tmp_path)

    register = run_agentic_de_local_effect_v57c(repo_root_path=temp_root)

    assert register.target_arc == "vNext+157"
    assert register.target_path == "V57-C"
    assert register.advisory_only is True
    assert register.candidate_only is True
    assert register.path_level_only is True
    assert register.exemplar_evidence_non_generalizing_by_default is True
    assert register.changes_live_behavior_by_default is False
    assert register.entry_count == 1
    entry = register.entries[0]
    assert (
        entry.selected_hardening_target_surface
        == "observed_and_restored_v57a_create_new_exemplar_only"
    )
    assert entry.recommended_outcome == "candidate_for_later_local_hardening"
    assert entry.observation_boundedness_verdict == "bounded"
    assert entry.restoration_boundedness_verdict == "bounded"
    assert "later_lock_required_for_scope" in entry.reason_codes


def test_missing_required_v57c_lane_drift_assumption_fails_closed(tmp_path: Path) -> None:
    temp_root = _copy_v57c_input_tree(tmp_path)
    lane_drift_path = (
        temp_root
        / "packages"
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v57c"
        / "reference_agentic_de_lane_drift_record.json"
    )
    payload = json.loads(lane_drift_path.read_text(encoding="utf-8"))
    payload["entries"] = payload["entries"][:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    lane_drift_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="required handoff posture"):
        run_agentic_de_local_effect_v57c(repo_root_path=temp_root)


def test_non_bounded_restoration_verdict_fails_closed(tmp_path: Path) -> None:
    temp_root = _copy_v57c_input_tree(tmp_path)
    restoration_path = (
        temp_root
        / "packages"
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v57b"
        / "reference_agentic_de_local_effect_restoration_record.json"
    )
    payload = json.loads(restoration_path.read_text(encoding="utf-8"))
    payload["restoration_outcome"] = "restoration_boundedness_verdict_failed"
    payload["restoration_boundedness_verdict"] = "failed"
    payload["restoration_id"] = None
    restoration_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="prior bounded restoration verdict"):
        run_agentic_de_local_effect_v57c(repo_root_path=temp_root)


def test_v57b_evidence_must_preserve_shipped_restoration_exemplar(tmp_path: Path) -> None:
    temp_root = _copy_v57c_input_tree(tmp_path)
    evidence_path = (
        temp_root
        / "artifacts"
        / "agent_harness"
        / "v156"
        / "evidence_inputs"
        / "v57b_local_effect_restoration_evidence_v156.json"
    )
    payload = json.loads(evidence_path.read_text(encoding="utf-8"))
    payload["selected_restoration_exemplar_for_v57b"] = "broader_restore_family"
    evidence_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="shipped restoration exemplar"):
        run_agentic_de_local_effect_v57c(repo_root_path=temp_root)


def test_candidate_outcome_requires_later_lock_reason_code() -> None:
    payload = _load_json("reference_agentic_de_local_effect_hardening_register.json")
    assert isinstance(payload, dict)
    entry = payload["entries"][0]
    assert isinstance(entry, dict)

    with pytest.raises(ValueError, match="later_lock_required_for_scope"):
        AgenticDeLocalEffectHardeningEntry.model_validate(
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
