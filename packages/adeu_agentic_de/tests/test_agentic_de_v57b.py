from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import (
    AgenticDeLocalEffectRestorationRecord,
    run_agentic_de_local_effect_v57b,
)
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v57b"


def _load_json(name: str) -> object:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v57b_input_tree(tmp_path: Path) -> Path:
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
        "artifacts/agent_harness/v152/evidence_inputs/v56a_agentic_de_interaction_governance_starter_evidence_v152.json",
        "artifacts/agent_harness/v153/evidence_inputs/v56b_bounded_live_gate_starter_evidence_v153.json",
        "artifacts/agent_harness/v154/evidence_inputs/v56c_harvest_calibration_migration_evidence_v154.json",
        "artifacts/agent_harness/v155/evidence_inputs/v57a_local_effect_observation_evidence_v155.json",
        "artifacts/agentic_de/v57/local_effect/.gitignore",
    ]
    for relative_path in relative_paths:
        source = repo_root_path / relative_path
        target = tmp_path / relative_path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    return tmp_path


def test_reference_outputs_match_live_v57b_runner(tmp_path: Path) -> None:
    temp_root = _copy_v57b_input_tree(tmp_path)

    restoration = run_agentic_de_local_effect_v57b(repo_root_path=temp_root)

    assert restoration.model_dump(mode="json") == _load_json(
        "reference_agentic_de_local_effect_restoration_record.json"
    )


def test_v57b_output_remains_evidence_only_and_lineage_bound(tmp_path: Path) -> None:
    temp_root = _copy_v57b_input_tree(tmp_path)

    restoration = run_agentic_de_local_effect_v57b(repo_root_path=temp_root)

    assert restoration.target_arc == "vNext+156"
    assert restoration.target_path == "V57-B"
    assert restoration.evidence_only is True
    assert restoration.changes_live_behavior_by_default is False
    assert restoration.selected_live_action_class == "local_write"
    assert (
        restoration.selected_restoration_exemplar
        == "compensating_restore_of_v57a_create_new_artifact_only"
    )
    assert (
        restoration.restoration_entitlement_mode
        == "lineage_bound_evidence_bound_bounded_compensating_scope_derivation_only"
    )
    assert restoration.restoration_outcome == "restoration_effect_observed"
    assert restoration.restoration_boundedness_verdict == "bounded"


def test_append_only_restoration_remains_out_of_scope(tmp_path: Path) -> None:
    temp_root = _copy_v57b_input_tree(tmp_path)
    observation_path = (
        temp_root
        / "packages"
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v57a"
        / "reference_agentic_de_local_effect_observation_record.json"
    )
    payload = json.loads(observation_path.read_text(encoding="utf-8"))
    payload["selected_local_write_kind"] = "append_only"
    payload["observed_write_set"][0]["write_kind"] = "append_only"
    payload["observation_id"] = None
    observation_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="create_new"):
        run_agentic_de_local_effect_v57b(
            repo_root_path=temp_root,
            v57a_observation_path=observation_path,
        )


def test_missing_required_v57b_lane_drift_assumption_fails_closed(tmp_path: Path) -> None:
    temp_root = _copy_v57b_input_tree(tmp_path)
    lane_drift_path = (
        temp_root
        / "packages"
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v57b"
        / "reference_agentic_de_lane_drift_record.json"
    )
    payload = json.loads(lane_drift_path.read_text(encoding="utf-8"))
    payload["entries"] = payload["entries"][:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    lane_drift_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="required handoff posture"):
        run_agentic_de_local_effect_v57b(repo_root_path=temp_root)


def test_lineage_bound_content_match_required(tmp_path: Path) -> None:
    temp_root = _copy_v57b_input_tree(tmp_path)

    with pytest.raises(ValueError, match="bounded compensating scope match"):
        run_agentic_de_local_effect_v57b(
            repo_root_path=temp_root,
            materialized_observed_content_text="drifted content\n",
        )


def test_v57a_conformance_ticket_lineage_mismatch_fails_closed(tmp_path: Path) -> None:
    temp_root = _copy_v57b_input_tree(tmp_path)
    conformance_path = (
        temp_root
        / "packages"
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v57a"
        / "reference_agentic_de_local_effect_conformance_report.json"
    )
    payload = json.loads(conformance_path.read_text(encoding="utf-8"))
    payload["ticket_ref"] = "agentic_de_action_ticket_wrong"
    payload["report_id"] = None
    conformance_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="does not bind the provided action ticket"):
        run_agentic_de_local_effect_v57b(
            repo_root_path=temp_root,
            v57a_local_effect_conformance_path=conformance_path,
        )


def test_expected_restoration_write_set_must_match_exactly(tmp_path: Path) -> None:
    temp_root = _copy_v57b_input_tree(tmp_path)

    restoration = run_agentic_de_local_effect_v57b(
        repo_root_path=temp_root,
        expected_relative_paths=(
            "artifacts/agentic_de/v57/local_effect/runtime/reference_patch_candidate.diff",
            "artifacts/agentic_de/v57/local_effect/runtime/second_expected.diff",
        ),
    )

    assert restoration.restoration_outcome == "restoration_mismatched_effect_observed"
    assert restoration.restoration_boundedness_verdict == "bounded"


def test_restoration_target_outside_expected_scope_is_explicit(tmp_path: Path) -> None:
    temp_root = _copy_v57b_input_tree(tmp_path)

    restoration = run_agentic_de_local_effect_v57b(
        repo_root_path=temp_root,
        expected_relative_paths=(
            "artifacts/agentic_de/v57/local_effect/runtime/not_the_reference.diff",
        ),
    )

    assert restoration.restoration_outcome == "restoration_out_of_scope_write_observed"
    assert restoration.restoration_boundedness_verdict == "failed"


def test_symlink_component_between_repo_root_and_sandbox_fails_closed(tmp_path: Path) -> None:
    temp_root = _copy_v57b_input_tree(tmp_path)
    agentic_de_root = temp_root / "artifacts" / "agentic_de"
    outside_root = temp_root / "outside_agentic_de"
    shutil.rmtree(agentic_de_root)
    outside_root.mkdir(parents=True)
    agentic_de_root.symlink_to(outside_root, target_is_directory=True)

    with pytest.raises(ValueError, match="forbids symlink components from the repository root"):
        run_agentic_de_local_effect_v57b(repo_root_path=temp_root)


def test_negative_restoration_outcomes_remain_explicit_vocab() -> None:
    payload = _load_json("reference_agentic_de_local_effect_restoration_record.json")
    assert isinstance(payload, dict)
    base_entry = payload["restoration_observed_write_set"][0]
    assert isinstance(base_entry, dict)

    cases = [
        ("restoration_mismatched_effect_observed", "bounded", [base_entry]),
        ("restoration_out_of_scope_write_observed", "failed", [base_entry]),
        ("restoration_boundedness_verdict_failed", "failed", [base_entry]),
    ]
    for outcome, verdict, observed_write_set in cases:
        candidate = {
            **payload,
            "restoration_id": None,
            "restoration_outcome": outcome,
            "restoration_boundedness_verdict": verdict,
            "restoration_observed_write_set": observed_write_set,
        }
        record = AgenticDeLocalEffectRestorationRecord.model_validate(candidate)
        assert record.restoration_outcome == outcome
