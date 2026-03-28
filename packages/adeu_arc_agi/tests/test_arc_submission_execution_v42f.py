from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_arc_agi import (
    ADEU_ARC_SUBMISSION_EXECUTION_RECORD_SCHEMA,
    AdeuArcSubmissionExecutionRecord,
    compute_adeu_arc_submission_execution_id,
    derive_v42f_arc_submission_execution_record,
)
from adeu_arc_solver import derive_v42f_submission_execution_record
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v89_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus89"


def _v90_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus90"


def _v91_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus91"


def _v92_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus92"


def _v93_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus93"


def _v94_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus94"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v89(name: str) -> dict[str, Any]:
    return _load_json(_v89_root() / name)


def _load_v90(name: str) -> dict[str, Any]:
    return _load_json(_v90_root() / name)


def _load_v91(name: str) -> dict[str, Any]:
    return _load_json(_v91_root() / name)


def _load_v92(name: str) -> dict[str, Any]:
    return _load_json(_v92_root() / name)


def _load_v93(name: str) -> dict[str, Any]:
    return _load_json(_v93_root() / name)


def _load_v94(name: str) -> dict[str, Any]:
    return _load_json(_v94_root() / name)


def _submission_schema_validator() -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_arc_agi"
            / "schema"
            / "adeu_arc_submission_execution_record.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v94_reference_fixture_replays_and_validates() -> None:
    task_packet = _load_v89("adeu_arc_task_packet_v89_reference.json")
    observation = _load_v90("adeu_arc_observation_frame_v90_reference.json")
    hypothesis = _load_v90("adeu_arc_hypothesis_frame_v90_reference.json")
    action = _load_v91("adeu_arc_action_proposal_v91_reference.json")
    rollout = _load_v91("adeu_arc_rollout_trace_v91_reference.json")
    local_eval = _load_v92("adeu_arc_local_eval_record_v92_reference.json")
    scorecard = _load_v93("adeu_arc_scorecard_manifest_v93_case_official_imported.json")
    submission = _load_v94("adeu_arc_submission_execution_record_v94_reference.json")

    validated = AdeuArcSubmissionExecutionRecord.model_validate(submission)
    assert validated.schema == ADEU_ARC_SUBMISSION_EXECUTION_RECORD_SCHEMA
    assert validated.task_packet_id == task_packet["task_packet_id"]
    assert validated.observation_frame_id == observation["observation_frame_id"]
    assert validated.hypothesis_frame_id == hypothesis["hypothesis_frame_id"]
    assert validated.action_proposal_id == action["action_proposal_id"]
    assert validated.rollout_trace_id == rollout["rollout_trace_id"]
    assert validated.local_eval_record_id == local_eval["local_eval_record_id"]
    assert validated.scorecard_manifest_id == scorecard["scorecard_manifest_id"]

    derived = derive_v42f_arc_submission_execution_record(
        task_packet=task_packet,
        task_packet_ref=submission["task_packet_ref"],
        observation_frame=observation,
        observation_frame_ref=submission["observation_frame_ref"],
        hypothesis_frame=hypothesis,
        hypothesis_frame_ref=submission["hypothesis_frame_ref"],
        action_proposal=action,
        action_proposal_ref=submission["action_proposal_ref"],
        rollout_trace=rollout,
        rollout_trace_ref=submission["rollout_trace_ref"],
        local_eval_record=local_eval,
        local_eval_record_ref=submission["local_eval_record_ref"],
        scorecard_manifest=scorecard,
        scorecard_manifest_ref=submission["scorecard_manifest_ref"],
        environment_ref=submission["environment_ref"],
        session_ref=submission["session_ref"],
        competition_scope_ref=submission["competition_scope_ref"],
        model_id=submission["model_id"],
        run_id=submission["run_id"],
        submission_authorization_status=submission["submission_authorization_status"],
        submission_authorization_source_kind=submission["submission_authorization_source_kind"],
        submission_authorization_validity=submission["submission_authorization_validity"],
        submission_authorization_basis_refs=submission["submission_authorization_basis_refs"],
        submission_execution_status=submission["submission_execution_status"],
        submission_transport_profile=submission["submission_transport_profile"],
        external_request_ref=submission["external_request_ref"],
        submission_payload_ref=submission["submission_payload_ref"],
        submission_payload_hash=submission["submission_payload_hash"],
        submission_request_ts=submission["submission_request_ts"],
        submission_receipt_ref=submission["submission_receipt_ref"],
        submission_receipt_hash=submission["submission_receipt_hash"],
        submission_receipt_ts=submission["submission_receipt_ts"],
        result_import_status=submission["result_import_status"],
        result_source_kind=submission["result_source_kind"],
        result_authority_validity=submission["result_authority_validity"],
        result_authority_basis_refs=submission["result_authority_basis_refs"],
        result_import_ref=submission["result_import_ref"],
        result_import_hash=submission["result_import_hash"],
        result_import_ts=submission["result_import_ts"],
        lifecycle_transition_matrix_ref=submission["lifecycle_transition_matrix_ref"],
        submission_result_posture=submission["submission_result_posture"],
        submission_result_summary=submission["submission_result_summary"],
        bounded_orchestration_constraint_register=submission[
            "bounded_orchestration_constraint_register"
        ],
        settlement_posture_carry=submission["settlement_posture_carry"],
        deferred_authority_assertions=submission["deferred_authority_assertions"],
        evidence_refs=submission["evidence_refs"],
    )
    assert derived == submission


def test_v94_solver_helper_replays_reference_fixture() -> None:
    task_packet = _load_v89("adeu_arc_task_packet_v89_reference.json")
    observation = _load_v90("adeu_arc_observation_frame_v90_reference.json")
    hypothesis = _load_v90("adeu_arc_hypothesis_frame_v90_reference.json")
    action = _load_v91("adeu_arc_action_proposal_v91_reference.json")
    rollout = _load_v91("adeu_arc_rollout_trace_v91_reference.json")
    local_eval = _load_v92("adeu_arc_local_eval_record_v92_reference.json")
    scorecard = _load_v93("adeu_arc_scorecard_manifest_v93_case_official_imported.json")
    submission = _load_v94("adeu_arc_submission_execution_record_v94_reference.json")

    derived = derive_v42f_submission_execution_record(
        task_packet=task_packet,
        task_packet_ref=submission["task_packet_ref"],
        observation_frame=observation,
        observation_frame_ref=submission["observation_frame_ref"],
        hypothesis_frame=hypothesis,
        hypothesis_frame_ref=submission["hypothesis_frame_ref"],
        action_proposal=action,
        action_proposal_ref=submission["action_proposal_ref"],
        rollout_trace=rollout,
        rollout_trace_ref=submission["rollout_trace_ref"],
        local_eval_record=local_eval,
        local_eval_record_ref=submission["local_eval_record_ref"],
        scorecard_manifest=scorecard,
        scorecard_manifest_ref=submission["scorecard_manifest_ref"],
        environment_ref=submission["environment_ref"],
        session_ref=submission["session_ref"],
        competition_scope_ref=submission["competition_scope_ref"],
        model_id=submission["model_id"],
        run_id=submission["run_id"],
        submission_authorization_status=submission["submission_authorization_status"],
        submission_authorization_source_kind=submission["submission_authorization_source_kind"],
        submission_authorization_validity=submission["submission_authorization_validity"],
        submission_authorization_basis_refs=submission["submission_authorization_basis_refs"],
        submission_execution_status=submission["submission_execution_status"],
        submission_transport_profile=submission["submission_transport_profile"],
        external_request_ref=submission["external_request_ref"],
        submission_payload_ref=submission["submission_payload_ref"],
        submission_payload_hash=submission["submission_payload_hash"],
        submission_request_ts=submission["submission_request_ts"],
        submission_receipt_ref=submission["submission_receipt_ref"],
        submission_receipt_hash=submission["submission_receipt_hash"],
        submission_receipt_ts=submission["submission_receipt_ts"],
        result_import_status=submission["result_import_status"],
        result_source_kind=submission["result_source_kind"],
        result_authority_validity=submission["result_authority_validity"],
        result_authority_basis_refs=submission["result_authority_basis_refs"],
        result_import_ref=submission["result_import_ref"],
        result_import_hash=submission["result_import_hash"],
        result_import_ts=submission["result_import_ts"],
        lifecycle_transition_matrix_ref=submission["lifecycle_transition_matrix_ref"],
        submission_result_posture=submission["submission_result_posture"],
        submission_result_summary=submission["submission_result_summary"],
        bounded_orchestration_constraint_register=submission[
            "bounded_orchestration_constraint_register"
        ],
        settlement_posture_carry=submission["settlement_posture_carry"],
        deferred_authority_assertions=submission["deferred_authority_assertions"],
        evidence_refs=submission["evidence_refs"],
    )
    assert derived == submission


def test_v94_id_is_deterministic() -> None:
    payload = _load_v94("adeu_arc_submission_execution_record_v94_reference.json")
    without_id = deepcopy(payload)
    without_id.pop("submission_execution_id")
    assert (
        compute_adeu_arc_submission_execution_id(without_id)
        == payload["submission_execution_id"]
    )


def test_v94_exported_schema_accepts_reference_fixture() -> None:
    _submission_schema_validator().validate(
        _load_v94("adeu_arc_submission_execution_record_v94_reference.json")
    )


def test_v94_accepts_three_lifecycle_authority_cases() -> None:
    fixture_names = [
        "adeu_arc_submission_execution_record_v94_case_authorized_not_submitted.json",
        "adeu_arc_submission_execution_record_v94_case_submitted_acknowledged_no_official_result_import.json",
        "adeu_arc_submission_execution_record_v94_reference.json",
    ]
    seen: set[tuple[str, str, str]] = set()
    for fixture_name in fixture_names:
        payload = _load_v94(fixture_name)
        validated = AdeuArcSubmissionExecutionRecord.model_validate(payload)
        seen.add(
            (
                validated.submission_authorization_status,
                validated.submission_execution_status,
                validated.result_import_status,
            )
        )
    assert seen == {
        ("authorized", "not_submitted", "not_imported"),
        ("authorized", "submitted_acknowledged", "deferred"),
        ("authorized", "submitted_acknowledged", "official_imported"),
    }


def test_v94_rejects_local_shadow_authority_laundering_fixture() -> None:
    payload = _load_v94(
        "adeu_arc_submission_execution_record_v94_reject_local_shadow_authority_laundering.json"
    )
    with pytest.raises(ValidationError, match="authorized submission requires"):
        AdeuArcSubmissionExecutionRecord.model_validate(payload)


def test_v94_rejects_missing_payload_lineage_hash_binding_fixture() -> None:
    payload = _load_v94(
        "adeu_arc_submission_execution_record_v94_reject_missing_payload_lineage_hash_binding.json"
    )
    with pytest.raises(ValidationError, match="submission_payload_hash must not be empty"):
        AdeuArcSubmissionExecutionRecord.model_validate(payload)


def test_v94_rejects_submitted_acknowledged_missing_receipt_binding_fixture() -> None:
    payload = _load_v94(
        "adeu_arc_submission_execution_record_v94_reject_submitted_acknowledged_missing_receipt_binding.json"
    )
    with pytest.raises(ValidationError, match="submitted_acknowledged status requires receipt"):
        AdeuArcSubmissionExecutionRecord.model_validate(payload)


def test_v94_rejects_contradictory_lifecycle_stage_combination_fixture() -> None:
    payload = _load_v94(
        "adeu_arc_submission_execution_record_v94_reject_contradictory_lifecycle_stages.json"
    )
    with pytest.raises(ValidationError, match="result_import_status violates"):
        AdeuArcSubmissionExecutionRecord.model_validate(payload)


def test_v94_rejects_official_result_import_without_authority_fixture() -> None:
    payload = _load_v94(
        "adeu_arc_submission_execution_record_v94_reject_official_result_import_without_authority_binding.json"
    )
    with pytest.raises(ValidationError, match="official result import requires"):
        AdeuArcSubmissionExecutionRecord.model_validate(payload)


def test_v94_rejects_request_receipt_result_cross_chain_identity_mismatch_fixture() -> None:
    payload = _load_v94(
        "adeu_arc_submission_execution_record_v94_reject_request_receipt_result_identity_chain_mismatch.json"
    )
    with pytest.raises(ValidationError, match="same request/environment/session/competition"):
        AdeuArcSubmissionExecutionRecord.model_validate(payload)


def test_v94_rejects_identity_chain_substring_collision() -> None:
    payload = deepcopy(_load_v94("adeu_arc_submission_execution_record_v94_reference.json"))
    payload["submission_receipt_ref"] = payload["submission_receipt_ref"].replace(
        "run_001|", "run_0011|", 1
    )
    with pytest.raises(ValidationError, match="same request/environment/session/competition"):
        AdeuArcSubmissionExecutionRecord.model_validate(payload)


def test_v94_rejects_tournament_api_web_authority_leakage_fixture() -> None:
    payload = _load_v94(
        "adeu_arc_submission_execution_record_v94_reject_tournament_api_web_authority_leakage.json"
    )
    with pytest.raises(ValidationError, match="forbidden term"):
        AdeuArcSubmissionExecutionRecord.model_validate(payload)


def test_v94_rejects_scorecard_source_kind_lineage_drift() -> None:
    task_packet = _load_v89("adeu_arc_task_packet_v89_reference.json")
    observation = _load_v90("adeu_arc_observation_frame_v90_reference.json")
    hypothesis = _load_v90("adeu_arc_hypothesis_frame_v90_reference.json")
    action = _load_v91("adeu_arc_action_proposal_v91_reference.json")
    rollout = _load_v91("adeu_arc_rollout_trace_v91_reference.json")
    local_eval = _load_v92("adeu_arc_local_eval_record_v92_reference.json")
    scorecard = _load_v93("adeu_arc_scorecard_manifest_v93_case_local_shadow_only.json")
    submission = _load_v94("adeu_arc_submission_execution_record_v94_reference.json")

    with pytest.raises(
        ValueError,
        match="authorized submission is forbidden unless released scorecard_source_kind",
    ):
        derive_v42f_arc_submission_execution_record(
            task_packet=task_packet,
            task_packet_ref=submission["task_packet_ref"],
            observation_frame=observation,
            observation_frame_ref=submission["observation_frame_ref"],
            hypothesis_frame=hypothesis,
            hypothesis_frame_ref=submission["hypothesis_frame_ref"],
            action_proposal=action,
            action_proposal_ref=submission["action_proposal_ref"],
            rollout_trace=rollout,
            rollout_trace_ref=submission["rollout_trace_ref"],
            local_eval_record=local_eval,
            local_eval_record_ref=submission["local_eval_record_ref"],
            scorecard_manifest=scorecard,
            scorecard_manifest_ref=(
                "apps/api/fixtures/arc_agi/vnext_plus93/"
                "adeu_arc_scorecard_manifest_v93_case_local_shadow_only.json"
            ),
            environment_ref=submission["environment_ref"],
            session_ref=submission["session_ref"],
            competition_scope_ref=submission["competition_scope_ref"],
            model_id=submission["model_id"],
            run_id=submission["run_id"],
            submission_authorization_status=submission["submission_authorization_status"],
            submission_authorization_source_kind=scorecard["scorecard_source_kind"],
            submission_authorization_validity=submission["submission_authorization_validity"],
            submission_authorization_basis_refs=submission["submission_authorization_basis_refs"],
            submission_execution_status=submission["submission_execution_status"],
            submission_transport_profile=submission["submission_transport_profile"],
            external_request_ref=submission["external_request_ref"],
            submission_payload_ref=submission["submission_payload_ref"],
            submission_payload_hash=submission["submission_payload_hash"],
            submission_request_ts=submission["submission_request_ts"],
            submission_receipt_ref=submission["submission_receipt_ref"],
            submission_receipt_hash=submission["submission_receipt_hash"],
            submission_receipt_ts=submission["submission_receipt_ts"],
            result_import_status=submission["result_import_status"],
            result_source_kind=submission["result_source_kind"],
            result_authority_validity=submission["result_authority_validity"],
            result_authority_basis_refs=submission["result_authority_basis_refs"],
            result_import_ref=submission["result_import_ref"],
            result_import_hash=submission["result_import_hash"],
            result_import_ts=submission["result_import_ts"],
            lifecycle_transition_matrix_ref=submission["lifecycle_transition_matrix_ref"],
            submission_result_posture=submission["submission_result_posture"],
            submission_result_summary=submission["submission_result_summary"],
            bounded_orchestration_constraint_register=submission[
                "bounded_orchestration_constraint_register"
            ],
            settlement_posture_carry=submission["settlement_posture_carry"],
            deferred_authority_assertions=submission["deferred_authority_assertions"],
            evidence_refs=submission["evidence_refs"],
        )


def test_v94_rejects_missing_contract_source_in_result_authority_basis_refs() -> None:
    task_packet = _load_v89("adeu_arc_task_packet_v89_reference.json")
    observation = _load_v90("adeu_arc_observation_frame_v90_reference.json")
    hypothesis = _load_v90("adeu_arc_hypothesis_frame_v90_reference.json")
    action = _load_v91("adeu_arc_action_proposal_v91_reference.json")
    rollout = _load_v91("adeu_arc_rollout_trace_v91_reference.json")
    local_eval = _load_v92("adeu_arc_local_eval_record_v92_reference.json")
    scorecard = _load_v93("adeu_arc_scorecard_manifest_v93_case_official_imported.json")
    submission = _load_v94("adeu_arc_submission_execution_record_v94_reference.json")

    result_authority_basis_refs = [
        ref
        for ref in submission["result_authority_basis_refs"]
        if ref
        != (
            "docs/LOCKED_CONTINUATION_vNEXT_PLUS94.md"
            "#v42f_arc_submission_execution_contract@1"
        )
    ]
    with pytest.raises(
        ValueError,
        match="result_authority_basis_refs must include the released v42f contract source",
    ):
        derive_v42f_arc_submission_execution_record(
            task_packet=task_packet,
            task_packet_ref=submission["task_packet_ref"],
            observation_frame=observation,
            observation_frame_ref=submission["observation_frame_ref"],
            hypothesis_frame=hypothesis,
            hypothesis_frame_ref=submission["hypothesis_frame_ref"],
            action_proposal=action,
            action_proposal_ref=submission["action_proposal_ref"],
            rollout_trace=rollout,
            rollout_trace_ref=submission["rollout_trace_ref"],
            local_eval_record=local_eval,
            local_eval_record_ref=submission["local_eval_record_ref"],
            scorecard_manifest=scorecard,
            scorecard_manifest_ref=submission["scorecard_manifest_ref"],
            environment_ref=submission["environment_ref"],
            session_ref=submission["session_ref"],
            competition_scope_ref=submission["competition_scope_ref"],
            model_id=submission["model_id"],
            run_id=submission["run_id"],
            submission_authorization_status=submission["submission_authorization_status"],
            submission_authorization_source_kind=submission["submission_authorization_source_kind"],
            submission_authorization_validity=submission["submission_authorization_validity"],
            submission_authorization_basis_refs=submission["submission_authorization_basis_refs"],
            submission_execution_status=submission["submission_execution_status"],
            submission_transport_profile=submission["submission_transport_profile"],
            external_request_ref=submission["external_request_ref"],
            submission_payload_ref=submission["submission_payload_ref"],
            submission_payload_hash=submission["submission_payload_hash"],
            submission_request_ts=submission["submission_request_ts"],
            submission_receipt_ref=submission["submission_receipt_ref"],
            submission_receipt_hash=submission["submission_receipt_hash"],
            submission_receipt_ts=submission["submission_receipt_ts"],
            result_import_status=submission["result_import_status"],
            result_source_kind=submission["result_source_kind"],
            result_authority_validity=submission["result_authority_validity"],
            result_authority_basis_refs=result_authority_basis_refs,
            result_import_ref=submission["result_import_ref"],
            result_import_hash=submission["result_import_hash"],
            result_import_ts=submission["result_import_ts"],
            lifecycle_transition_matrix_ref=submission["lifecycle_transition_matrix_ref"],
            submission_result_posture=submission["submission_result_posture"],
            submission_result_summary=submission["submission_result_summary"],
            bounded_orchestration_constraint_register=submission[
                "bounded_orchestration_constraint_register"
            ],
            settlement_posture_carry=submission["settlement_posture_carry"],
            deferred_authority_assertions=submission["deferred_authority_assertions"],
            evidence_refs=submission["evidence_refs"],
        )
