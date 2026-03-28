from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from adeu_arc_solver import derive_v42f_submission_execution_record
from adeu_ir.repo import repo_root


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def test_solver_helper_replays_v94_reference_submission_execution_record() -> None:
    root = _repo_root()
    task_packet = _load_json(
        root
        / "apps"
        / "api"
        / "fixtures"
        / "arc_agi"
        / "vnext_plus89"
        / "adeu_arc_task_packet_v89_reference.json"
    )
    observation = _load_json(
        root
        / "apps"
        / "api"
        / "fixtures"
        / "arc_agi"
        / "vnext_plus90"
        / "adeu_arc_observation_frame_v90_reference.json"
    )
    hypothesis = _load_json(
        root
        / "apps"
        / "api"
        / "fixtures"
        / "arc_agi"
        / "vnext_plus90"
        / "adeu_arc_hypothesis_frame_v90_reference.json"
    )
    action = _load_json(
        root
        / "apps"
        / "api"
        / "fixtures"
        / "arc_agi"
        / "vnext_plus91"
        / "adeu_arc_action_proposal_v91_reference.json"
    )
    rollout = _load_json(
        root
        / "apps"
        / "api"
        / "fixtures"
        / "arc_agi"
        / "vnext_plus91"
        / "adeu_arc_rollout_trace_v91_reference.json"
    )
    local_eval = _load_json(
        root
        / "apps"
        / "api"
        / "fixtures"
        / "arc_agi"
        / "vnext_plus92"
        / "adeu_arc_local_eval_record_v92_reference.json"
    )
    scorecard = _load_json(
        root
        / "apps"
        / "api"
        / "fixtures"
        / "arc_agi"
        / "vnext_plus93"
        / "adeu_arc_scorecard_manifest_v93_case_official_imported.json"
    )
    submission = _load_json(
        root
        / "apps"
        / "api"
        / "fixtures"
        / "arc_agi"
        / "vnext_plus94"
        / "adeu_arc_submission_execution_record_v94_reference.json"
    )

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
