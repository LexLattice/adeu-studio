from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_arc_agi import (
    ADEU_ARC_LOCAL_EVAL_RECORD_SCHEMA,
    AdeuArcLocalEvalRecord,
    compute_adeu_arc_local_eval_record_id,
    derive_v42d_arc_local_eval_record,
)
from adeu_arc_solver import derive_v42d_local_eval_record
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


def _local_eval_schema_validator() -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_arc_agi"
            / "schema"
            / "adeu_arc_local_eval_record.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v92_reference_fixture_replays_and_validates() -> None:
    task_packet = _load_v89("adeu_arc_task_packet_v89_reference.json")
    observation = _load_v90("adeu_arc_observation_frame_v90_reference.json")
    hypothesis = _load_v90("adeu_arc_hypothesis_frame_v90_reference.json")
    action = _load_v91("adeu_arc_action_proposal_v91_reference.json")
    rollout = _load_v91("adeu_arc_rollout_trace_v91_reference.json")
    local_eval = _load_v92("adeu_arc_local_eval_record_v92_reference.json")

    validated = AdeuArcLocalEvalRecord.model_validate(local_eval)
    assert validated.schema == ADEU_ARC_LOCAL_EVAL_RECORD_SCHEMA
    assert validated.task_packet_id == task_packet["task_packet_id"]
    assert validated.observation_frame_id == observation["observation_frame_id"]
    assert validated.hypothesis_frame_id == hypothesis["hypothesis_frame_id"]
    assert validated.action_proposal_id == action["action_proposal_id"]
    assert validated.rollout_trace_id == rollout["rollout_trace_id"]

    derived = derive_v42d_local_eval_record(
        task_packet=task_packet,
        task_packet_ref=local_eval["task_packet_ref"],
        observation_frame=observation,
        observation_frame_ref=local_eval["observation_frame_ref"],
        hypothesis_frame=hypothesis,
        hypothesis_frame_ref=local_eval["hypothesis_frame_ref"],
        action_proposal=action,
        action_proposal_ref=local_eval["action_proposal_ref"],
        rollout_trace=rollout,
        rollout_trace_ref=local_eval["rollout_trace_ref"],
        benchmark_scope=local_eval["benchmark_scope"],
        benchmark_profile=local_eval["benchmark_profile"],
        model_id=local_eval["model_id"],
        run_id=local_eval["run_id"],
        sample_basis=local_eval["sample_basis"],
        evaluation_rule_set_ref=local_eval["evaluation_rule_set_ref"],
        evaluation_method_version=local_eval["evaluation_method_version"],
        task_success_basis=local_eval["task_success_basis"],
        adherence_metric_basis=local_eval["adherence_metric_basis"],
        ground_truth_refs=local_eval["ground_truth_refs"],
        task_success_metrics=local_eval["task_success_metrics"],
        adherence_metric_register=local_eval["adherence_metric_register"],
        adherence_failure_register=local_eval["adherence_failure_register"],
        control_plane_adherence_metrics=local_eval["control_plane_adherence_metrics"],
        settlement_posture_checks=local_eval["settlement_posture_checks"],
        evaluation_summary=local_eval["evaluation_summary"],
        evidence_refs=local_eval["evidence_refs"],
        deferred_authority_assertions=local_eval["deferred_authority_assertions"],
    )
    assert derived == local_eval


def test_v92_id_is_deterministic() -> None:
    local_eval = _load_v92("adeu_arc_local_eval_record_v92_reference.json")
    without_id = deepcopy(local_eval)
    without_id.pop("local_eval_record_id")
    assert compute_adeu_arc_local_eval_record_id(without_id) == local_eval["local_eval_record_id"]


def test_v92_exported_schema_accepts_reference_fixture() -> None:
    _local_eval_schema_validator().validate(
        _load_v92("adeu_arc_local_eval_record_v92_reference.json")
    )


def test_v92_accepts_orthogonality_matrix_cases() -> None:
    fixture_names = [
        "adeu_arc_local_eval_record_v92_case_task_success_control_success.json",
        "adeu_arc_local_eval_record_v92_case_task_success_control_fail.json",
        "adeu_arc_local_eval_record_v92_case_task_fail_control_success.json",
        "adeu_arc_local_eval_record_v92_case_task_fail_control_fail.json",
    ]
    seen: set[tuple[bool, bool]] = set()
    for fixture_name in fixture_names:
        payload = _load_v92(fixture_name)
        validated = AdeuArcLocalEvalRecord.model_validate(payload)
        task_solved = validated.task_success_metrics.task_solved
        control_plane_succeeded = (
            validated.control_plane_adherence_metrics.checks_passed
            == validated.control_plane_adherence_metrics.checks_total
        )
        seen.add((task_solved, control_plane_succeeded))
    assert seen == {(True, True), (True, False), (False, True), (False, False)}


def test_v92_rejects_missing_adherence_decomposition_fixture() -> None:
    payload = _load_v92(
        "adeu_arc_local_eval_record_v92_reject_missing_adherence_decomposition.json"
    )
    with pytest.raises(ValidationError, match="required decomposition keys"):
        AdeuArcLocalEvalRecord.model_validate(payload)


def test_v92_rejects_missing_evaluation_provenance_fixture() -> None:
    payload = _load_v92("adeu_arc_local_eval_record_v92_reject_missing_evaluation_provenance.json")
    with pytest.raises(ValidationError, match="evaluation_rule_set_ref must not be empty"):
        AdeuArcLocalEvalRecord.model_validate(payload)


def test_v92_rejects_scorecard_replay_leakage_fixture() -> None:
    payload = _load_v92("adeu_arc_local_eval_record_v92_reject_scorecard_competition_leakage.json")
    with pytest.raises(ValidationError, match="forbidden term"):
        AdeuArcLocalEvalRecord.model_validate(payload)


def test_v92_rejects_leaderboard_overclaim_fixture() -> None:
    payload = _load_v92("adeu_arc_local_eval_record_v92_reject_leaderboard_overclaim.json")
    with pytest.raises(ValidationError, match="forbidden term"):
        AdeuArcLocalEvalRecord.model_validate(payload)


def test_v92_rejects_retroactive_necessity_laundering() -> None:
    payload = deepcopy(_load_v92("adeu_arc_local_eval_record_v92_reference.json"))
    payload["evaluation_summary"] = "all solutions must follow this trajectory after one success"
    with pytest.raises(ValidationError, match="forbidden term"):
        AdeuArcLocalEvalRecord.model_validate(payload)


def test_v92_rejects_lineage_drift() -> None:
    task_packet = _load_v89("adeu_arc_task_packet_v89_reference.json")
    observation = _load_v90("adeu_arc_observation_frame_v90_reference.json")
    hypothesis = _load_v90("adeu_arc_hypothesis_frame_v90_reference.json")
    action = _load_v91("adeu_arc_action_proposal_v91_reference.json")
    rollout = _load_v91("adeu_arc_rollout_trace_v91_reference.json")
    local_eval = _load_v92("adeu_arc_local_eval_record_v92_reference.json")
    broken_rollout = deepcopy(rollout)
    broken_rollout["task_packet_id"] = "arc_task_drifted"

    with pytest.raises(ValueError, match="rollout_trace must bind to released task_packet_id"):
        derive_v42d_arc_local_eval_record(
            task_packet=task_packet,
            task_packet_ref=local_eval["task_packet_ref"],
            observation_frame=observation,
            observation_frame_ref=local_eval["observation_frame_ref"],
            hypothesis_frame=hypothesis,
            hypothesis_frame_ref=local_eval["hypothesis_frame_ref"],
            action_proposal=action,
            action_proposal_ref=local_eval["action_proposal_ref"],
            rollout_trace=broken_rollout,
            rollout_trace_ref=local_eval["rollout_trace_ref"],
            benchmark_scope=local_eval["benchmark_scope"],
            benchmark_profile=local_eval["benchmark_profile"],
            model_id=local_eval["model_id"],
            run_id=local_eval["run_id"],
            sample_basis=local_eval["sample_basis"],
            evaluation_rule_set_ref=local_eval["evaluation_rule_set_ref"],
            evaluation_method_version=local_eval["evaluation_method_version"],
            task_success_basis=local_eval["task_success_basis"],
            adherence_metric_basis=local_eval["adherence_metric_basis"],
            ground_truth_refs=local_eval["ground_truth_refs"],
            task_success_metrics=local_eval["task_success_metrics"],
            adherence_metric_register=local_eval["adherence_metric_register"],
            adherence_failure_register=local_eval["adherence_failure_register"],
            control_plane_adherence_metrics=local_eval["control_plane_adherence_metrics"],
            settlement_posture_checks=local_eval["settlement_posture_checks"],
            evaluation_summary=local_eval["evaluation_summary"],
            evidence_refs=local_eval["evidence_refs"],
            deferred_authority_assertions=local_eval["deferred_authority_assertions"],
        )


def test_v92_rejects_rollout_action_ref_drift() -> None:
    task_packet = _load_v89("adeu_arc_task_packet_v89_reference.json")
    observation = _load_v90("adeu_arc_observation_frame_v90_reference.json")
    hypothesis = _load_v90("adeu_arc_hypothesis_frame_v90_reference.json")
    action = _load_v91("adeu_arc_action_proposal_v91_reference.json")
    rollout = _load_v91("adeu_arc_rollout_trace_v91_reference.json")
    local_eval = _load_v92("adeu_arc_local_eval_record_v92_reference.json")
    broken_rollout = deepcopy(rollout)
    broken_rollout["expectation_surface_ref"] = (
        "apps/api/fixtures/arc_agi/vnext_plus91/non_matching.json"
    )

    with pytest.raises(
        ValueError, match="rollout_trace must preserve released action_proposal_ref lineage"
    ):
        derive_v42d_arc_local_eval_record(
            task_packet=task_packet,
            task_packet_ref=local_eval["task_packet_ref"],
            observation_frame=observation,
            observation_frame_ref=local_eval["observation_frame_ref"],
            hypothesis_frame=hypothesis,
            hypothesis_frame_ref=local_eval["hypothesis_frame_ref"],
            action_proposal=action,
            action_proposal_ref=local_eval["action_proposal_ref"],
            rollout_trace=broken_rollout,
            rollout_trace_ref=local_eval["rollout_trace_ref"],
            benchmark_scope=local_eval["benchmark_scope"],
            benchmark_profile=local_eval["benchmark_profile"],
            model_id=local_eval["model_id"],
            run_id=local_eval["run_id"],
            sample_basis=local_eval["sample_basis"],
            evaluation_rule_set_ref=local_eval["evaluation_rule_set_ref"],
            evaluation_method_version=local_eval["evaluation_method_version"],
            task_success_basis=local_eval["task_success_basis"],
            adherence_metric_basis=local_eval["adherence_metric_basis"],
            ground_truth_refs=local_eval["ground_truth_refs"],
            task_success_metrics=local_eval["task_success_metrics"],
            adherence_metric_register=local_eval["adherence_metric_register"],
            adherence_failure_register=local_eval["adherence_failure_register"],
            control_plane_adherence_metrics=local_eval["control_plane_adherence_metrics"],
            settlement_posture_checks=local_eval["settlement_posture_checks"],
            evaluation_summary=local_eval["evaluation_summary"],
            evidence_refs=local_eval["evidence_refs"],
            deferred_authority_assertions=local_eval["deferred_authority_assertions"],
        )


def test_v92_rejects_necessity_metric_inconsistency() -> None:
    payload = deepcopy(_load_v92("adeu_arc_local_eval_record_v92_reference.json"))
    payload["settlement_posture_checks"]["necessity_laundering_detected"] = True
    with pytest.raises(
        ValidationError,
        match=(
            "retroactive_necessity_laundering_absent must fail when "
            "necessity_laundering_detected is true"
        ),
    ):
        AdeuArcLocalEvalRecord.model_validate(payload)
