from __future__ import annotations

from copy import deepcopy
from typing import Any

from adeu_arc_agi import derive_v42d_arc_local_eval_record


def derive_v42d_local_eval_record(
    *,
    task_packet: dict[str, Any],
    task_packet_ref: str,
    observation_frame: dict[str, Any],
    observation_frame_ref: str,
    hypothesis_frame: dict[str, Any],
    hypothesis_frame_ref: str,
    action_proposal: dict[str, Any],
    action_proposal_ref: str,
    rollout_trace: dict[str, Any],
    rollout_trace_ref: str,
    benchmark_scope: str,
    benchmark_profile: str,
    model_id: str,
    run_id: str,
    sample_basis: str,
    evaluation_rule_set_ref: str,
    evaluation_method_version: str,
    task_success_basis: str,
    adherence_metric_basis: str,
    ground_truth_refs: list[str],
    task_success_metrics: dict[str, Any],
    adherence_metric_register: list[dict[str, Any]],
    adherence_failure_register: list[dict[str, Any]],
    control_plane_adherence_metrics: dict[str, Any],
    settlement_posture_checks: dict[str, Any],
    evaluation_summary: str,
    evidence_refs: list[str],
    deferred_authority_assertions: list[str],
) -> dict[str, Any]:
    return derive_v42d_arc_local_eval_record(
        task_packet=deepcopy(task_packet),
        task_packet_ref=task_packet_ref,
        observation_frame=deepcopy(observation_frame),
        observation_frame_ref=observation_frame_ref,
        hypothesis_frame=deepcopy(hypothesis_frame),
        hypothesis_frame_ref=hypothesis_frame_ref,
        action_proposal=deepcopy(action_proposal),
        action_proposal_ref=action_proposal_ref,
        rollout_trace=deepcopy(rollout_trace),
        rollout_trace_ref=rollout_trace_ref,
        benchmark_scope=benchmark_scope,  # type: ignore[arg-type]
        benchmark_profile=benchmark_profile,
        model_id=model_id,
        run_id=run_id,
        sample_basis=sample_basis,
        evaluation_rule_set_ref=evaluation_rule_set_ref,
        evaluation_method_version=evaluation_method_version,
        task_success_basis=task_success_basis,
        adherence_metric_basis=adherence_metric_basis,
        ground_truth_refs=deepcopy(ground_truth_refs),
        task_success_metrics=deepcopy(task_success_metrics),
        adherence_metric_register=deepcopy(adherence_metric_register),
        adherence_failure_register=deepcopy(adherence_failure_register),
        control_plane_adherence_metrics=deepcopy(control_plane_adherence_metrics),
        settlement_posture_checks=deepcopy(settlement_posture_checks),
        evaluation_summary=evaluation_summary,
        evidence_refs=deepcopy(evidence_refs),
        deferred_authority_assertions=deepcopy(deferred_authority_assertions),
    )

