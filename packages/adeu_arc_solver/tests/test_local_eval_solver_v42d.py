from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from adeu_arc_solver import derive_v42d_local_eval_record
from adeu_ir.repo import repo_root


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def test_solver_helper_replays_v92_reference_record() -> None:
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

