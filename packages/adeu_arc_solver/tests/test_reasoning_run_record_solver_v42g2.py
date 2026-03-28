from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from adeu_arc_solver import derive_v42g2_reasoning_run_record
from adeu_ir.repo import repo_root


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def test_solver_helper_replays_v96_reference_reasoning_run_record() -> None:
    root = _repo_root()
    puzzle_input_bundle = _load_json(
        root
        / "apps"
        / "api"
        / "fixtures"
        / "arc_agi"
        / "vnext_plus95"
        / "adeu_arc_puzzle_input_bundle_v95_reference.json"
    )
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
    run_record = _load_json(
        root
        / "apps"
        / "api"
        / "fixtures"
        / "arc_agi"
        / "vnext_plus96"
        / "adeu_arc_reasoning_run_record_v96_reference.json"
    )

    derived = derive_v42g2_reasoning_run_record(
        puzzle_input_bundle=puzzle_input_bundle,
        selected_puzzle_id=run_record["puzzle_id"],
        task_packet=task_packet,
        task_packet_ref=run_record["task_packet_ref"],
        observation_frame=observation,
        observation_frame_ref=run_record["observation_frame_ref"],
        hypothesis_frame=hypothesis,
        hypothesis_frame_ref=run_record["hypothesis_frame_ref"],
        action_proposal=action,
        action_proposal_ref=run_record["action_proposal_ref"],
        rollout_trace=rollout,
        rollout_trace_ref=run_record["rollout_trace_ref"],
        environment_ref=run_record["environment_ref"],
        session_ref=run_record["session_ref"],
        competition_scope_ref=run_record["competition_scope_ref"],
        model_id=run_record["model_id"],
        run_id=run_record["run_id"],
        agent_profile_ref=run_record["agent_profile_ref"],
        run_config_ref=run_record["run_config_ref"],
        prompt_profile_ref=run_record["prompt_profile_ref"],
        reasoning_effort_requested=run_record["reasoning_effort_requested"],
        reasoning_effort_observed=run_record["reasoning_effort_observed"],
        reasoning_effort_source_kind=run_record["reasoning_effort_source_kind"],
        task_packet_emission_evidence_refs=run_record["task_packet_emission_evidence_refs"],
        observation_frame_emission_evidence_refs=run_record[
            "observation_frame_emission_evidence_refs"
        ],
        hypothesis_frame_emission_evidence_refs=run_record[
            "hypothesis_frame_emission_evidence_refs"
        ],
        action_proposal_emission_evidence_refs=run_record[
            "action_proposal_emission_evidence_refs"
        ],
        rollout_trace_emission_evidence_refs=run_record[
            "rollout_trace_emission_evidence_refs"
        ],
        emission_sequence_register=run_record["emission_sequence_register"],
        run_execution_status=run_record["run_execution_status"],
        run_terminal_posture=run_record["run_terminal_posture"],
        rollout_presence_posture=run_record["rollout_presence_posture"],
        branching_posture=run_record["branching_posture"],
        branching_visibility_status=run_record["branching_visibility_status"],
        branch_event_refs=run_record["branch_event_refs"],
        settlement_posture_carry=run_record["settlement_posture_carry"],
        run_summary=run_record["run_summary"],
        evidence_refs=run_record["evidence_refs"],
    )

    assert derived == run_record
