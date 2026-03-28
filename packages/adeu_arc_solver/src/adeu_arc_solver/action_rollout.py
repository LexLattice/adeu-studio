from __future__ import annotations

from copy import deepcopy
from typing import Any

from adeu_arc_agi import derive_v42c_arc_action_proposal, derive_v42c_arc_rollout_trace


def derive_v42c_action_and_rollout(
    *,
    task_packet: dict[str, Any],
    task_packet_ref: str,
    observation_frame: dict[str, Any],
    observation_frame_ref: str,
    hypothesis_frame: dict[str, Any],
    hypothesis_frame_ref: str,
    action_inputs: dict[str, Any],
    rollout_inputs: dict[str, Any],
    action_proposal_ref: str,
) -> tuple[dict[str, Any], dict[str, Any]]:
    action_proposal = derive_v42c_arc_action_proposal(
        task_packet=deepcopy(task_packet),
        task_packet_ref=task_packet_ref,
        observation_frame=deepcopy(observation_frame),
        observation_frame_ref=observation_frame_ref,
        hypothesis_frame=deepcopy(hypothesis_frame),
        hypothesis_frame_ref=hypothesis_frame_ref,
        proposal_step_index=action_inputs["proposal_step_index"],
        proposal_status=action_inputs["proposal_status"],
        proposed_action_kind=action_inputs.get("proposed_action_kind"),
        proposed_action_payload=deepcopy(action_inputs.get("proposed_action_payload")),
        proposal_deontic_admissibility=action_inputs["proposal_deontic_admissibility"],
        proposal_decision_basis=action_inputs["proposal_decision_basis"],
        hypothesis_selection_basis=action_inputs["hypothesis_selection_basis"],
        utility_pressure_basis=action_inputs["utility_pressure_basis"],
        ambiguity_handling_basis=action_inputs["ambiguity_handling_basis"],
        proposal_utility_posture=action_inputs["proposal_utility_posture"],
        supporting_hypothesis_refs=deepcopy(action_inputs["supporting_hypothesis_refs"]),
        alternative_action_register=deepcopy(action_inputs["alternative_action_register"]),
        expected_state_delta=deepcopy(action_inputs["expected_state_delta"]),
        expected_hypothesis_effects=deepcopy(action_inputs["expected_hypothesis_effects"]),
        expected_falsification_conditions=deepcopy(
            action_inputs["expected_falsification_conditions"]
        ),
        expected_ambiguity_effects=deepcopy(action_inputs["expected_ambiguity_effects"]),
        expected_outcome_summary=action_inputs["expected_outcome_summary"],
        expected_outcome_refs=deepcopy(action_inputs["expected_outcome_refs"]),
    )
    rollout_trace = derive_v42c_arc_rollout_trace(
        task_packet=deepcopy(task_packet),
        task_packet_ref=task_packet_ref,
        action_proposal=action_proposal,
        action_proposal_ref=action_proposal_ref,
        rollout_steps=deepcopy(rollout_inputs["rollout_steps"]),
        terminal_rollout_status=rollout_inputs["terminal_rollout_status"],
        rollout_stop_reason=rollout_inputs["rollout_stop_reason"],
        outcome_hypothesis_effects=deepcopy(rollout_inputs["outcome_hypothesis_effects"]),
        expectation_outcome_comparison=deepcopy(rollout_inputs["expectation_outcome_comparison"]),
        settlement_posture_carry=deepcopy(rollout_inputs["settlement_posture_carry"]),
    )
    return action_proposal, rollout_trace
