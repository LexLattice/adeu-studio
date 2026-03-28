from __future__ import annotations

import json
from pathlib import Path

from adeu_arc_solver import derive_v42c_action_and_rollout
from adeu_ir.repo import repo_root


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def test_solver_helper_replays_v91_reference_pair() -> None:
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

    derived_action, derived_rollout = derive_v42c_action_and_rollout(
        task_packet=task_packet,
        task_packet_ref="apps/api/fixtures/arc_agi/vnext_plus89/adeu_arc_task_packet_v89_reference.json",
        observation_frame=observation,
        observation_frame_ref="apps/api/fixtures/arc_agi/vnext_plus90/adeu_arc_observation_frame_v90_reference.json",
        hypothesis_frame=hypothesis,
        hypothesis_frame_ref="apps/api/fixtures/arc_agi/vnext_plus90/adeu_arc_hypothesis_frame_v90_reference.json",
        action_inputs={
            "proposal_step_index": action["proposal_step_index"],
            "proposal_status": action["proposal_status"],
            "proposed_action_kind": action["proposed_action_kind"],
            "proposed_action_payload": action["proposed_action_payload"],
            "proposal_deontic_admissibility": action["proposal_deontic_admissibility"],
            "proposal_decision_basis": action["proposal_decision_basis"],
            "hypothesis_selection_basis": action["hypothesis_selection_basis"],
            "utility_pressure_basis": action["utility_pressure_basis"],
            "ambiguity_handling_basis": action["ambiguity_handling_basis"],
            "proposal_utility_posture": action["proposal_utility_posture"],
            "supporting_hypothesis_refs": action["supporting_hypothesis_refs"],
            "alternative_action_register": action["alternative_action_register"],
            "expected_state_delta": action["expected_state_delta"],
            "expected_hypothesis_effects": action["expected_hypothesis_effects"],
            "expected_falsification_conditions": action["expected_falsification_conditions"],
            "expected_ambiguity_effects": action["expected_ambiguity_effects"],
            "expected_outcome_summary": action["expected_outcome_summary"],
            "expected_outcome_refs": action["expected_outcome_refs"],
        },
        rollout_inputs={
            "rollout_steps": rollout["rollout_steps"],
            "terminal_rollout_status": rollout["terminal_rollout_status"],
            "rollout_stop_reason": rollout["rollout_stop_reason"],
            "outcome_hypothesis_effects": rollout["outcome_hypothesis_effects"],
            "expectation_outcome_comparison": rollout["expectation_outcome_comparison"],
            "settlement_posture_carry": rollout["settlement_posture_carry"],
        },
        action_proposal_ref="apps/api/fixtures/arc_agi/vnext_plus91/adeu_arc_action_proposal_v91_reference.json",
    )

    assert derived_action == action
    assert derived_rollout == rollout
