from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_arc_agi import (
    ADEU_ARC_ACTION_PROPOSAL_SCHEMA,
    ADEU_ARC_ROLLOUT_TRACE_SCHEMA,
    AdeuArcActionProposal,
    AdeuArcRolloutTrace,
    compute_adeu_arc_action_proposal_id,
    compute_adeu_arc_rollout_trace_id,
    derive_v42c_arc_action_proposal,
)
from adeu_arc_solver import derive_v42c_action_and_rollout
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


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v89(name: str) -> dict[str, object]:
    return _load_json(_v89_root() / name)


def _load_v90(name: str) -> dict[str, object]:
    return _load_json(_v90_root() / name)


def _load_v91(name: str) -> dict[str, object]:
    return _load_json(_v91_root() / name)


def _action_schema_validator() -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_arc_agi"
            / "schema"
            / "adeu_arc_action_proposal.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _rollout_schema_validator() -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_rollout_trace.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v91_reference_fixtures_replay_and_validate() -> None:
    task_packet = _load_v89("adeu_arc_task_packet_v89_reference.json")
    observation = _load_v90("adeu_arc_observation_frame_v90_reference.json")
    hypothesis = _load_v90("adeu_arc_hypothesis_frame_v90_reference.json")
    action = _load_v91("adeu_arc_action_proposal_v91_reference.json")
    rollout = _load_v91("adeu_arc_rollout_trace_v91_reference.json")

    validated_action = AdeuArcActionProposal.model_validate(action)
    validated_rollout = AdeuArcRolloutTrace.model_validate(rollout)
    assert validated_action.schema == ADEU_ARC_ACTION_PROPOSAL_SCHEMA
    assert validated_rollout.schema == ADEU_ARC_ROLLOUT_TRACE_SCHEMA
    assert validated_action.task_packet_id == task_packet["task_packet_id"]
    assert validated_rollout.task_packet_id == task_packet["task_packet_id"]

    action_inputs = {
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
    }
    rollout_inputs = {
        "rollout_steps": rollout["rollout_steps"],
        "terminal_rollout_status": rollout["terminal_rollout_status"],
        "rollout_stop_reason": rollout["rollout_stop_reason"],
        "outcome_hypothesis_effects": rollout["outcome_hypothesis_effects"],
        "expectation_outcome_comparison": rollout["expectation_outcome_comparison"],
        "settlement_posture_carry": rollout["settlement_posture_carry"],
    }
    derived_action, derived_rollout = derive_v42c_action_and_rollout(
        task_packet=task_packet,
        task_packet_ref="apps/api/fixtures/arc_agi/vnext_plus89/adeu_arc_task_packet_v89_reference.json",
        observation_frame=observation,
        observation_frame_ref="apps/api/fixtures/arc_agi/vnext_plus90/adeu_arc_observation_frame_v90_reference.json",
        hypothesis_frame=hypothesis,
        hypothesis_frame_ref="apps/api/fixtures/arc_agi/vnext_plus90/adeu_arc_hypothesis_frame_v90_reference.json",
        action_inputs=action_inputs,
        rollout_inputs=rollout_inputs,
        action_proposal_ref="apps/api/fixtures/arc_agi/vnext_plus91/adeu_arc_action_proposal_v91_reference.json",
    )
    assert derived_action == action
    assert derived_rollout == rollout


def test_v91_ids_are_deterministic() -> None:
    action = _load_v91("adeu_arc_action_proposal_v91_reference.json")
    without_action_id = deepcopy(action)
    without_action_id.pop("action_proposal_id")
    assert compute_adeu_arc_action_proposal_id(without_action_id) == action["action_proposal_id"]

    rollout = _load_v91("adeu_arc_rollout_trace_v91_reference.json")
    without_rollout_id = deepcopy(rollout)
    without_rollout_id.pop("rollout_trace_id")
    assert compute_adeu_arc_rollout_trace_id(without_rollout_id) == rollout["rollout_trace_id"]


def test_v91_exported_schemas_accept_reference_fixtures() -> None:
    _action_schema_validator().validate(_load_v91("adeu_arc_action_proposal_v91_reference.json"))
    _rollout_schema_validator().validate(_load_v91("adeu_arc_rollout_trace_v91_reference.json"))


def test_v91_rejects_deontically_inadmissible_action_proposal() -> None:
    task_packet = _load_v89("adeu_arc_task_packet_v89_reference.json")
    observation = _load_v90("adeu_arc_observation_frame_v90_reference.json")
    hypothesis = _load_v90("adeu_arc_hypothesis_frame_v90_reference.json")
    payload = _load_v91("adeu_arc_action_proposal_v91_reject_deontic_outside_envelope.json")
    with pytest.raises(ValueError, match="outside released legal_action_envelope"):
        derive_v42c_arc_action_proposal(
            task_packet=task_packet,
            task_packet_ref=payload["task_packet_ref"],  # type: ignore[index]
            observation_frame=observation,
            observation_frame_ref=payload["observation_frame_ref"],  # type: ignore[index]
            hypothesis_frame=hypothesis,
            hypothesis_frame_ref=payload["hypothesis_frame_ref"],  # type: ignore[index]
            proposal_step_index=payload["proposal_step_index"],  # type: ignore[index]
            proposal_status=payload["proposal_status"],  # type: ignore[index]
            proposed_action_kind=payload["proposed_action_kind"],  # type: ignore[index]
            proposed_action_payload=payload["proposed_action_payload"],  # type: ignore[index]
            proposal_deontic_admissibility=payload["proposal_deontic_admissibility"],  # type: ignore[index]
            proposal_decision_basis=payload["proposal_decision_basis"],  # type: ignore[index]
            hypothesis_selection_basis=payload["hypothesis_selection_basis"],  # type: ignore[index]
            utility_pressure_basis=payload["utility_pressure_basis"],  # type: ignore[index]
            ambiguity_handling_basis=payload["ambiguity_handling_basis"],  # type: ignore[index]
            proposal_utility_posture=payload["proposal_utility_posture"],  # type: ignore[index]
            supporting_hypothesis_refs=payload["supporting_hypothesis_refs"],  # type: ignore[index]
            alternative_action_register=payload["alternative_action_register"],  # type: ignore[index]
            expected_state_delta=payload["expected_state_delta"],  # type: ignore[index]
            expected_hypothesis_effects=payload["expected_hypothesis_effects"],  # type: ignore[index]
            expected_falsification_conditions=payload["expected_falsification_conditions"],  # type: ignore[index]
            expected_ambiguity_effects=payload["expected_ambiguity_effects"],  # type: ignore[index]
            expected_outcome_summary=payload["expected_outcome_summary"],  # type: ignore[index]
            expected_outcome_refs=payload["expected_outcome_refs"],  # type: ignore[index]
        )


def test_v91_rejects_hidden_utility_tactical_opacity_fixture() -> None:
    payload = _load_v91("adeu_arc_action_proposal_v91_reject_hidden_utility_laundering.json")
    with pytest.raises(ValidationError, match="proposal_decision_basis must not be empty"):
        AdeuArcActionProposal.model_validate(payload)


def test_v91_rejects_expectation_lineage_omission_fixture() -> None:
    payload = _load_v91("adeu_arc_rollout_trace_v91_reject_expectation_lineage_omission.json")
    with pytest.raises(ValidationError, match="must include evaluated"):
        AdeuArcRolloutTrace.model_validate(payload)


def test_v91_rejects_post_hoc_expectation_rewrite_fixture() -> None:
    payload = _load_v91("adeu_arc_rollout_trace_v91_reject_expectation_rewrite.json")
    with pytest.raises(ValidationError, match="expectation surface hash mismatch"):
        AdeuArcRolloutTrace.model_validate(payload)


def test_v91_rejects_retroactive_necessity_laundering_fixture() -> None:
    payload = _load_v91("adeu_arc_rollout_trace_v91_reject_retroactive_necessity_laundering.json")
    with pytest.raises(ValidationError, match="forbidden term"):
        AdeuArcRolloutTrace.model_validate(payload)


def test_v91_rejects_scorecard_replay_semantic_leakage() -> None:
    payload = deepcopy(_load_v91("adeu_arc_action_proposal_v91_reference.json"))
    payload["proposal_decision_basis"] = (
        "choose action for leaderboard optimization with hidden scorecard path"
    )
    with pytest.raises(ValidationError, match="forbidden term"):
        AdeuArcActionProposal.model_validate(payload)
