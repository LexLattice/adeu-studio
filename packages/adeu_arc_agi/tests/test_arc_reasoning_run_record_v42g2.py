from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_arc_agi import (
    ADEU_ARC_REASONING_RUN_RECORD_SCHEMA,
    AdeuArcReasoningRunRecord,
    compute_adeu_arc_reasoning_run_record_id,
    derive_v42g2_arc_reasoning_run_record,
)
from adeu_arc_solver import derive_v42g2_reasoning_run_record
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


def _v95_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus95"


def _v96_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus96"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v89(name: str) -> dict[str, Any]:
    return _load_json(_v89_root() / name)


def _load_v90(name: str) -> dict[str, Any]:
    return _load_json(_v90_root() / name)


def _load_v91(name: str) -> dict[str, Any]:
    return _load_json(_v91_root() / name)


def _load_v95(name: str) -> dict[str, Any]:
    return _load_json(_v95_root() / name)


def _load_v96(name: str) -> dict[str, Any]:
    return _load_json(_v96_root() / name)


def _run_record_schema_validator() -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_arc_agi"
            / "schema"
            / "adeu_arc_reasoning_run_record.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v96_reference_fixture_replays_and_validates() -> None:
    puzzle_input_bundle = _load_v95("adeu_arc_puzzle_input_bundle_v95_reference.json")
    task_packet = _load_v89("adeu_arc_task_packet_v89_reference.json")
    observation = _load_v90("adeu_arc_observation_frame_v90_reference.json")
    hypothesis = _load_v90("adeu_arc_hypothesis_frame_v90_reference.json")
    action = _load_v91("adeu_arc_action_proposal_v91_reference.json")
    rollout = _load_v91("adeu_arc_rollout_trace_v91_reference.json")
    run_record = _load_v96("adeu_arc_reasoning_run_record_v96_reference.json")

    validated = AdeuArcReasoningRunRecord.model_validate(run_record)
    assert validated.schema == ADEU_ARC_REASONING_RUN_RECORD_SCHEMA
    assert validated.puzzle_input_bundle_id == puzzle_input_bundle["puzzle_input_bundle_id"]
    assert validated.selection_register_id == puzzle_input_bundle["selection_register_id"]
    assert validated.task_packet_ref == run_record["task_packet_ref"]
    assert validated.observation_frame_ref == run_record["observation_frame_ref"]
    assert validated.hypothesis_frame_ref == run_record["hypothesis_frame_ref"]
    assert validated.action_proposal_ref == run_record["action_proposal_ref"]
    assert validated.rollout_trace_ref == run_record["rollout_trace_ref"]

    derived = derive_v42g2_arc_reasoning_run_record(
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


def test_v96_solver_helper_replays_reference_fixture() -> None:
    puzzle_input_bundle = _load_v95("adeu_arc_puzzle_input_bundle_v95_reference.json")
    task_packet = _load_v89("adeu_arc_task_packet_v89_reference.json")
    observation = _load_v90("adeu_arc_observation_frame_v90_reference.json")
    hypothesis = _load_v90("adeu_arc_hypothesis_frame_v90_reference.json")
    action = _load_v91("adeu_arc_action_proposal_v91_reference.json")
    rollout = _load_v91("adeu_arc_rollout_trace_v91_reference.json")
    run_record = _load_v96("adeu_arc_reasoning_run_record_v96_reference.json")

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


def test_v96_id_is_deterministic() -> None:
    payload = _load_v96("adeu_arc_reasoning_run_record_v96_reference.json")
    without_id = deepcopy(payload)
    without_id.pop("reasoning_run_record_id")
    assert (
        compute_adeu_arc_reasoning_run_record_id(without_id)
        == payload["reasoning_run_record_id"]
    )


def test_v96_exported_schema_accepts_reference_fixture() -> None:
    _run_record_schema_validator().validate(_load_v96("adeu_arc_reasoning_run_record_v96_reference.json"))


def test_v96_rejects_post_hoc_reconstruction_fixture() -> None:
    payload = _load_v96("adeu_arc_reasoning_run_record_v96_reject_post_hoc_reconstruction.json")
    with pytest.raises(ValidationError, match="forbidden term|post_hoc_reconstruction"):
        AdeuArcReasoningRunRecord.model_validate(payload)


def test_v96_rejects_missing_intermediate_occupancy_fixture() -> None:
    payload = _load_v96(
        "adeu_arc_reasoning_run_record_v96_reject_missing_intermediate_occupancy.json"
    )
    with pytest.raises(ValidationError, match="observation_frame_emission_evidence_refs"):
        AdeuArcReasoningRunRecord.model_validate(payload)


def test_v96_rejects_all_at_once_dump_without_staged_monotonic_evidence_fixture() -> None:
    payload = _load_v96(
        "adeu_arc_reasoning_run_record_v96_reject_all_at_once_dump_without_staged_monotonic_evidence.json"
    )
    with pytest.raises(
        ValidationError,
        match="must include each per-stage evidence ref exactly once|"
        "must include all required non-rollout stages",
    ):
        AdeuArcReasoningRunRecord.model_validate(payload)


def test_v96_rejects_identity_chain_mismatch_fixture() -> None:
    payload = _load_v96("adeu_arc_reasoning_run_record_v96_reject_identity_chain_mismatch.json")
    with pytest.raises(ValidationError, match="must bind to the same identity chain"):
        AdeuArcReasoningRunRecord.model_validate(payload)


def test_v96_rejects_hidden_branching_laundering_fixture() -> None:
    payload = _load_v96("adeu_arc_reasoning_run_record_v96_reject_hidden_branching_laundering.json")
    with pytest.raises(ValidationError, match="branching_observed posture requires"):
        AdeuArcReasoningRunRecord.model_validate(payload)


def test_v96_rejects_rollout_presence_posture_contradiction_fixture() -> None:
    payload = _load_v96(
        "adeu_arc_reasoning_run_record_v96_reject_rollout_presence_posture_contradiction.json"
    )
    with pytest.raises(ValidationError, match="rollout_absent posture forbids rollout_trace_ref"):
        AdeuArcReasoningRunRecord.model_validate(payload)


def test_v96_rejects_stage_evidence_ref_missing_from_sequence_register() -> None:
    payload = _load_v96("adeu_arc_reasoning_run_record_v96_reference.json")
    identity_chain = payload["evidence_refs"][1].split("identity_chain:", maxsplit=1)[1]
    payload["action_proposal_emission_evidence_refs"].append(
        f"evidence:action_emit:step_999|{identity_chain}"
    )
    with pytest.raises(
        ValidationError,
        match="must include each per-stage evidence ref exactly once",
    ):
        AdeuArcReasoningRunRecord.model_validate(payload)


def test_v96_rejects_stage_order_regression_in_emission_sequence_register() -> None:
    payload = _load_v96("adeu_arc_reasoning_run_record_v96_reference.json")
    identity_chain = payload["evidence_refs"][1].split("identity_chain:", maxsplit=1)[1]
    extra_obs_ref = f"evidence:observation_emit:step_999|{identity_chain}"
    payload["observation_frame_emission_evidence_refs"].append(extra_obs_ref)
    payload["emission_sequence_register"].append(
        {
            "stage": "observation_frame",
            "sequence_index": 6,
            "evidence_ref": extra_obs_ref,
        }
    )
    with pytest.raises(ValidationError, match="stage order must be non-regressing"):
        AdeuArcReasoningRunRecord.model_validate(payload)
