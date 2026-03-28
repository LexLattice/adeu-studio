from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path

import pytest
from adeu_arc_agi import (
    ADEU_ARC_HYPOTHESIS_FRAME_SCHEMA,
    ADEU_ARC_OBSERVATION_FRAME_SCHEMA,
    AdeuArcHypothesisFrame,
    AdeuArcObservationFrame,
    compute_adeu_arc_hypothesis_frame_id,
    compute_adeu_arc_observation_frame_id,
)
from adeu_arc_solver import derive_v42b_observation_and_hypothesis
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v89_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus89"


def _v90_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus90"


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v89(name: str) -> dict[str, object]:
    return _load_json(_v89_root() / name)


def _load_v90(name: str) -> dict[str, object]:
    return _load_json(_v90_root() / name)


def _observation_schema_validator() -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_arc_agi"
            / "schema"
            / "adeu_arc_observation_frame.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _hypothesis_schema_validator() -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_arc_agi"
            / "schema"
            / "adeu_arc_hypothesis_frame.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v90_reference_fixtures_replay_and_validate() -> None:
    task_packet = _load_v89("adeu_arc_task_packet_v89_reference.json")
    observation = _load_v90("adeu_arc_observation_frame_v90_reference.json")
    hypothesis = _load_v90("adeu_arc_hypothesis_frame_v90_reference.json")

    validated_observation = AdeuArcObservationFrame.model_validate(observation)
    validated_hypothesis = AdeuArcHypothesisFrame.model_validate(hypothesis)

    assert validated_observation.schema == ADEU_ARC_OBSERVATION_FRAME_SCHEMA
    assert validated_hypothesis.schema == ADEU_ARC_HYPOTHESIS_FRAME_SCHEMA
    assert validated_observation.task_packet_id == task_packet["task_packet_id"]
    assert validated_hypothesis.observation_frame_id == observation["observation_frame_id"]

    observation_inputs = {
        "ontology_register": observation["ontology_register"],
        "entity_inventory": observation["entity_inventory"],
        "relation_inventory": observation["relation_inventory"],
        "state_partition_register": observation["state_partition_register"],
        "ontology_uncertainty_register": observation["ontology_uncertainty_register"],
        "observation_entries": observation["observation_entries"],
        "required_dimension_set": observation["required_dimension_set"],
        "missing_dimension_register": observation["missing_dimension_register"],
    }
    hypothesis_inputs = {
        "hypothesis_register": hypothesis["hypothesis_register"],
        "ambiguity_register": hypothesis["ambiguity_register"],
        "claim_posture_register": hypothesis["claim_posture_register"],
        "deontic_admissibility_register": hypothesis["deontic_admissibility_register"],
        "utility_pressure_register": hypothesis["utility_pressure_register"],
        "working_hypothesis_posture": hypothesis["working_hypothesis_posture"],
    }
    derived_observation, derived_hypothesis = derive_v42b_observation_and_hypothesis(
        task_packet=task_packet,
        task_packet_ref="apps/api/fixtures/arc_agi/vnext_plus89/adeu_arc_task_packet_v89_reference.json",
        observation_inputs=observation_inputs,
        hypothesis_inputs=hypothesis_inputs,
        observation_frame_ref="apps/api/fixtures/arc_agi/vnext_plus90/adeu_arc_observation_frame_v90_reference.json",
    )
    assert derived_observation == observation
    assert derived_hypothesis == hypothesis


def test_v90_frame_ids_are_deterministic() -> None:
    observation = _load_v90("adeu_arc_observation_frame_v90_reference.json")
    without_observation_id = deepcopy(observation)
    without_observation_id.pop("observation_frame_id")
    assert (
        compute_adeu_arc_observation_frame_id(without_observation_id)
        == observation["observation_frame_id"]
    )

    hypothesis = _load_v90("adeu_arc_hypothesis_frame_v90_reference.json")
    without_hypothesis_id = deepcopy(hypothesis)
    without_hypothesis_id.pop("hypothesis_frame_id")
    assert (
        compute_adeu_arc_hypothesis_frame_id(without_hypothesis_id)
        == hypothesis["hypothesis_frame_id"]
    )


def test_v90_exported_schemas_accept_reference_fixtures() -> None:
    _observation_schema_validator().validate(
        _load_v90("adeu_arc_observation_frame_v90_reference.json")
    )
    _hypothesis_schema_validator().validate(
        _load_v90("adeu_arc_hypothesis_frame_v90_reference.json")
    )


def test_v90_rejects_missing_oe_typing_fixture() -> None:
    payload = _load_v90("adeu_arc_observation_frame_v90_reject_missing_oe_typing_and_refs.json")
    with pytest.raises(ValidationError, match="observation_mode"):
        AdeuArcObservationFrame.model_validate(payload)


def test_v90_rejects_hypothesis_laundering_bleed_fixture() -> None:
    payload = _load_v90("adeu_arc_observation_frame_v90_reject_hypothesis_bleed.json")
    with pytest.raises(ValidationError, match="forbidden interpretation term"):
        AdeuArcObservationFrame.model_validate(payload)


def test_v90_rejects_unsupported_impossibility_fixture() -> None:
    payload = _load_v90(
        "adeu_arc_hypothesis_frame_v90_reject_ambiguity_laundering_impossibility.json"
    )
    with pytest.raises(ValidationError, match="forbidden interpretation term"):
        AdeuArcHypothesisFrame.model_validate(payload)


def test_v90_rejects_denominator_free_decomposition_coverage() -> None:
    payload = deepcopy(_load_v90("adeu_arc_observation_frame_v90_reference.json"))
    payload["required_dimension_set"] = []
    with pytest.raises(ValidationError, match="at least 1 item"):
        AdeuArcObservationFrame.model_validate(payload)


def test_v90_rejects_hidden_action_commitment_leakage() -> None:
    payload = deepcopy(_load_v90("adeu_arc_hypothesis_frame_v90_reference.json"))
    payload["working_hypothesis_posture"]["action_commitment_allowed"] = True  # type: ignore[index]
    with pytest.raises(ValidationError, match="action commitment"):
        AdeuArcHypothesisFrame.model_validate(payload)
