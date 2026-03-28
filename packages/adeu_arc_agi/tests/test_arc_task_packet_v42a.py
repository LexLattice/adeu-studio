from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path

import pytest
from adeu_arc_agi import (
    ADEU_ARC_TASK_PACKET_SCHEMA,
    AdeuArcTaskPacket,
    canonicalize_adeu_arc_task_packet_payload,
    compute_adeu_arc_task_packet_id,
    derive_v42a_arc_task_packet,
)
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v89_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus89"


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v89(name: str) -> dict[str, object]:
    return _load_json(_v89_root() / name)


def _schema_validator() -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_arc_agi"
            / "schema"
            / "adeu_arc_task_packet.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v89_reference_fixture_replays_and_validates() -> None:
    packet = _load_v89("adeu_arc_task_packet_v89_reference.json")
    validated = AdeuArcTaskPacket.model_validate(packet)

    assert validated.schema == ADEU_ARC_TASK_PACKET_SCHEMA
    assert validated.environment_authority == "official_arc_toolkit"
    assert validated.mode_posture == "local_offline"

    derived = derive_v42a_arc_task_packet(
        adapter="arc_toolkit_local/v1",
        game_ref="toolkit://local/arcagi3/game/sample_game_001",
        session_ref="toolkit://local/arcagi3/session/sample_session_001",
        initial_state_ref="toolkit://local/arcagi3/state/sample_state_001",
        initial_state_hash="2f6fcbf68f2f5f0c3073b7479247138ba68f75d84a38d64f8ef96f5c3f028de9",
        toolkit_legal_action_envelope=["edit_cell", "submit"],
        legal_action_envelope=["edit_cell"],
        normalization_kind="subset",
    )
    assert derived == packet
    assert canonicalize_adeu_arc_task_packet_payload(packet) == packet


def test_v89_task_packet_id_is_deterministic_and_boundary_sensitive() -> None:
    packet = _load_v89("adeu_arc_task_packet_v89_reference.json")
    without_id = deepcopy(packet)
    without_id.pop("task_packet_id")
    assert compute_adeu_arc_task_packet_id(without_id) == packet["task_packet_id"]

    mutated = deepcopy(without_id)
    mutated["adapter"] = "arc_toolkit_local/v2"
    assert compute_adeu_arc_task_packet_id(mutated) != packet["task_packet_id"]


def test_v89_exported_schema_accepts_reference_fixture() -> None:
    _schema_validator().validate(_load_v89("adeu_arc_task_packet_v89_reference.json"))


def test_v89_rejects_non_authoritative_adapter_posture_fixture() -> None:
    payload = _load_v89("adeu_arc_task_packet_v89_reject_non_authoritative_posture.json")
    with pytest.raises(ValidationError, match="official_arc_toolkit"):
        AdeuArcTaskPacket.model_validate(payload)


def test_v89_rejects_inconsistent_legal_envelope_fixture() -> None:
    payload = _load_v89("adeu_arc_task_packet_v89_reject_inconsistent_legal_envelope.json")
    with pytest.raises(ValidationError, match="subset of toolkit_legal_action_envelope"):
        AdeuArcTaskPacket.model_validate(payload)


def test_v89_rejects_policy_semantic_smuggling() -> None:
    payload = deepcopy(_load_v89("adeu_arc_task_packet_v89_reference.json"))
    payload["adapter_boundary_policy"]["solver_hint"] = "latent_branching"  # type: ignore[index]
    with pytest.raises(ValidationError, match="Extra inputs are not permitted"):
        AdeuArcTaskPacket.model_validate(payload)


def test_v89_rejects_synthetic_prompt_packet_identity() -> None:
    payload = deepcopy(_load_v89("adeu_arc_task_packet_v89_reference.json"))
    payload["initial_state_ref"] = "prompt://synthetic/arcagi3/state/sample_state_001"
    with pytest.raises(ValidationError, match="initial_state_ref must be sourced"):
        AdeuArcTaskPacket.model_validate(payload)


def test_v89_rejects_scorecard_authority_leakage() -> None:
    payload = deepcopy(_load_v89("adeu_arc_task_packet_v89_reference.json"))
    payload["adapter_boundary_policy"]["scorecard_authority_allowed"] = True  # type: ignore[index]
    with pytest.raises(ValidationError, match="scorecard authority"):
        AdeuArcTaskPacket.model_validate(payload)


def test_v89_rejects_task_packet_id_derived_from_state_only() -> None:
    payload = deepcopy(_load_v89("adeu_arc_task_packet_v89_reference.json"))
    payload["adapter"] = "arc_toolkit_local/v2"
    with pytest.raises(ValidationError, match="canonical full packet payload hash identity"):
        AdeuArcTaskPacket.model_validate(payload)
