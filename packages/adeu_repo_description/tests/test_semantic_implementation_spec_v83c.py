from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_IMPLEMENTATION_SPEC_PROJECTION_PACKET_SCHEMA,
    REPO_INTENT_TO_WORK_PACKET_HANDOFF_SCHEMA,
    REPO_SEMANTIC_IMPLEMENTATION_SPEC_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    RepoArtifactObligationMap,
    RepoImplementationSpecProjectionPacket,
    RepoIntentEdgeDecomposition,
    RepoIntentNonImplementationGuardrail,
    RepoIntentSourceIndex,
    RepoIntentToWorkPacketHandoff,
    RepoSemanticDriftAmbiguityRegister,
    RepoSemanticImplementationSpecFamilyCloseoutAlignment,
    RepoSemanticIntentContract,
    derive_v83c_semantic_implementation_projection_bundle,
    validate_v83c_semantic_implementation_projection_bundle,
)
from adeu_repo_description.semantic_implementation_spec import _surface_id
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root(slice_name: str) -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / slice_name


def _load_fixture(slice_name: str, name: str) -> dict[str, Any]:
    return json.loads((_fixture_root(slice_name) / name).read_text(encoding="utf-8"))


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_repo_description" / "schema" / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _v83a_source_index() -> RepoIntentSourceIndex:
    return RepoIntentSourceIndex.model_validate(
        _load_fixture("vnext_plus233", "repo_intent_source_index_v233_reference.json")
    )


def _v83a_contract() -> RepoSemanticIntentContract:
    return RepoSemanticIntentContract.model_validate(
        _load_fixture("vnext_plus233", "repo_semantic_intent_contract_v233_reference.json")
    )


def _v83a_guardrail() -> RepoIntentNonImplementationGuardrail:
    return RepoIntentNonImplementationGuardrail.model_validate(
        _load_fixture(
            "vnext_plus233",
            "repo_intent_non_implementation_guardrail_v233_reference.json",
        )
    )


def _v83b_edge_decomposition() -> RepoIntentEdgeDecomposition:
    return RepoIntentEdgeDecomposition.model_validate(
        _load_fixture("vnext_plus234", "repo_intent_edge_decomposition_v234_reference.json")
    )


def _v83b_obligation_map() -> RepoArtifactObligationMap:
    return RepoArtifactObligationMap.model_validate(
        _load_fixture("vnext_plus234", "repo_artifact_obligation_map_v234_reference.json")
    )


def _v83b_drift_register() -> RepoSemanticDriftAmbiguityRegister:
    return RepoSemanticDriftAmbiguityRegister.model_validate(
        _load_fixture(
            "vnext_plus234",
            "repo_semantic_drift_ambiguity_register_v234_reference.json",
        )
    )


def _v83c_projection_packet(
    name: str = "repo_implementation_spec_projection_packet_v235_reference.json",
) -> RepoImplementationSpecProjectionPacket:
    return RepoImplementationSpecProjectionPacket.model_validate(
        _load_fixture("vnext_plus235", name)
    )


def _v83c_handoff(
    name: str = "repo_intent_to_work_packet_handoff_v235_reference.json",
) -> RepoIntentToWorkPacketHandoff:
    return RepoIntentToWorkPacketHandoff.model_validate(_load_fixture("vnext_plus235", name))


def _v83c_closeout(
    name: str = "repo_semantic_implementation_spec_family_closeout_alignment_v235_reference.json",
) -> RepoSemanticImplementationSpecFamilyCloseoutAlignment:
    return RepoSemanticImplementationSpecFamilyCloseoutAlignment.model_validate(
        _load_fixture("vnext_plus235", name)
    )


def _validate_reference_bundle_with(
    *,
    projection_packet: RepoImplementationSpecProjectionPacket | None = None,
    handoff: RepoIntentToWorkPacketHandoff | None = None,
    closeout: RepoSemanticImplementationSpecFamilyCloseoutAlignment | None = None,
) -> None:
    validate_v83c_semantic_implementation_projection_bundle(
        intent_source_index=_v83a_source_index(),
        semantic_intent_contract=_v83a_contract(),
        intent_non_implementation_guardrail=_v83a_guardrail(),
        intent_edge_decomposition=_v83b_edge_decomposition(),
        artifact_obligation_map=_v83b_obligation_map(),
        semantic_drift_ambiguity_register=_v83b_drift_register(),
        implementation_spec_projection_packet=projection_packet or _v83c_projection_packet(),
        intent_to_work_packet_handoff=handoff or _v83c_handoff(),
        semantic_implementation_spec_family_closeout_alignment=closeout or _v83c_closeout(),
    )


def _projection_with_recomputed_id(
    payload: dict[str, Any],
) -> RepoImplementationSpecProjectionPacket:
    payload["implementation_spec_projection_packet_id"] = _surface_id(
        "repo_implementation_spec_projection_packet",
        payload["schema"],
        payload,
        "implementation_spec_projection_packet_id",
    )
    return RepoImplementationSpecProjectionPacket.model_validate(payload)


def _handoff_with_recomputed_id(payload: dict[str, Any]) -> RepoIntentToWorkPacketHandoff:
    payload["intent_to_work_packet_handoff_id"] = _surface_id(
        "repo_intent_to_work_packet_handoff",
        payload["schema"],
        payload,
        "intent_to_work_packet_handoff_id",
    )
    return RepoIntentToWorkPacketHandoff.model_validate(payload)


def _handoff_for_projection(
    projection_packet: RepoImplementationSpecProjectionPacket,
) -> RepoIntentToWorkPacketHandoff:
    payload = deepcopy(
        _load_fixture("vnext_plus235", "repo_intent_to_work_packet_handoff_v235_reference.json")
    )
    payload["implementation_spec_projection_packet_id"] = (
        projection_packet.implementation_spec_projection_packet_id
    )
    return _handoff_with_recomputed_id(payload)


def _closeout_with_recomputed_id(
    payload: dict[str, Any],
) -> RepoSemanticImplementationSpecFamilyCloseoutAlignment:
    payload["semantic_implementation_spec_family_closeout_alignment_id"] = _surface_id(
        "repo_semantic_implementation_spec_family_closeout_alignment",
        payload["schema"],
        payload,
        "semantic_implementation_spec_family_closeout_alignment_id",
    )
    return RepoSemanticImplementationSpecFamilyCloseoutAlignment.model_validate(payload)


def _closeout_for_projection_and_handoff(
    projection_packet: RepoImplementationSpecProjectionPacket,
    handoff: RepoIntentToWorkPacketHandoff,
) -> RepoSemanticImplementationSpecFamilyCloseoutAlignment:
    payload = deepcopy(
        _load_fixture(
            "vnext_plus235",
            "repo_semantic_implementation_spec_family_closeout_alignment_v235_reference.json",
        )
    )
    payload["implementation_spec_projection_packet_id"] = (
        projection_packet.implementation_spec_projection_packet_id
    )
    payload["intent_to_work_packet_handoff_id"] = handoff.intent_to_work_packet_handoff_id
    return _closeout_with_recomputed_id(payload)


def test_v235_reference_bundle_validates() -> None:
    projection_packet = _v83c_projection_packet()
    handoff = _v83c_handoff()
    closeout = _v83c_closeout()

    assert projection_packet.schema == REPO_IMPLEMENTATION_SPEC_PROJECTION_PACKET_SCHEMA
    assert handoff.schema == REPO_INTENT_TO_WORK_PACKET_HANDOFF_SCHEMA
    assert closeout.schema == REPO_SEMANTIC_IMPLEMENTATION_SPEC_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA

    packet_row = projection_packet.projection_packet_rows[0]
    assert packet_row.projection_posture == "projection_packet_ready_for_review"
    assert {
        row.check_kind for row in packet_row.spec_review_checklist_rows
    }.issuperset(
        {
            "edge_coverage_check",
            "generated_spec_provenance_check",
            "reject_fixture_check",
            "source_binding_check",
            "validation_evidence_check",
        }
    )
    assert handoff.handoff_rows[0].implementation_lock_requirement == (
        "canonical_starter_lock_required"
    )

    _validate_reference_bundle_with(
        projection_packet=projection_packet,
        handoff=handoff,
        closeout=closeout,
    )


def test_v235_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_implementation_spec_projection_packet.v1.json").validate(
        _load_fixture(
            "vnext_plus235",
            "repo_implementation_spec_projection_packet_v235_reference.json",
        )
    )
    _schema_validator("repo_intent_to_work_packet_handoff.v1.json").validate(
        _load_fixture("vnext_plus235", "repo_intent_to_work_packet_handoff_v235_reference.json")
    )
    _schema_validator(
        "repo_semantic_implementation_spec_family_closeout_alignment.v1.json"
    ).validate(
        _load_fixture(
            "vnext_plus235",
            "repo_semantic_implementation_spec_family_closeout_alignment_v235_reference.json",
        )
    )


def test_v235_derivation_helper_matches_reference_fixtures() -> None:
    *_, projection_packet, handoff, closeout = (
        derive_v83c_semantic_implementation_projection_bundle(repo_root=_repo_root())
    )

    assert projection_packet.model_dump(mode="json") == _load_fixture(
        "vnext_plus235",
        "repo_implementation_spec_projection_packet_v235_reference.json",
    )
    assert handoff.model_dump(mode="json") == _load_fixture(
        "vnext_plus235",
        "repo_intent_to_work_packet_handoff_v235_reference.json",
    )
    assert closeout.model_dump(mode="json") == _load_fixture(
        "vnext_plus235",
        "repo_semantic_implementation_spec_family_closeout_alignment_v235_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_semantic_implementation_spec_v235_reject_projection_without_intent_contract_refs.json",
            RepoImplementationSpecProjectionPacket,
            "at least 1 item",
        ),
        (
            "repo_semantic_implementation_spec_v235_reject_projection_generated_without_provenance.json",
            RepoImplementationSpecProjectionPacket,
            "model/agent projection provenance requires profile and prompt refs",
        ),
        (
            "repo_semantic_implementation_spec_v235_reject_projection_ready_with_carried_blocker.json",
            RepoImplementationSpecProjectionPacket,
            "ready projection packets cannot carry blockers",
        ),
        (
            "repo_semantic_implementation_spec_v235_reject_implementation_spec_without_obligation_refs.json",
            RepoImplementationSpecProjectionPacket,
            "at least 1 item",
        ),
        (
            "repo_semantic_implementation_spec_v235_reject_broad_projection_target_surface.json",
            RepoImplementationSpecProjectionPacket,
            "bounded target surfaces",
        ),
        (
            "repo_semantic_implementation_spec_v235_reject_handoff_missing_canonical_later_lock.json",
            RepoIntentToWorkPacketHandoff,
            "ready work-packet handoffs require canonical later lock",
        ),
        (
            "repo_semantic_implementation_spec_v235_reject_handoff_ready_to_implement_now.json",
            RepoIntentToWorkPacketHandoff,
            r"may not carry V83(?:-C)? implementation authority",
        ),
        (
            "repo_semantic_implementation_spec_v235_reject_work_packet_executed.json",
            RepoIntentToWorkPacketHandoff,
            "V83-C handoffs must not execute work packets",
        ),
        (
            "repo_semantic_implementation_spec_v235_reject_meta_orchestrator_runtime_authorized.json",
            RepoIntentToWorkPacketHandoff,
            "meta-orchestrator handoffs remain workflow review only",
        ),
        (
            "repo_semantic_implementation_spec_v235_reject_closeout_selects_v84.json",
            RepoSemanticImplementationSpecFamilyCloseoutAlignment,
            "must not select V84",
        ),
        (
            "repo_semantic_implementation_spec_v235_reject_closeout_claims_code_implementation.json",
            RepoSemanticImplementationSpecFamilyCloseoutAlignment,
            r"may not carry V83(?:-C)? implementation authority",
        ),
    ],
)
def test_v235_model_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[BaseModel],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus235", fixture_name))


def test_v235_bundle_rejects_projection_parent_mismatch() -> None:
    payload = deepcopy(
        _load_fixture(
            "vnext_plus235",
            "repo_implementation_spec_projection_packet_v235_reference.json",
        )
    )
    payload["artifact_obligation_map_id"] = "repo_artifact_obligation_map:v83b:mismatched"
    projection_packet = _projection_with_recomputed_id(payload)

    with pytest.raises(ValueError, match="projection packet must reference released V83-A/B"):
        _validate_reference_bundle_with(projection_packet=projection_packet)


def test_v235_bundle_rejects_handoff_unknown_obligation_ref() -> None:
    payload = deepcopy(
        _load_fixture("vnext_plus235", "repo_intent_to_work_packet_handoff_v235_reference.json")
    )
    payload["handoff_rows"][0]["artifact_obligation_refs"] = [
        "artifact-obligation:v83c:unknown"
    ]
    handoff = _handoff_with_recomputed_id(payload)
    closeout_payload = deepcopy(
        _load_fixture(
            "vnext_plus235",
            "repo_semantic_implementation_spec_family_closeout_alignment_v235_reference.json",
        )
    )
    closeout_payload["intent_to_work_packet_handoff_id"] = (
        handoff.intent_to_work_packet_handoff_id
    )
    closeout = _closeout_with_recomputed_id(closeout_payload)

    with pytest.raises(ValueError, match="work-packet handoff obligation refs must be known"):
        _validate_reference_bundle_with(handoff=handoff, closeout=closeout)


@pytest.mark.parametrize(
    ("field_name", "bad_ref", "match"),
    [
        (
            "semantic_edge_refs",
            "semantic-relation:v83b:unknown",
            "projection checklist semantic edge refs must be known",
        ),
        (
            "artifact_obligation_refs",
            "artifact-obligation:v83b:unknown",
            "projection checklist obligation refs must be known",
        ),
        (
            "source_refs",
            "source:v83c:unknown",
            "projection checklist source refs must be known",
        ),
    ],
)
def test_v235_bundle_rejects_unknown_projection_checklist_refs(
    field_name: str,
    bad_ref: str,
    match: str,
) -> None:
    payload = deepcopy(
        _load_fixture(
            "vnext_plus235",
            "repo_implementation_spec_projection_packet_v235_reference.json",
        )
    )
    payload["projection_packet_rows"][0]["spec_review_checklist_rows"][0][field_name] = [
        bad_ref
    ]
    projection_packet = _projection_with_recomputed_id(payload)
    handoff = _handoff_for_projection(projection_packet)
    closeout = _closeout_for_projection_and_handoff(projection_packet, handoff)

    with pytest.raises(ValueError, match=match):
        _validate_reference_bundle_with(
            projection_packet=projection_packet,
            handoff=handoff,
            closeout=closeout,
        )


def test_v235_bundle_rejects_tests_only_quality_gate() -> None:
    payload = deepcopy(
        _load_fixture(
            "vnext_plus235",
            "repo_implementation_spec_projection_packet_v235_reference.json",
        )
    )
    packet_row = payload["projection_packet_rows"][0]
    packet_row["spec_review_checklist_rows"] = [
        row
        for row in packet_row["spec_review_checklist_rows"]
        if row["check_kind"] == "validation_evidence_check"
    ]
    packet_row["implementation_spec_quality_gate_rows"][0]["required_check_refs"] = [
        packet_row["spec_review_checklist_rows"][0]["review_check_ref"]
    ]

    with pytest.raises(ValidationError, match="complete review checklist"):
        RepoImplementationSpecProjectionPacket.model_validate(payload)
