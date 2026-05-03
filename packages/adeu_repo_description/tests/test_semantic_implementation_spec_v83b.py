from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_ARTIFACT_OBLIGATION_MAP_SCHEMA,
    REPO_INTENT_EDGE_DECOMPOSITION_SCHEMA,
    REPO_SEMANTIC_DRIFT_AMBIGUITY_REGISTER_SCHEMA,
    RepoArtifactObligationMap,
    RepoIntentEdgeDecomposition,
    RepoIntentNonImplementationGuardrail,
    RepoIntentSourceIndex,
    RepoSemanticDriftAmbiguityRegister,
    RepoSemanticIntentContract,
    derive_v83b_semantic_edge_obligation_bundle,
    validate_v83b_semantic_edge_obligation_bundle,
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


def _v83b_edge_decomposition(
    name: str = "repo_intent_edge_decomposition_v234_reference.json",
) -> RepoIntentEdgeDecomposition:
    return RepoIntentEdgeDecomposition.model_validate(_load_fixture("vnext_plus234", name))


def _v83b_obligation_map(
    name: str = "repo_artifact_obligation_map_v234_reference.json",
) -> RepoArtifactObligationMap:
    return RepoArtifactObligationMap.model_validate(_load_fixture("vnext_plus234", name))


def _v83b_drift_register(
    name: str = "repo_semantic_drift_ambiguity_register_v234_reference.json",
) -> RepoSemanticDriftAmbiguityRegister:
    return RepoSemanticDriftAmbiguityRegister.model_validate(_load_fixture("vnext_plus234", name))


def _drift_register_for_obligation_map(
    obligation_map: RepoArtifactObligationMap,
) -> RepoSemanticDriftAmbiguityRegister:
    payload = deepcopy(
        _load_fixture(
            "vnext_plus234",
            "repo_semantic_drift_ambiguity_register_v234_reference.json",
        )
    )
    payload["artifact_obligation_map_id"] = obligation_map.artifact_obligation_map_id
    payload["semantic_drift_ambiguity_register_id"] = _surface_id(
        "repo_semantic_drift_ambiguity_register",
        payload["schema"],
        payload,
        "semantic_drift_ambiguity_register_id",
    )
    return RepoSemanticDriftAmbiguityRegister.model_validate(payload)


def _validate_reference_bundle_with(
    *,
    edge_decomposition: RepoIntentEdgeDecomposition | None = None,
    obligation_map: RepoArtifactObligationMap | None = None,
    drift_register: RepoSemanticDriftAmbiguityRegister | None = None,
) -> None:
    resolved_obligation_map = (
        obligation_map if obligation_map is not None else _v83b_obligation_map()
    )
    validate_v83b_semantic_edge_obligation_bundle(
        intent_source_index=_v83a_source_index(),
        semantic_intent_contract=_v83a_contract(),
        intent_non_implementation_guardrail=_v83a_guardrail(),
        intent_edge_decomposition=(
            edge_decomposition if edge_decomposition is not None else _v83b_edge_decomposition()
        ),
        artifact_obligation_map=resolved_obligation_map,
        semantic_drift_ambiguity_register=(
            drift_register
            if drift_register is not None
            else (
                _drift_register_for_obligation_map(resolved_obligation_map)
                if obligation_map is not None
                else _v83b_drift_register()
            )
        ),
    )


def test_v234_reference_bundle_validates() -> None:
    edge_decomposition = _v83b_edge_decomposition()
    obligation_map = _v83b_obligation_map()
    drift_register = _v83b_drift_register()

    assert edge_decomposition.schema == REPO_INTENT_EDGE_DECOMPOSITION_SCHEMA
    assert obligation_map.schema == REPO_ARTIFACT_OBLIGATION_MAP_SCHEMA
    assert drift_register.schema == REPO_SEMANTIC_DRIFT_AMBIGUITY_REGISTER_SCHEMA
    edge_row = edge_decomposition.edge_decomposition_rows[0]
    assert {relation.relation_kind for relation in edge_row.semantic_relation_rows}.issuperset(
        {
            "acceptance_requires",
            "authority_requires",
            "non_goal_of",
            "realizes",
            "validation_requires",
        }
    )
    assert {validation.validation_kind for validation in edge_row.validation_need_rows}.issuperset(
        {
            "positive_fixture",
            "reject_fixture",
            "schema_validation",
            "semantic_review",
            "validator_behavior",
        }
    )
    assert {
        drift.drift_kind for drift in drift_register.drift_register_rows[0].drift_or_ambiguity_rows
    } == {
        "direct_oai_runtime_scope_drift",
        "future_family_pressure_unclassified",
        "morphic_ux_scope_drift",
    }

    _validate_reference_bundle_with(
        edge_decomposition=edge_decomposition,
        obligation_map=obligation_map,
        drift_register=drift_register,
    )


def test_v234_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_intent_edge_decomposition.v1.json").validate(
        _load_fixture("vnext_plus234", "repo_intent_edge_decomposition_v234_reference.json")
    )
    _schema_validator("repo_artifact_obligation_map.v1.json").validate(
        _load_fixture("vnext_plus234", "repo_artifact_obligation_map_v234_reference.json")
    )
    _schema_validator("repo_semantic_drift_ambiguity_register.v1.json").validate(
        _load_fixture(
            "vnext_plus234",
            "repo_semantic_drift_ambiguity_register_v234_reference.json",
        )
    )


def test_v234_derivation_helper_matches_reference_fixtures() -> None:
    _, _, _, edge_decomposition, obligation_map, drift_register = (
        derive_v83b_semantic_edge_obligation_bundle(repo_root=_repo_root())
    )

    assert edge_decomposition.model_dump(mode="json") == _load_fixture(
        "vnext_plus234",
        "repo_intent_edge_decomposition_v234_reference.json",
    )
    assert obligation_map.model_dump(mode="json") == _load_fixture(
        "vnext_plus234",
        "repo_artifact_obligation_map_v234_reference.json",
    )
    assert drift_register.model_dump(mode="json") == _load_fixture(
        "vnext_plus234",
        "repo_semantic_drift_ambiguity_register_v234_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_semantic_implementation_spec_v234_reject_edge_without_intent_contract_ref.json",
            RepoIntentEdgeDecomposition,
            "at least 1 item",
        ),
        (
            "repo_semantic_implementation_spec_v234_reject_semantic_object_without_source_refs.json",
            RepoIntentEdgeDecomposition,
            "at least 1 item",
        ),
        (
            "repo_semantic_implementation_spec_v234_reject_future_projection_packet_ref.json",
            RepoIntentEdgeDecomposition,
            "Extra inputs are not permitted",
        ),
        (
            "repo_semantic_implementation_spec_v234_reject_morphic_runtime_claim.json",
            RepoIntentEdgeDecomposition,
            "limitation_note may not carry V83-B downstream authority",
        ),
        (
            "repo_semantic_implementation_spec_v234_reject_obligation_without_semantic_edge_refs.json",
            RepoArtifactObligationMap,
            "at least 1 item",
        ),
        (
            "repo_semantic_implementation_spec_v234_reject_broad_target_surface.json",
            RepoArtifactObligationMap,
            "bounded target surfaces",
        ),
        (
            "repo_semantic_implementation_spec_v234_reject_drift_blocker_hidden.json",
            RepoSemanticDriftAmbiguityRegister,
            "blocking drift cannot be hidden",
        ),
        (
            "repo_semantic_implementation_spec_v234_reject_drift_resolved_by_v83b.json",
            RepoSemanticDriftAmbiguityRegister,
            "Input should be",
        ),
    ],
)
def test_v234_model_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[BaseModel],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus234", fixture_name))


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_semantic_implementation_spec_v234_reject_non_goal_as_required_change.json",
            "non-goals cannot become implementation obligations",
        ),
        (
            "repo_semantic_implementation_spec_v234_reject_authority_boundary_as_code_permission.json",
            "authority boundaries cannot become code permissions",
        ),
    ],
)
def test_v234_bundle_rejects_semantic_laundering(
    fixture_name: str,
    match: str,
) -> None:
    obligation_map = _v83b_obligation_map(fixture_name)

    with pytest.raises(ValueError, match=match):
        _validate_reference_bundle_with(obligation_map=obligation_map)


def test_v234_bundle_rejects_obligation_map_parent_contract_mismatch() -> None:
    payload = deepcopy(
        _load_fixture("vnext_plus234", "repo_artifact_obligation_map_v234_reference.json")
    )
    payload["semantic_intent_contract_id"] = "repo_semantic_intent_contract:v83a:mismatched"
    payload["artifact_obligation_map_id"] = _surface_id(
        "repo_artifact_obligation_map",
        payload["schema"],
        payload,
        "artifact_obligation_map_id",
    )
    obligation_map = RepoArtifactObligationMap.model_validate(payload)

    with pytest.raises(
        ValueError,
        match="artifact obligation map must reference released V83-A intent contract",
    ):
        _validate_reference_bundle_with(obligation_map=obligation_map)


def test_v234_bundle_rejects_drift_register_parent_edge_mismatch() -> None:
    payload = deepcopy(
        _load_fixture(
            "vnext_plus234",
            "repo_semantic_drift_ambiguity_register_v234_reference.json",
        )
    )
    payload["intent_edge_decomposition_id"] = "repo_intent_edge_decomposition:v83b:mismatched"
    payload["semantic_drift_ambiguity_register_id"] = _surface_id(
        "repo_semantic_drift_ambiguity_register",
        payload["schema"],
        payload,
        "semantic_drift_ambiguity_register_id",
    )
    drift_register = RepoSemanticDriftAmbiguityRegister.model_validate(payload)

    with pytest.raises(ValueError, match="drift register must reference edge decomposition"):
        _validate_reference_bundle_with(drift_register=drift_register)


def test_v234_bundle_rejects_drift_register_parent_contract_mismatch() -> None:
    payload = deepcopy(
        _load_fixture(
            "vnext_plus234",
            "repo_semantic_drift_ambiguity_register_v234_reference.json",
        )
    )
    payload["semantic_intent_contract_id"] = "repo_semantic_intent_contract:v83a:mismatched"
    payload["semantic_drift_ambiguity_register_id"] = _surface_id(
        "repo_semantic_drift_ambiguity_register",
        payload["schema"],
        payload,
        "semantic_drift_ambiguity_register_id",
    )
    drift_register = RepoSemanticDriftAmbiguityRegister.model_validate(payload)

    with pytest.raises(
        ValueError,
        match="drift register must reference released V83-A intent contract",
    ):
        _validate_reference_bundle_with(drift_register=drift_register)
