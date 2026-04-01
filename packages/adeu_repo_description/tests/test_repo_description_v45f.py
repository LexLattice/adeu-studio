from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_DESCRIPTIVE_NORMATIVE_BINDING_FRAME_SCHEMA,
    RepoDescriptiveNormativeBindingFrame,
    compute_repo_arc_dependency_register_id,
    compute_repo_descriptive_normative_binding_frame_id,
    default_v45f_source_paths,
    derive_v45a_repo_description_bundle,
    derive_v45b_repo_symbol_catalog_and_dependency_graph,
    derive_v45d_repo_test_intent_matrix,
    derive_v45e_repo_optimization_register,
    derive_v45f_repo_descriptive_normative_binding_frame,
    validate_repo_descriptive_normative_binding_frame_against_v45_baseline,
)
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v105_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / "vnext_plus105"


def _v102_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / "vnext_plus102"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v105(name: str) -> dict[str, Any]:
    return _load_json(_v105_root() / name)


def _load_v102(name: str) -> dict[str, Any]:
    return _load_json(_v102_root() / name)


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_repo_description" / "schema" / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v105_reference_binding_frame_validates_as_historical_baseline() -> None:
    accepted_frame = _load_v105("repo_descriptive_normative_binding_frame_v105_reference.json")
    validated_frame = RepoDescriptiveNormativeBindingFrame.model_validate(accepted_frame)

    assert validated_frame.schema == REPO_DESCRIPTIVE_NORMATIVE_BINDING_FRAME_SCHEMA


def test_v45f_current_binding_frame_derivation_validates_against_current_baseline() -> None:
    derived_frame = derive_v45f_repo_descriptive_normative_binding_frame(
        source_paths=default_v45f_source_paths(),
        snapshot_validity_posture="snapshot_bound_current",
    )
    validated_frame = RepoDescriptiveNormativeBindingFrame.model_validate(derived_frame)

    bound_schema_registry, bound_entity_catalog = derive_v45a_repo_description_bundle()
    bound_symbol_catalog, bound_dependency_graph = (
        derive_v45b_repo_symbol_catalog_and_dependency_graph()
    )
    bound_arc_dependency_register = _load_v102("repo_arc_dependency_register_v102_reference.json")
    bound_test_intent_matrix = derive_v45d_repo_test_intent_matrix(
        bound_symbol_catalog_payload=bound_symbol_catalog,
        bound_dependency_graph_payload=bound_dependency_graph,
    )
    bound_optimization_register = derive_v45e_repo_optimization_register(
        bound_entity_catalog_payload=bound_entity_catalog,
        bound_schema_family_registry_payload=bound_schema_registry,
        bound_symbol_catalog_payload=bound_symbol_catalog,
        bound_dependency_graph_payload=bound_dependency_graph,
        bound_test_intent_matrix_payload=bound_test_intent_matrix,
        bound_arc_dependency_register_payload=bound_arc_dependency_register,
    )

    (
        pair_frame,
        _entity_catalog,
        _schema_family_registry,
        _symbol_catalog,
        _dependency_graph,
        _arc_dependency_register,
        _test_intent_matrix,
        _optimization_register,
    ) = validate_repo_descriptive_normative_binding_frame_against_v45_baseline(
        binding_frame_payload=derived_frame,
        entity_catalog_payload=bound_entity_catalog,
        schema_family_registry_payload=bound_schema_registry,
        symbol_catalog_payload=bound_symbol_catalog,
        dependency_graph_payload=bound_dependency_graph,
        arc_dependency_register_payload=bound_arc_dependency_register,
        test_intent_matrix_payload=bound_test_intent_matrix,
        optimization_register_payload=bound_optimization_register,
    )

    assert pair_frame == validated_frame


def test_v105_binding_frame_id_is_deterministic() -> None:
    payload = _load_v105("repo_descriptive_normative_binding_frame_v105_reference.json")
    without_id = deepcopy(payload)
    without_id.pop("repo_descriptive_normative_binding_frame_id")
    assert compute_repo_descriptive_normative_binding_frame_id(without_id) == payload[
        "repo_descriptive_normative_binding_frame_id"
    ]


def test_v105_exported_schema_accepts_reference_fixture() -> None:
    _schema_validator("repo_descriptive_normative_binding_frame.v1.json").validate(
        _load_v105("repo_descriptive_normative_binding_frame_v105_reference.json")
    )


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_descriptive_normative_binding_frame_v105_reject_missing_promotion_law_posture.json",
            "Field required",
        ),
        (
            "repo_descriptive_normative_binding_frame_v105_reject_missing_bound_optimization_register_ref.json",
            "Field required",
        ),
        (
            "repo_descriptive_normative_binding_frame_v105_reject_source_artifact_ref_outside_source_set.json",
            "binding_entries source_artifact_refs must resolve inside source_set",
        ),
        (
            "repo_descriptive_normative_binding_frame_v105_reject_authority_laundering_from_descriptive_artifact_alone.json",
            "non-advisory binding rows must name a separate authority_source_kind",
        ),
        (
            "repo_descriptive_normative_binding_frame_v105_reject_recursive_governance_execution_entitlement.json",
            "recursive_governance_consumer requires separate_normative_authority_required",
        ),
    ],
)
def test_v105_rejects_invalid_reference_fixtures(fixture_name: str, match: str) -> None:
    payload = _load_v105(fixture_name)
    with pytest.raises(ValidationError, match=match):
        RepoDescriptiveNormativeBindingFrame.model_validate(payload)


def test_v105_rejects_descriptive_input_ref_outside_bound_baseline() -> None:
    payload = _load_v105(
        "repo_descriptive_normative_binding_frame_v105_reject_descriptive_input_ref_outside_bound_baseline.json"
    )
    bound_schema_registry, bound_entity_catalog = derive_v45a_repo_description_bundle()
    bound_symbol_catalog, bound_dependency_graph = (
        derive_v45b_repo_symbol_catalog_and_dependency_graph()
    )
    bound_arc_dependency_register = _load_v102("repo_arc_dependency_register_v102_reference.json")
    bound_test_intent_matrix = derive_v45d_repo_test_intent_matrix(
        bound_symbol_catalog_payload=bound_symbol_catalog,
        bound_dependency_graph_payload=bound_dependency_graph,
    )
    bound_optimization_register = derive_v45e_repo_optimization_register(
        bound_entity_catalog_payload=bound_entity_catalog,
        bound_schema_family_registry_payload=bound_schema_registry,
        bound_symbol_catalog_payload=bound_symbol_catalog,
        bound_dependency_graph_payload=bound_dependency_graph,
        bound_test_intent_matrix_payload=bound_test_intent_matrix,
        bound_arc_dependency_register_payload=bound_arc_dependency_register,
    )

    with pytest.raises(
        ValueError,
        match=(
            "repo_descriptive_normative_binding_frame descriptive_input_ref must resolve "
            "against the bound V45-A through V45-E descriptive baseline"
        ),
    ):
        validate_repo_descriptive_normative_binding_frame_against_v45_baseline(
            binding_frame_payload=payload,
            entity_catalog_payload=bound_entity_catalog,
            schema_family_registry_payload=bound_schema_registry,
            symbol_catalog_payload=bound_symbol_catalog,
            dependency_graph_payload=bound_dependency_graph,
            arc_dependency_register_payload=bound_arc_dependency_register,
            test_intent_matrix_payload=bound_test_intent_matrix,
            optimization_register_payload=bound_optimization_register,
        )


def test_v105_reference_fixture_binds_v45c_explicitly() -> None:
    payload = _load_v105("repo_descriptive_normative_binding_frame_v105_reference.json")
    assert payload["bound_arc_dependency_register_ref"].startswith(
        "repo_arc_dependency_register_"
    )


def test_v45f_propagates_historical_snapshot_validity_to_nested_derivations() -> None:
    bound_schema_registry, bound_entity_catalog = derive_v45a_repo_description_bundle(
        snapshot_validity_posture="snapshot_bound_historical"
    )
    bound_symbol_catalog, bound_dependency_graph = (
        derive_v45b_repo_symbol_catalog_and_dependency_graph(
            snapshot_validity_posture="snapshot_bound_historical"
        )
    )
    bound_arc_dependency_register = deepcopy(
        _load_v102("repo_arc_dependency_register_v102_reference.json")
    )
    bound_arc_dependency_register["snapshot_validity_posture"] = "snapshot_bound_historical"
    bound_arc_dependency_register["repo_arc_dependency_register_id"] = (
        compute_repo_arc_dependency_register_id(
            {
                key: value
                for key, value in bound_arc_dependency_register.items()
                if key != "repo_arc_dependency_register_id"
            }
        )
    )
    bound_test_intent_matrix = derive_v45d_repo_test_intent_matrix(
        bound_symbol_catalog_payload=bound_symbol_catalog,
        bound_dependency_graph_payload=bound_dependency_graph,
        snapshot_validity_posture="snapshot_bound_historical",
    )
    bound_optimization_register = derive_v45e_repo_optimization_register(
        bound_entity_catalog_payload=bound_entity_catalog,
        bound_schema_family_registry_payload=bound_schema_registry,
        bound_symbol_catalog_payload=bound_symbol_catalog,
        bound_dependency_graph_payload=bound_dependency_graph,
        bound_test_intent_matrix_payload=bound_test_intent_matrix,
        bound_arc_dependency_register_payload=bound_arc_dependency_register,
        snapshot_validity_posture="snapshot_bound_historical",
    )

    frame = derive_v45f_repo_descriptive_normative_binding_frame(
        source_paths=default_v45f_source_paths(),
        bound_entity_catalog_payload=bound_entity_catalog,
        bound_schema_family_registry_payload=bound_schema_registry,
        bound_symbol_catalog_payload=bound_symbol_catalog,
        bound_dependency_graph_payload=bound_dependency_graph,
        bound_arc_dependency_register_payload=bound_arc_dependency_register,
        bound_test_intent_matrix_payload=bound_test_intent_matrix,
        bound_optimization_register_payload=bound_optimization_register,
        snapshot_validity_posture="snapshot_bound_historical",
    )

    assert frame["snapshot_validity_posture"] == "snapshot_bound_historical"
