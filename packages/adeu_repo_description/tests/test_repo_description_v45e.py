from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_OPTIMIZATION_REGISTER_SCHEMA,
    RepoOptimizationRegister,
    compute_repo_optimization_register_id,
    default_v45e_source_paths,
    derive_v45a_repo_description_bundle,
    derive_v45b_repo_symbol_catalog_and_dependency_graph,
    derive_v45d_repo_test_intent_matrix,
    derive_v45e_repo_optimization_register,
    validate_repo_optimization_register_against_v45_baseline,
)
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v104_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / "vnext_plus104"


def _v102_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / "vnext_plus102"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v104(name: str) -> dict[str, Any]:
    return _load_json(_v104_root() / name)


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


def test_v104_reference_optimization_register_replays_and_validates() -> None:
    accepted_register = _load_v104("repo_optimization_register_v104_reference.json")
    validated_register = RepoOptimizationRegister.model_validate(accepted_register)

    derived_register = derive_v45e_repo_optimization_register(
        source_paths=default_v45e_source_paths(),
        snapshot_validity_posture=accepted_register["snapshot_validity_posture"],
    )
    assert derived_register == accepted_register

    bound_schema_registry, bound_entity_catalog = derive_v45a_repo_description_bundle()
    bound_symbol_catalog, bound_dependency_graph = (
        derive_v45b_repo_symbol_catalog_and_dependency_graph()
    )
    bound_test_intent_matrix = derive_v45d_repo_test_intent_matrix(
        bound_symbol_catalog_payload=bound_symbol_catalog,
        bound_dependency_graph_payload=bound_dependency_graph,
    )
    bound_arc_dependency_register = _load_v102("repo_arc_dependency_register_v102_reference.json")

    (
        pair_register,
        _entity_catalog,
        _schema_family_registry,
        _symbol_catalog,
        _dependency_graph,
        _test_intent_matrix,
    ) = validate_repo_optimization_register_against_v45_baseline(
        optimization_register_payload=accepted_register,
        entity_catalog_payload=bound_entity_catalog,
        schema_family_registry_payload=bound_schema_registry,
        symbol_catalog_payload=bound_symbol_catalog,
        dependency_graph_payload=bound_dependency_graph,
        test_intent_matrix_payload=bound_test_intent_matrix,
        arc_dependency_register_payload=bound_arc_dependency_register,
    )

    assert validated_register.schema == REPO_OPTIMIZATION_REGISTER_SCHEMA
    assert pair_register == validated_register


def test_v104_optimization_register_id_is_deterministic() -> None:
    payload = _load_v104("repo_optimization_register_v104_reference.json")
    without_id = deepcopy(payload)
    without_id.pop("repo_optimization_register_id")
    assert compute_repo_optimization_register_id(without_id) == payload[
        "repo_optimization_register_id"
    ]


def test_v104_exported_schema_accepts_reference_fixture() -> None:
    _schema_validator("repo_optimization_register.v1.json").validate(
        _load_v104("repo_optimization_register_v104_reference.json")
    )


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_optimization_register_v104_reject_missing_support_basis.json",
            "Field required",
        ),
        (
            "repo_optimization_register_v104_reject_source_artifact_ref_outside_source_set.json",
            "optimization_entries source_artifact_refs must resolve inside source_set",
        ),
        (
            "repo_optimization_register_v104_reject_cross_surface_cluster_without_member_carrier.json",
            "cross_surface_cluster finding_scope_kind requires at least two cluster_member_refs",
        ),
        (
            "repo_optimization_register_v104_reject_amendment_entitlement_laundering.json",
            "Input should be 'not_authorized_by_this_artifact'",
        ),
        (
            "repo_optimization_register_v104_reject_unresolved_finding_scope.json",
            "repo_optimization_register finding_scope must resolve against source_set",
        ),
    ],
)
def test_v104_rejects_invalid_reference_fixtures(fixture_name: str, match: str) -> None:
    payload = _load_v104(fixture_name)

    if fixture_name == "repo_optimization_register_v104_reject_unresolved_finding_scope.json":
        bound_schema_registry, bound_entity_catalog = derive_v45a_repo_description_bundle()
        bound_symbol_catalog, bound_dependency_graph = (
            derive_v45b_repo_symbol_catalog_and_dependency_graph()
        )
        bound_test_intent_matrix = derive_v45d_repo_test_intent_matrix(
            bound_symbol_catalog_payload=bound_symbol_catalog,
            bound_dependency_graph_payload=bound_dependency_graph,
        )
        bound_arc_dependency_register = _load_v102(
            "repo_arc_dependency_register_v102_reference.json"
        )
        with pytest.raises(ValueError, match=match):
            validate_repo_optimization_register_against_v45_baseline(
                optimization_register_payload=payload,
                entity_catalog_payload=bound_entity_catalog,
                schema_family_registry_payload=bound_schema_registry,
                symbol_catalog_payload=bound_symbol_catalog,
                dependency_graph_payload=bound_dependency_graph,
                test_intent_matrix_payload=bound_test_intent_matrix,
                arc_dependency_register_payload=bound_arc_dependency_register,
            )
        return

    with pytest.raises(ValidationError, match=match):
        RepoOptimizationRegister.model_validate(payload)


def test_v104_rejects_bundle_with_mismatched_bound_v45b_snapshot_identity() -> None:
    payload = _load_v104(
        "repo_optimization_register_bundle_v104_reject_bound_artifact_snapshot_scope_mismatch.json"
    )

    with pytest.raises(
        ValueError,
        match="repo_optimization_register must share repo_snapshot_id with V45-B",
    ):
        validate_repo_optimization_register_against_v45_baseline(
            optimization_register_payload=payload["optimization_register"],
            entity_catalog_payload=payload["entity_catalog"],
            schema_family_registry_payload=payload["schema_family_registry"],
            symbol_catalog_payload=payload["symbol_catalog"],
            dependency_graph_payload=payload["dependency_graph"],
            test_intent_matrix_payload=payload["test_intent_matrix"],
            arc_dependency_register_payload=payload["arc_dependency_register"],
        )


def test_v104_reference_fixture_contains_cluster_and_secondary_tags() -> None:
    payload = _load_v104("repo_optimization_register_v104_reference.json")
    cluster_rows = [
        row
        for row in payload["optimization_entries"]
        if row["finding_scope"]["finding_scope_kind"] == "cross_surface_cluster"
    ]

    assert cluster_rows
    assert all(row["finding_scope"]["cluster_member_refs"] for row in cluster_rows)
    assert any(row["secondary_compression_axes"] for row in payload["optimization_entries"])
    assert any(row["secondary_support_basis_tags"] for row in payload["optimization_entries"])
