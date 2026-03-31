from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_DEPENDENCY_GRAPH_SCHEMA,
    REPO_SYMBOL_CATALOG_SCHEMA,
    RepoDependencyGraph,
    RepoSymbolCatalog,
    compute_repo_dependency_graph_id,
    compute_repo_symbol_catalog_id,
    default_v45b_source_paths,
    derive_v45b_repo_symbol_catalog_and_dependency_graph,
    validate_repo_symbol_catalog_dependency_graph_pair,
)
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v101_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / "vnext_plus101"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v101(name: str) -> dict[str, Any]:
    return _load_json(_v101_root() / name)


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_repo_description" / "schema" / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v101_reference_symbol_catalog_and_dependency_graph_replay_and_validate() -> None:
    accepted_catalog = _load_v101("repo_symbol_catalog_v101_reference.json")
    accepted_graph = _load_v101("repo_dependency_graph_v101_reference.json")

    validated_catalog = RepoSymbolCatalog.model_validate(accepted_catalog)
    validated_graph = RepoDependencyGraph.model_validate(accepted_graph)
    pair_catalog, pair_graph = validate_repo_symbol_catalog_dependency_graph_pair(
        symbol_catalog_payload=accepted_catalog,
        dependency_graph_payload=accepted_graph,
    )

    assert validated_catalog.schema == REPO_SYMBOL_CATALOG_SCHEMA
    assert validated_graph.schema == REPO_DEPENDENCY_GRAPH_SCHEMA
    assert pair_catalog == validated_catalog
    assert pair_graph == validated_graph

    derived_catalog, derived_graph = derive_v45b_repo_symbol_catalog_and_dependency_graph(
        source_paths=default_v45b_source_paths(),
        snapshot_validity_posture=accepted_catalog["snapshot_validity_posture"],
    )
    assert derived_catalog == accepted_catalog
    assert derived_graph == accepted_graph


def test_v101_symbol_catalog_id_is_deterministic() -> None:
    payload = _load_v101("repo_symbol_catalog_v101_reference.json")
    without_id = deepcopy(payload)
    without_id.pop("repo_symbol_catalog_id")
    assert compute_repo_symbol_catalog_id(without_id) == payload["repo_symbol_catalog_id"]


def test_v101_dependency_graph_id_is_deterministic() -> None:
    payload = _load_v101("repo_dependency_graph_v101_reference.json")
    without_id = deepcopy(payload)
    without_id.pop("repo_dependency_graph_id")
    assert compute_repo_dependency_graph_id(without_id) == payload["repo_dependency_graph_id"]


def test_v101_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_symbol_catalog.v1.json").validate(
        _load_v101("repo_symbol_catalog_v101_reference.json")
    )
    _schema_validator("repo_dependency_graph.v1.json").validate(
        _load_v101("repo_dependency_graph_v101_reference.json")
    )


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_symbol_catalog_v101_reject_missing_snapshot_identity.json",
            "Field required",
        ),
        (
            "repo_symbol_catalog_v101_reject_duplicate_symbol_identity.json",
            "symbol_entries symbol_id values must be unique",
        ),
        (
            "repo_symbol_catalog_v101_reject_refactor_entitlement_laundering.json",
            "graph_scope may not carry refactor, scheduling, or mutation entitlement claims",
        ),
    ],
)
def test_v101_rejects_invalid_symbol_catalog_fixtures(fixture_name: str, match: str) -> None:
    with pytest.raises(ValidationError, match=match):
        RepoSymbolCatalog.model_validate(_load_v101(fixture_name))


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_dependency_graph_v101_reject_missing_dependency_posture.json",
            "Field required",
        ),
        (
            "repo_dependency_graph_v101_reject_out_of_scope_endpoint_without_boundary_typing.json",
            "to_ref must use the out_of_scope: prefix",
        ),
    ],
)
def test_v101_rejects_invalid_dependency_graph_fixtures(fixture_name: str, match: str) -> None:
    with pytest.raises(ValidationError, match=match):
        RepoDependencyGraph.model_validate(_load_v101(fixture_name))


def test_v101_rejects_dangling_symbol_ref_when_graph_is_paired_to_catalog() -> None:
    accepted_catalog = _load_v101("repo_symbol_catalog_v101_reference.json")
    reject_graph = _load_v101("repo_dependency_graph_v101_reject_dangling_symbol_ref.json")

    with pytest.raises(
        ValueError,
        match="dependency edge to_ref must resolve against repo_symbol_catalog",
    ):
        validate_repo_symbol_catalog_dependency_graph_pair(
            symbol_catalog_payload=accepted_catalog,
            dependency_graph_payload=reject_graph,
        )


def test_v101_rejects_pair_with_mismatched_snapshot_source_identity() -> None:
    payload = _load_v101(
        "repo_symbol_dependency_pair_v101_reject_mismatched_snapshot_source_identity.json"
    )

    with pytest.raises(
        ValueError,
        match="symbol catalog and dependency graph must share repo_snapshot_id",
    ):
        validate_repo_symbol_catalog_dependency_graph_pair(
            symbol_catalog_payload=payload["symbol_catalog"],
            dependency_graph_payload=payload["dependency_graph"],
        )
