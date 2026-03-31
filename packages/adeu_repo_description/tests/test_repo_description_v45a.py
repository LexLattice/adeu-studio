from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    RECONSTRUCTION_EQUIVALENCE_MODE,
    REPO_ENTITY_CATALOG_SCHEMA,
    REPO_SCHEMA_FAMILY_REGISTRY_SCHEMA,
    SCHEMA_VISIBLE_ENTITY_COVERAGE_MODE,
    RepoEntityCatalog,
    RepoSchemaFamilyRegistry,
    compute_repo_entity_catalog_id,
    compute_repo_schema_family_registry_id,
    derive_v45a_repo_entity_catalog,
    derive_v45a_repo_schema_family_registry,
)
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v99_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / "vnext_plus99"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v99(name: str) -> dict[str, Any]:
    return _load_json(_v99_root() / name)


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_repo_description" / "schema" / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v99_reference_registry_fixture_replays_and_validates() -> None:
    accepted_registry = _load_v99("repo_schema_family_registry_v99_reference.json")
    validated = RepoSchemaFamilyRegistry.model_validate(accepted_registry)
    assert validated.schema == REPO_SCHEMA_FAMILY_REGISTRY_SCHEMA
    assert validated.reconstruction_equivalence_mode == RECONSTRUCTION_EQUIVALENCE_MODE

    derived_registry = derive_v45a_repo_schema_family_registry(
        source_paths=accepted_registry["source_set"]["source_paths"],
        snapshot_validity_posture=accepted_registry["snapshot_validity_posture"],
    )
    assert derived_registry == accepted_registry


def test_v99_reference_entity_fixture_replays_and_validates() -> None:
    accepted_registry = _load_v99("repo_schema_family_registry_v99_reference.json")
    accepted_catalog = _load_v99("repo_entity_catalog_v99_reference.json")

    validated = RepoEntityCatalog.model_validate(accepted_catalog)
    assert validated.schema == REPO_ENTITY_CATALOG_SCHEMA
    assert validated.entity_coverage_mode == SCHEMA_VISIBLE_ENTITY_COVERAGE_MODE

    derived_catalog = derive_v45a_repo_entity_catalog(schema_family_registry=accepted_registry)
    assert derived_catalog == accepted_catalog


def test_v99_registry_id_is_deterministic() -> None:
    payload = _load_v99("repo_schema_family_registry_v99_reference.json")
    without_id = deepcopy(payload)
    without_id.pop("schema_family_registry_id")
    assert (
        compute_repo_schema_family_registry_id(without_id) == payload["schema_family_registry_id"]
    )


def test_v99_entity_catalog_id_is_deterministic() -> None:
    payload = _load_v99("repo_entity_catalog_v99_reference.json")
    without_id = deepcopy(payload)
    without_id.pop("repo_entity_catalog_id")
    assert compute_repo_entity_catalog_id(without_id) == payload["repo_entity_catalog_id"]


def test_v99_exported_schema_accepts_reference_fixtures() -> None:
    _schema_validator("repo_schema_family_registry.v1.json").validate(
        _load_v99("repo_schema_family_registry_v99_reference.json")
    )
    _schema_validator("repo_entity_catalog.v1.json").validate(
        _load_v99("repo_entity_catalog_v99_reference.json")
    )


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_schema_family_registry_v99_reject_missing_snapshot_identity.json",
            "Field required",
        ),
        (
            "repo_schema_family_registry_v99_reject_unresolved_primary_carrier_class.json",
            "Input should be",
        ),
        (
            "repo_schema_family_registry_v99_reject_naming_only_role_form_classification.json",
            "naming-only role-form classification is forbidden",
        ),
        (
            "repo_schema_family_registry_v99_reject_settled_posture_without_adjudication_support.json",
            "settled posture requires explicit adjudicator_ref support",
        ),
        (
            "repo_schema_family_registry_v99_reject_precedence_contradiction.json",
            "precedence contradiction",
        ),
        (
            "repo_entity_catalog_v99_reject_missing_taxonomy_axis.json",
            "semantic_role",
        ),
        (
            "repo_schema_family_registry_v99_reject_non_round_tripping_reconstruction.json",
            "round-trip under canonical normalized semantic equivalence",
        ),
    ],
)
def test_v99_rejects_invalid_reference_fixtures(fixture_name: str, match: str) -> None:
    payload = _load_v99(fixture_name)
    if fixture_name.startswith("repo_entity_catalog"):
        with pytest.raises(ValidationError, match=match):
            RepoEntityCatalog.model_validate(payload)
    else:
        with pytest.raises(ValidationError, match=match):
            RepoSchemaFamilyRegistry.model_validate(payload)
