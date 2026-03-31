from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_ARC_DEPENDENCY_REGISTER_SCHEMA,
    RepoArcDependencyRegister,
    compute_repo_arc_dependency_register_id,
    default_v45c_source_paths,
    derive_v45c_repo_arc_dependency_register,
)
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v100_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / "vnext_plus100"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v100(name: str) -> dict[str, Any]:
    return _load_json(_v100_root() / name)


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_repo_description" / "schema" / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v100_reference_dependency_register_fixture_replays_and_validates() -> None:
    accepted_register = _load_v100("repo_arc_dependency_register_v100_reference.json")
    validated = RepoArcDependencyRegister.model_validate(accepted_register)
    assert validated.schema == REPO_ARC_DEPENDENCY_REGISTER_SCHEMA

    derived_register = derive_v45c_repo_arc_dependency_register(
        source_paths=default_v45c_source_paths(),
        snapshot_validity_posture=accepted_register["snapshot_validity_posture"],
    )
    assert derived_register == accepted_register


def test_v100_dependency_register_id_is_deterministic() -> None:
    payload = _load_v100("repo_arc_dependency_register_v100_reference.json")
    without_id = deepcopy(payload)
    without_id.pop("repo_arc_dependency_register_id")
    assert (
        compute_repo_arc_dependency_register_id(without_id)
        == payload["repo_arc_dependency_register_id"]
    )


def test_v100_exported_schema_accepts_reference_fixture() -> None:
    _schema_validator("repo_arc_dependency_register.v1.json").validate(
        _load_v100("repo_arc_dependency_register_v100_reference.json")
    )


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_arc_dependency_register_v100_reject_missing_snapshot_identity.json",
            "Field required",
        ),
        (
            "repo_arc_dependency_register_v100_reject_dangling_dependency_target_arc.json",
            "known open_arc_entries arc_id",
        ),
        (
            "repo_arc_dependency_register_v100_reject_duplicate_edge_identity.json",
            "dependency_edges edge_id values must be unique",
        ),
        (
            "repo_arc_dependency_register_v100_reject_unresolved_blocker_ready_posture.json",
            "ready/deferred readiness_posture may not coexist with unresolved hard blockers",
        ),
        (
            "repo_arc_dependency_register_v100_reject_authority_laundering_scheduling_entitlement.json",
            "register_scope may not carry scheduling or mutation entitlement claims",
        ),
    ],
)
def test_v100_rejects_invalid_reference_fixtures(fixture_name: str, match: str) -> None:
    payload = _load_v100(fixture_name)
    with pytest.raises(ValidationError, match=match):
        RepoArcDependencyRegister.model_validate(payload)
