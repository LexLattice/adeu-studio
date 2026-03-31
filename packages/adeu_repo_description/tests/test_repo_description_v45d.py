from __future__ import annotations

import json
from collections import Counter
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_TEST_INTENT_MATRIX_SCHEMA,
    RepoTestIntentMatrix,
    compute_repo_test_intent_matrix_id,
    default_v45b_source_paths,
    default_v45d_source_paths,
    derive_v45b_repo_symbol_catalog_and_dependency_graph,
    derive_v45d_repo_test_intent_matrix,
    validate_repo_test_intent_matrix_against_v45b,
)
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v103_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / "vnext_plus103"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v103(name: str) -> dict[str, Any]:
    return _load_json(_v103_root() / name)


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_repo_description" / "schema" / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v103_reference_test_intent_matrix_replays_and_validates() -> None:
    accepted_matrix = _load_v103("repo_test_intent_matrix_v103_reference.json")
    validated_matrix = RepoTestIntentMatrix.model_validate(accepted_matrix)

    derived_matrix = derive_v45d_repo_test_intent_matrix(
        source_paths=default_v45d_source_paths(),
        snapshot_validity_posture=accepted_matrix["snapshot_validity_posture"],
    )
    assert derived_matrix == accepted_matrix

    bound_symbol_catalog, bound_dependency_graph = (
        derive_v45b_repo_symbol_catalog_and_dependency_graph(
            source_paths=default_v45b_source_paths(),
            snapshot_validity_posture=accepted_matrix["snapshot_validity_posture"],
        )
    )
    pair_matrix, _symbol_catalog, _dependency_graph = (
        validate_repo_test_intent_matrix_against_v45b(
            test_intent_matrix_payload=accepted_matrix,
            symbol_catalog_payload=bound_symbol_catalog,
            dependency_graph_payload=bound_dependency_graph,
        )
    )

    assert validated_matrix.schema == REPO_TEST_INTENT_MATRIX_SCHEMA
    assert pair_matrix == validated_matrix


def test_v103_test_intent_matrix_id_is_deterministic() -> None:
    payload = _load_v103("repo_test_intent_matrix_v103_reference.json")
    without_id = deepcopy(payload)
    without_id.pop("repo_test_intent_matrix_id")
    assert (
        compute_repo_test_intent_matrix_id(without_id)
        == payload["repo_test_intent_matrix_id"]
    )


def test_v103_exported_schema_accepts_reference_fixture() -> None:
    _schema_validator("repo_test_intent_matrix.v1.json").validate(
        _load_v103("repo_test_intent_matrix_v103_reference.json")
    )


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_test_intent_matrix_v103_reject_missing_snapshot_identity.json",
            "Field required",
        ),
        (
            "repo_test_intent_matrix_v103_reject_claim_without_observed_assertion_surface.json",
            "Field required",
        ),
        (
            "repo_test_intent_matrix_v103_reject_guarded_surface_ref_without_boundary_typing.json",
            "guarded_surface_ref_value must use the external: or out_of_scope: prefix",
        ),
        (
            "repo_test_intent_matrix_v103_reject_source_artifact_ref_outside_test_source_set.json",
            "source_artifact_refs must resolve inside test_source_set",
        ),
        (
            "repo_test_intent_matrix_v103_reject_authority_laundering_release_gating.json",
            (
                "matrix_scope may not carry release-gating, optimization, scheduling, or "
                "mutation entitlement claims"
            ),
        ),
    ],
)
def test_v103_rejects_invalid_reference_fixtures(fixture_name: str, match: str) -> None:
    with pytest.raises(ValidationError, match=match):
        RepoTestIntentMatrix.model_validate(_load_v103(fixture_name))


def test_v103_rejects_pair_with_mismatched_v45b_snapshot_binding() -> None:
    payload = _load_v103(
        "repo_test_intent_matrix_pair_v103_reject_mismatched_v45b_snapshot_binding.json"
    )

    with pytest.raises(
        ValueError,
        match="repo_test_intent_matrix must share repo_snapshot_id with V45-B",
    ):
        validate_repo_test_intent_matrix_against_v45b(
            test_intent_matrix_payload=payload["test_intent_matrix"],
            symbol_catalog_payload=payload["symbol_catalog"],
            dependency_graph_payload=payload["dependency_graph"],
        )


def test_v103_reference_fixture_preserves_row_granularity_and_pytest_raises_rows() -> None:
    payload = _load_v103("repo_test_intent_matrix_v103_reference.json")
    rows = payload["test_intent_entries"]
    row_counts = Counter(row["test_ref"] for row in rows)

    pytest_raises_rows = [
        row
        for row in rows
        if row["observed_assertion_surface"]["assertion_surface_kind"] == "pytest_raises"
    ]

    assert any(count > 1 for count in row_counts.values())
    assert pytest_raises_rows
    assert any(
        row["guarded_surface_ref"]["guarded_surface_ref_kind"] == "internal_symbol"
        for row in pytest_raises_rows
    )
