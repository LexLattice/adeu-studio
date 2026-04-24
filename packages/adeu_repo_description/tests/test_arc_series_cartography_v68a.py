from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_ARC_SERIES_CARTOGRAPHY_SCHEMA,
    RepoArcSeriesCartography,
    compute_repo_arc_series_cartography_id,
)
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v188_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / "vnext_plus188"


def _load_v188(name: str) -> dict[str, Any]:
    return json.loads((_v188_root() / name).read_text(encoding="utf-8"))


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_repo_description" / "schema" / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v188_reference_cartography_fixture_validates() -> None:
    payload = _load_v188("repo_arc_series_cartography_v188_reference.json")
    validated = RepoArcSeriesCartography.model_validate(payload)

    assert validated.schema == REPO_ARC_SERIES_CARTOGRAPHY_SCHEMA
    assert validated.coverage_horizon.startswith("post-V67 seed")
    assert {row.canonical_label for row in validated.namespace_rows}.issuperset(
        {"V43", "V67", "V68", "V69", "V75", "repo_arc_series_cartography@1"}
    )
    assert any(
        row.branch_family_id == "family:V43"
        and row.branch_posture == "connected_conditional_branch"
        for row in validated.branch_rows
    )
    integrated_reviews = {
        row.source_ref
        for row in validated.source_rows
        if row.source_kind == "review_input" and row.source_status == "integrated_shaping_source"
    }
    assert integrated_reviews == {
        "docs/support/arc_series_mapping/REVIEW_GPTPRO_ARC_SERIES_CARTOGRAPHY_ABC_SPECS_v0.md",
        "docs/support/arc_series_mapping/REVIEW_GPTPRO_ARC_SERIES_MAPPING_V68_PLANNING_v0.md",
    }


def test_v188_cartography_id_is_deterministic() -> None:
    payload = _load_v188("repo_arc_series_cartography_v188_reference.json")
    without_id = deepcopy(payload)
    without_id.pop("cartography_id")

    assert compute_repo_arc_series_cartography_id(without_id) == payload["cartography_id"]


def test_v188_exported_schema_accepts_reference_fixture() -> None:
    _schema_validator("repo_arc_series_cartography.v1.json").validate(
        _load_v188("repo_arc_series_cartography_v188_reference.json")
    )


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_arc_series_cartography_v188_reject_missing_integrated_review_source.json",
            "integrated source rows",
        ),
        (
            "repo_arc_series_cartography_v188_reject_family_v67_collapsed_with_global_vnext67.json",
            "V-family labels",
        ),
        (
            "repo_arc_series_cartography_v188_reject_v187_collapsed_with_v67c.json",
            "V-family labels",
        ),
        (
            "repo_arc_series_cartography_v188_reject_support_doc_as_lock_authority.json",
            "lock authority",
        ),
        (
            "repo_arc_series_cartography_v188_reject_missing_v43_branch_posture.json",
            "external contest future seams",
        ),
        (
            "repo_arc_series_cartography_v188_reject_global_tool_applicability_overclaim.json",
            "global scope",
        ),
        (
            "repo_arc_series_cartography_v188_reject_coordinate_authorizes_v69.json",
            "non_authority_guardrail",
        ),
        (
            "repo_arc_series_cartography_v188_reject_repo_schema_as_arc_agi_challenge_artifact.json",
            "Input should be",
        ),
    ],
)
def test_v188_rejects_invalid_cartography_fixtures(fixture_name: str, match: str) -> None:
    with pytest.raises(ValidationError, match=match):
        RepoArcSeriesCartography.model_validate(_load_v188(fixture_name))
