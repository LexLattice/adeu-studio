from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_ARC_SERIES_CARTOGRAPHY_SCHEMA,
    RepoArcMappingToolApplicabilityReport,
    RepoArcSeriesCartography,
    compute_repo_arc_series_cartography_id,
    materialize_repo_arc_series_cartography_payload,
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


def test_v188_allows_same_tool_for_distinct_applicability_claims() -> None:
    payload = _load_v188("repo_arc_series_cartography_v188_reference.json")
    payload["cartography_id"] = "placeholder"
    payload["tool_applicability_rows"].append(
        {
            "applicability_posture": "applicable_with_warnings",
            "limitation_note": (
                "The same start-check tool is scoped here to family-level selection evidence."
            ),
            "observed_result_ref": "evidence:v188_start_gate",
            "target_claim_id": "family:V68",
            "target_namespace_kind": "family_id",
            "tool_id": "tool:arc-start-check:ARC=188",
        }
    )
    payload["tool_applicability_rows"] = sorted(
        payload["tool_applicability_rows"],
        key=lambda row: (row["tool_id"], row["target_claim_id"], row["target_namespace_kind"]),
    )
    payload.pop("cartography_id")

    validated = RepoArcSeriesCartography.model_validate(
        materialize_repo_arc_series_cartography_payload(payload)
    )

    assert [
        row.target_claim_id
        for row in validated.tool_applicability_rows
        if row.tool_id == "tool:arc-start-check:ARC=188"
    ] == ["evidence:v188_start_gate", "family:V68"]


def test_v188_rejects_duplicate_tool_applicability_claim_key() -> None:
    payload = _load_v188("repo_arc_series_cartography_v188_reference.json")
    payload["tool_applicability_rows"].append(deepcopy(payload["tool_applicability_rows"][-1]))

    with pytest.raises(ValidationError, match="composite tool applicability keys"):
        RepoArcSeriesCartography.model_validate(payload)


def test_v188_tool_report_rejects_duplicate_tool_applicability_claim_key() -> None:
    payload = _load_v188("repo_arc_series_cartography_v188_reference.json")

    with pytest.raises(ValidationError, match="composite tool applicability keys"):
        RepoArcMappingToolApplicabilityReport.model_validate(
            {
                "cartography_id": payload["cartography_id"],
                "schema": "repo_arc_mapping_tool_applicability_report@1",
                "snapshot_id": payload["snapshot_id"],
                "tool_applicability_report_id": "tool-report:duplicate-key",
                "tool_applicability_rows": [
                    payload["tool_applicability_rows"][-1],
                    deepcopy(payload["tool_applicability_rows"][-1]),
                ],
            }
        )


def test_v188_global_scope_check_does_not_reject_non_global_limitations() -> None:
    payload = _load_v188("repo_arc_series_cartography_v188_reference.json")
    payload["tool_applicability_rows"][-1]["limitation_note"] = (
        "Non-global support applies to the V68-A starter bundle only."
    )
    payload.pop("cartography_id")

    RepoArcSeriesCartography.model_validate(
        materialize_repo_arc_series_cartography_payload(payload)
    )


def test_v188_rejects_any_non_connected_v43_branch_when_external_contest_seam_tracked() -> None:
    payload = _load_v188("repo_arc_series_cartography_v188_reference.json")
    payload["branch_rows"].append(
        {
            "branch_family_id": "family:V43",
            "branch_posture": "review_required_branch",
            "branch_ref": "branch:V43-review-required",
            "selection_condition": "Review required if contest branch pressure changes.",
            "source_refs": ["docs/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v2.md"],
        }
    )
    payload["branch_rows"] = sorted(payload["branch_rows"], key=lambda row: row["branch_ref"])

    with pytest.raises(ValidationError, match="external contest future seams"):
        RepoArcSeriesCartography.model_validate(payload)


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
