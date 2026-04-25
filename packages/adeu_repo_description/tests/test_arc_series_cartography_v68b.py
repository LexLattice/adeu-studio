from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_ARC_CARTOGRAPHY_DERIVATION_MANIFEST_SCHEMA,
    REPO_ARC_CARTOGRAPHY_GAP_SCAN_REPORT_SCHEMA,
    RepoArcCartographyDerivationManifest,
    RepoArcCartographyGapScanReport,
    derive_v68b_repo_arc_cartography_derivation_bundle,
    derive_v68b_repo_arc_cartography_derivation_manifest,
)
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v189_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / "vnext_plus189"


def _load_v189(name: str) -> dict[str, Any]:
    return json.loads((_v189_root() / name).read_text(encoding="utf-8"))


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_repo_description" / "schema" / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v189_reference_derivation_manifest_validates() -> None:
    payload = _load_v189("repo_arc_cartography_derivation_manifest_v189_reference.json")
    validated = RepoArcCartographyDerivationManifest.model_validate(payload)

    assert validated.schema == REPO_ARC_CARTOGRAPHY_DERIVATION_MANIFEST_SCHEMA
    assert validated.coverage_horizon.startswith("V68-B starter derivation")
    assert all("*" not in row.source_ref for row in validated.observed_input_rows)
    assert {
        row.derived_ref for row in validated.derived_row_records
    } == {
        "derived:branch:V43-connected-conditional",
        "derived:closeout:V68-A",
        "derived:coordinate_absence:V68-B",
        "derived:family:V68-B",
    }


def test_v189_reference_gap_scan_report_validates() -> None:
    payload = _load_v189("repo_arc_cartography_gap_scan_report_v189_reference.json")
    validated = RepoArcCartographyGapScanReport.model_validate(payload)

    assert validated.schema == REPO_ARC_CARTOGRAPHY_GAP_SCAN_REPORT_SCHEMA
    assert validated.coordinate_posture == "coordinate_absent_deliberate"
    assert any(row.gap_family == "coordinate_posture_absent" for row in validated.gap_rows)


def test_v189_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_arc_cartography_derivation_manifest.v1.json").validate(
        _load_v189("repo_arc_cartography_derivation_manifest_v189_reference.json")
    )
    _schema_validator("repo_arc_cartography_gap_scan_report.v1.json").validate(
        _load_v189("repo_arc_cartography_gap_scan_report_v189_reference.json")
    )


def test_v189_derivation_helper_matches_reference_fixtures() -> None:
    manifest, gap_scan = derive_v68b_repo_arc_cartography_derivation_bundle(
        repo_root=_repo_root()
    )

    assert manifest.model_dump(mode="json") == _load_v189(
        "repo_arc_cartography_derivation_manifest_v189_reference.json"
    )
    assert gap_scan.model_dump(mode="json") == _load_v189(
        "repo_arc_cartography_gap_scan_report_v189_reference.json"
    )


def test_v189_derivation_helper_fails_on_missing_expected_source_file() -> None:
    with pytest.raises(ValueError, match="expected V68-B source file is missing"):
        derive_v68b_repo_arc_cartography_derivation_manifest(
            repo_root=_repo_root(),
            source_patterns=("docs/DOES_NOT_EXIST_FOR_V68B.md",),
        )


def test_v189_derivation_helper_fails_on_missing_required_source_ref() -> None:
    with pytest.raises(ValueError, match="expected V68-B derivation source_refs"):
        derive_v68b_repo_arc_cartography_derivation_manifest(
            repo_root=_repo_root(),
            source_patterns=("docs/DRAFT_NEXT_ARC_OPTIONS_v54.md",),
        )


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_arc_cartography_derivation_manifest_v189_reject_glob_promoted_to_source.json",
            "concrete source ref",
        ),
        (
            "repo_arc_cartography_derivation_manifest_v189_reject_unknown_derived_source_ref.json",
            "derived source_refs",
        ),
        (
            "repo_arc_cartography_derivation_manifest_v189_reject_support_review_as_lock_evidence.json",
            "support review text",
        ),
        (
            "repo_arc_cartography_derivation_manifest_v189_reject_v69_authorized_lock.json",
            "V69 through V75",
        ),
        (
            "repo_arc_cartography_derivation_manifest_v189_reject_closure_from_support_prose.json",
            "closure derivation",
        ),
        (
            "repo_arc_cartography_derivation_manifest_v189_reject_ambiguous_branch_promoted_settled.json",
            "ambiguous or review-required",
        ),
        (
            "repo_arc_cartography_derivation_manifest_v189_reject_family_v67_collapsed_with_global_vnext67.json",
            "global implementation arc refs",
        ),
        (
            "repo_arc_cartography_derivation_manifest_v189_reject_lock_authorized_without_source_refs.json",
            "settled derivation claim horizons",
        ),
    ],
)
def test_v189_rejects_invalid_derivation_manifest_fixtures(
    fixture_name: str, match: str
) -> None:
    with pytest.raises(ValidationError, match=match):
        RepoArcCartographyDerivationManifest.model_validate(_load_v189(fixture_name))


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_arc_cartography_gap_scan_report_v189_reject_expected_support_missing_without_gap.json",
            "expected missing support artifacts",
        ),
        (
            "repo_arc_cartography_gap_scan_report_v189_reject_coordinate_absence_omitted.json",
            "coordinate absence",
        ),
        (
            "repo_arc_cartography_gap_scan_report_v189_reject_coordinate_emitted_with_absence_gap.json",
            "coordinate emitted posture",
        ),
    ],
)
def test_v189_rejects_invalid_gap_scan_report_fixtures(
    fixture_name: str, match: str
) -> None:
    with pytest.raises(ValidationError, match=match):
        RepoArcCartographyGapScanReport.model_validate(_load_v189(fixture_name))
