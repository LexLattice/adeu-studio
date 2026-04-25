from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CANDIDATE_INTAKE_DERIVATION_MANIFEST_SCHEMA,
    REPO_CANDIDATE_INTAKE_GAP_SCAN_SCHEMA,
    RepoCandidateIntakeDerivationManifest,
    RepoCandidateIntakeGapScan,
    derive_v69b_repo_candidate_intake_derivation_bundle,
    derive_v69b_repo_candidate_intake_derivation_manifest,
)
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v192_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / "vnext_plus192"


def _load_v192(name: str) -> dict[str, Any]:
    return json.loads((_v192_root() / name).read_text(encoding="utf-8"))


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_repo_description" / "schema" / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v192_reference_derivation_manifest_validates() -> None:
    payload = _load_v192("repo_candidate_intake_derivation_manifest_v192_reference.json")
    validated = RepoCandidateIntakeDerivationManifest.model_validate(payload)

    assert validated.schema == REPO_CANDIDATE_INTAKE_DERIVATION_MANIFEST_SCHEMA
    assert validated.coverage_horizon.startswith("V69-B starter derivation")
    assert len(validated.derivation_rows) == 6
    assert all("*" not in row.source_ref for row in validated.observed_source_rows)
    assert set(validated.candidate_refs_emitted) == {
        "candidate:evidence:V68_substrate_for_V69",
        "candidate:internal:odeu_conceptual_diff_report@1",
        "candidate:internal:odeu_conceptual_diff_schema_support",
        "candidate:internal:self_evidencing_workflow_type_emergence",
        "candidate:internal:typed_adjudication_product_wedge",
        "candidate:planning:V69_candidate_intake_family",
    }


def test_v192_reference_gap_scan_validates() -> None:
    payload = _load_v192("repo_candidate_intake_gap_scan_v192_reference.json")
    validated = RepoCandidateIntakeGapScan.model_validate(payload)

    assert validated.schema == REPO_CANDIDATE_INTAKE_GAP_SCAN_SCHEMA
    assert {
        row.gap_kind for row in validated.gap_rows
    } == {
        "derivation_rule_inconclusive",
        "v68_cartography_source_unmapped",
    }


def test_v192_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_candidate_intake_derivation_manifest.v1.json").validate(
        _load_v192("repo_candidate_intake_derivation_manifest_v192_reference.json")
    )
    _schema_validator("repo_candidate_intake_gap_scan.v1.json").validate(
        _load_v192("repo_candidate_intake_gap_scan_v192_reference.json")
    )


def test_v192_derivation_helper_matches_reference_fixtures() -> None:
    manifest, gap_scan = derive_v69b_repo_candidate_intake_derivation_bundle(
        repo_root=_repo_root()
    )

    assert manifest.model_dump(mode="json") == _load_v192(
        "repo_candidate_intake_derivation_manifest_v192_reference.json"
    )
    assert gap_scan.model_dump(mode="json") == _load_v192(
        "repo_candidate_intake_gap_scan_v192_reference.json"
    )


def test_v192_derivation_helper_fails_on_missing_expected_source_file() -> None:
    with pytest.raises(ValueError, match="expected V69-B source file is missing"):
        derive_v69b_repo_candidate_intake_derivation_manifest(
            repo_root=_repo_root(),
            source_patterns=("docs/DOES_NOT_EXIST_FOR_V69B.md",),
        )


def test_v192_derivation_helper_fails_on_missing_required_source_ref() -> None:
    with pytest.raises(ValueError, match="expected V69-B derivation source_refs"):
        derive_v69b_repo_candidate_intake_derivation_manifest(
            repo_root=_repo_root(),
            source_patterns=(
                "apps/api/fixtures/repo_description/vnext_plus191/"
                "repo_recursive_candidate_intake_v191_reference.json",
            ),
        )


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_candidate_intake_derivation_manifest_v192_reject_glob_as_source.json",
            "concrete source ref",
        ),
        (
            "repo_candidate_intake_derivation_manifest_v192_reject_missing_integrated_source.json",
            "integrated observed sources",
        ),
        (
            "repo_candidate_intake_derivation_manifest_v192_reject_unobserved_source_without_posture.json",
            "derivation source_refs",
        ),
        (
            "repo_candidate_intake_derivation_manifest_v192_reject_duplicate_without_equivalence_group.json",
            "suppressed_duplicate candidates",
        ),
        (
            "repo_candidate_intake_derivation_manifest_v192_reject_derivation_upgrades_support_to_lock.json",
            "support input cannot be upgraded",
        ),
        (
            "repo_candidate_intake_derivation_manifest_v192_reject_embedded_v70_review_classification.json",
            "evidence classification",
        ),
    ],
)
def test_v192_rejects_invalid_derivation_manifest_fixtures(
    fixture_name: str, match: str
) -> None:
    with pytest.raises(ValidationError, match=match):
        RepoCandidateIntakeDerivationManifest.model_validate(_load_v192(fixture_name))


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_candidate_intake_gap_scan_v192_reject_missing_expected_support_artifact_gap.json",
            "expected missing support artifacts",
        ),
        (
            "repo_candidate_intake_gap_scan_v192_reject_v68_cartography_source_unmapped_gap_missing.json",
            "V68 cartography unmapped sources",
        ),
        (
            "repo_candidate_intake_gap_scan_v192_reject_candidate_overclaim_without_blocking_gap.json",
            "candidate overclaims require",
        ),
        (
            "repo_candidate_intake_gap_scan_v192_reject_unknown_gap_source_ref.json",
            "gap source_refs",
        ),
        (
            "repo_candidate_intake_gap_scan_v192_reject_overclaim_gap_not_blocking.json",
            "candidate overclaims must remain blocking gaps",
        ),
    ],
)
def test_v192_rejects_invalid_gap_scan_fixtures(fixture_name: str, match: str) -> None:
    with pytest.raises(ValidationError, match=match):
        RepoCandidateIntakeGapScan.model_validate(_load_v192(fixture_name))
