from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CANDIDATE_ADVERSARIAL_REVIEW_MATRIX_SCHEMA,
    REPO_CANDIDATE_REVIEW_CONFLICT_REGISTER_SCHEMA,
    REPO_CANDIDATE_REVIEW_GAP_SCAN_SCHEMA,
    RepoCandidateAdversarialReviewMatrix,
    RepoCandidateEvidenceClassificationRecord,
    RepoCandidateEvidenceSourceIndex,
    RepoCandidateReviewConflictRegister,
    RepoCandidateReviewGapScan,
    derive_v70b_repo_candidate_review_bundle,
    validate_v70b_candidate_review_bundle,
)
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v194_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / "vnext_plus194"


def _v195_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / "vnext_plus195"


def _load_v194(name: str) -> dict[str, Any]:
    return json.loads((_v194_root() / name).read_text(encoding="utf-8"))


def _load_v195(name: str) -> dict[str, Any]:
    return json.loads((_v195_root() / name).read_text(encoding="utf-8"))


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_repo_description" / "schema" / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _v70a_source_index() -> RepoCandidateEvidenceSourceIndex:
    return RepoCandidateEvidenceSourceIndex.model_validate(
        _load_v194("repo_candidate_evidence_source_index_v194_reference.json")
    )


def _v70a_classification() -> RepoCandidateEvidenceClassificationRecord:
    return RepoCandidateEvidenceClassificationRecord.model_validate(
        _load_v194("repo_candidate_evidence_classification_v194_reference.json")
    )


def _v70b_reference_bundle() -> tuple[
    RepoCandidateAdversarialReviewMatrix,
    RepoCandidateReviewConflictRegister,
    RepoCandidateReviewGapScan,
]:
    return (
        RepoCandidateAdversarialReviewMatrix.model_validate(
            _load_v195("repo_candidate_adversarial_review_matrix_v195_reference.json")
        ),
        RepoCandidateReviewConflictRegister.model_validate(
            _load_v195("repo_candidate_review_conflict_register_v195_reference.json")
        ),
        RepoCandidateReviewGapScan.model_validate(
            _load_v195("repo_candidate_review_gap_scan_v195_reference.json")
        ),
    )


def test_v195_reference_bundle_validates() -> None:
    matrix, conflict_register, gap_scan = _v70b_reference_bundle()

    assert matrix.schema == REPO_CANDIDATE_ADVERSARIAL_REVIEW_MATRIX_SCHEMA
    assert conflict_register.schema == REPO_CANDIDATE_REVIEW_CONFLICT_REGISTER_SCHEMA
    assert gap_scan.schema == REPO_CANDIDATE_REVIEW_GAP_SCAN_SCHEMA
    assert {row.review_relation_kind for row in conflict_register.relation_rows} == {
        "complementarity",
        "conflict",
    }
    assert "product_wedge_without_v74_boundary" in {
        row.gap_kind for row in gap_scan.gap_rows
    }

    validate_v70b_candidate_review_bundle(
        source_index=_v70a_source_index(),
        classification_record=_v70a_classification(),
        adversarial_review_matrix=matrix,
        conflict_register=conflict_register,
        gap_scan=gap_scan,
    )


def test_v195_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_candidate_adversarial_review_matrix.v1.json").validate(
        _load_v195("repo_candidate_adversarial_review_matrix_v195_reference.json")
    )
    _schema_validator("repo_candidate_review_conflict_register.v1.json").validate(
        _load_v195("repo_candidate_review_conflict_register_v195_reference.json")
    )
    _schema_validator("repo_candidate_review_gap_scan.v1.json").validate(
        _load_v195("repo_candidate_review_gap_scan_v195_reference.json")
    )


def test_v195_derivation_helper_matches_reference_fixtures() -> None:
    _source_index, _classification, matrix, conflict_register, gap_scan = (
        derive_v70b_repo_candidate_review_bundle(repo_root=_repo_root())
    )

    assert matrix.model_dump(mode="json") == _load_v195(
        "repo_candidate_adversarial_review_matrix_v195_reference.json"
    )
    assert conflict_register.model_dump(mode="json") == _load_v195(
        "repo_candidate_review_conflict_register_v195_reference.json"
    )
    assert gap_scan.model_dump(mode="json") == _load_v195(
        "repo_candidate_review_gap_scan_v195_reference.json"
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "id_key"),
    [
        (
            "repo_candidate_adversarial_review_matrix_v195_reference.json",
            RepoCandidateAdversarialReviewMatrix,
            "review_matrix_id",
        ),
        (
            "repo_candidate_review_conflict_register_v195_reference.json",
            RepoCandidateReviewConflictRegister,
            "conflict_register_id",
        ),
        (
            "repo_candidate_review_gap_scan_v195_reference.json",
            RepoCandidateReviewGapScan,
            "gap_scan_id",
        ),
    ],
)
def test_v195_rejects_stale_top_level_hash_identity(
    fixture_name: str,
    model_type: type[
        RepoCandidateAdversarialReviewMatrix
        | RepoCandidateReviewConflictRegister
        | RepoCandidateReviewGapScan
    ],
    id_key: str,
) -> None:
    payload = _load_v195(fixture_name)
    payload[id_key] = "stale-id"

    with pytest.raises(ValidationError, match="hash identity"):
        model_type.model_validate(payload)


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_candidate_review_v195_reject_missing_classification_ref.json",
            "known classification_refs",
        ),
        (
            "repo_candidate_review_v195_reject_adversarial_review_as_ratification.json",
            "authority",
        ),
    ],
)
def test_v195_rejects_invalid_adversarial_matrix_fixtures(
    fixture_name: str, match: str
) -> None:
    with pytest.raises(ValidationError, match=match):
        RepoCandidateAdversarialReviewMatrix.model_validate(_load_v195(fixture_name))


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_candidate_review_v195_reject_conflict_marked_resolved.json",
            "Input should be",
        ),
        (
            "repo_candidate_review_v195_reject_complementarity_as_conflict.json",
            "non-conflict relation rows",
        ),
        (
            "repo_candidate_review_v195_reject_v71_selected_by_conflict.json",
            "Input should be",
        ),
    ],
)
def test_v195_rejects_invalid_conflict_register_fixtures(
    fixture_name: str, match: str
) -> None:
    with pytest.raises(ValidationError, match=match):
        RepoCandidateReviewConflictRegister.model_validate(_load_v195(fixture_name))


def test_v195_rejects_gap_as_implementation_priority_fixture() -> None:
    with pytest.raises(ValidationError, match="Input should be"):
        RepoCandidateReviewGapScan.model_validate(
            _load_v195("repo_candidate_review_v195_reject_gap_as_implementation_priority.json")
        )


@pytest.mark.parametrize(
    ("matrix_fixture", "match"),
    [
        (
            "repo_candidate_review_v195_reject_v70a_claim_unreviewed.json",
            "need adversarial review rows",
        ),
        (
            "repo_candidate_review_v195_reject_model_output_without_negative_control.json",
            "opposing or negative control",
        ),
    ],
)
def test_v195_bundle_rejects_invalid_matrix_coverage(
    matrix_fixture: str, match: str
) -> None:
    matrix = RepoCandidateAdversarialReviewMatrix.model_validate(_load_v195(matrix_fixture))
    _reference_matrix, conflict_register, gap_scan = _v70b_reference_bundle()
    conflict_register = conflict_register.model_copy(
        update={"review_matrix_id": matrix.review_matrix_id}
    )

    with pytest.raises(ValueError, match=match):
        validate_v70b_candidate_review_bundle(
            source_index=_v70a_source_index(),
            classification_record=_v70a_classification(),
            adversarial_review_matrix=matrix,
            conflict_register=conflict_register,
            gap_scan=gap_scan,
        )


def test_v195_bundle_rejects_cross_surface_review_identity_mismatch() -> None:
    matrix, conflict_register, gap_scan = _v70b_reference_bundle()
    stale_conflict_register = conflict_register.model_copy(
        update={"review_id": "review:v70b:stale"}
    )

    with pytest.raises(ValueError, match="review_id must match"):
        validate_v70b_candidate_review_bundle(
            source_index=_v70a_source_index(),
            classification_record=_v70a_classification(),
            adversarial_review_matrix=matrix,
            conflict_register=stale_conflict_register,
            gap_scan=gap_scan,
        )


def test_v195_bundle_rejects_cross_surface_snapshot_mismatch() -> None:
    matrix, conflict_register, gap_scan = _v70b_reference_bundle()
    stale_gap_scan = gap_scan.model_copy(update={"snapshot_id": "vNext+195-stale"})

    with pytest.raises(ValueError, match="snapshot_id must match"):
        validate_v70b_candidate_review_bundle(
            source_index=_v70a_source_index(),
            classification_record=_v70a_classification(),
            adversarial_review_matrix=matrix,
            conflict_register=conflict_register,
            gap_scan=stale_gap_scan,
        )


def test_v195_bundle_rejects_classification_record_id_mismatch() -> None:
    matrix, conflict_register, gap_scan = _v70b_reference_bundle()
    stale_matrix = matrix.model_copy(update={"classification_record_id": "classification:stale"})

    with pytest.raises(ValueError, match="classification_record_id must match"):
        validate_v70b_candidate_review_bundle(
            source_index=_v70a_source_index(),
            classification_record=_v70a_classification(),
            adversarial_review_matrix=stale_matrix,
            conflict_register=conflict_register,
            gap_scan=gap_scan,
        )


def test_v195_bundle_rejects_unknown_relation_claim_ref() -> None:
    matrix, conflict_register, gap_scan = _v70b_reference_bundle()
    bad_relation = conflict_register.relation_rows[0].model_copy(
        update={"claim_refs": ["claim:v70a:missing"]}
    )
    bad_register = conflict_register.model_copy(update={"relation_rows": [bad_relation]})

    with pytest.raises(ValueError, match="known V70-A claims"):
        validate_v70b_candidate_review_bundle(
            source_index=_v70a_source_index(),
            classification_record=_v70a_classification(),
            adversarial_review_matrix=matrix,
            conflict_register=bad_register,
            gap_scan=gap_scan,
        )


def test_v195_bundle_rejects_relation_claim_candidate_mismatch() -> None:
    matrix, conflict_register, gap_scan = _v70b_reference_bundle()
    bad_relation = conflict_register.relation_rows[0].model_copy(
        update={"claim_refs": ["claim:v70a:product-wedge:authority-boundary"]}
    )
    bad_register = conflict_register.model_copy(update={"relation_rows": [bad_relation]})

    with pytest.raises(ValueError, match="candidate_ref must match referenced V70-A claims"):
        validate_v70b_candidate_review_bundle(
            source_index=_v70a_source_index(),
            classification_record=_v70a_classification(),
            adversarial_review_matrix=matrix,
            conflict_register=bad_register,
            gap_scan=gap_scan,
        )


@pytest.mark.parametrize(
    ("gap_fixture", "match"),
    [
        (
            "repo_candidate_review_v195_reject_single_source_overclaim_omitted.json",
            "single_source_overclaim",
        ),
        (
            "repo_candidate_review_v195_reject_product_wedge_without_boundary.json",
            "product_wedge_without_v74_boundary",
        ),
    ],
)
def test_v195_bundle_rejects_missing_gap_rows(gap_fixture: str, match: str) -> None:
    matrix, conflict_register, _gap_scan = _v70b_reference_bundle()
    gap_scan = RepoCandidateReviewGapScan.model_validate(_load_v195(gap_fixture))

    with pytest.raises(ValueError, match=match):
        validate_v70b_candidate_review_bundle(
            source_index=_v70a_source_index(),
            classification_record=_v70a_classification(),
            adversarial_review_matrix=matrix,
            conflict_register=conflict_register,
            gap_scan=gap_scan,
        )
