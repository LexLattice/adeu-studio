from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CANDIDATE_PRE_RATIFICATION_HANDOFF_SCHEMA,
    REPO_CANDIDATE_REVIEW_CLASSIFICATION_SUMMARY_SCHEMA,
    RepoCandidateAdversarialReviewMatrix,
    RepoCandidateEvidenceClassificationRecord,
    RepoCandidateEvidenceSourceIndex,
    RepoCandidatePreRatificationHandoff,
    RepoCandidateReviewClassificationSummary,
    RepoCandidateReviewConflictRegister,
    RepoCandidateReviewGapScan,
    derive_v70c_repo_candidate_review_summary_bundle,
    validate_v70c_candidate_review_summary_bundle,
)
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root(slice_name: str) -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / slice_name


def _load_fixture(slice_name: str, name: str) -> dict[str, Any]:
    return json.loads((_fixture_root(slice_name) / name).read_text(encoding="utf-8"))


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
        _load_fixture("vnext_plus194", "repo_candidate_evidence_source_index_v194_reference.json")
    )


def _v70a_classification() -> RepoCandidateEvidenceClassificationRecord:
    return RepoCandidateEvidenceClassificationRecord.model_validate(
        _load_fixture("vnext_plus194", "repo_candidate_evidence_classification_v194_reference.json")
    )


def _v70b_bundle() -> tuple[
    RepoCandidateAdversarialReviewMatrix,
    RepoCandidateReviewConflictRegister,
    RepoCandidateReviewGapScan,
]:
    return (
        RepoCandidateAdversarialReviewMatrix.model_validate(
            _load_fixture(
                "vnext_plus195",
                "repo_candidate_adversarial_review_matrix_v195_reference.json",
            )
        ),
        RepoCandidateReviewConflictRegister.model_validate(
            _load_fixture(
                "vnext_plus195",
                "repo_candidate_review_conflict_register_v195_reference.json",
            )
        ),
        RepoCandidateReviewGapScan.model_validate(
            _load_fixture("vnext_plus195", "repo_candidate_review_gap_scan_v195_reference.json")
        ),
    )


def _v70c_reference_bundle() -> tuple[
    RepoCandidateReviewClassificationSummary,
    RepoCandidatePreRatificationHandoff,
]:
    return (
        RepoCandidateReviewClassificationSummary.model_validate(
            _load_fixture(
                "vnext_plus196",
                "repo_candidate_review_classification_summary_v196_reference.json",
            )
        ),
        RepoCandidatePreRatificationHandoff.model_validate(
            _load_fixture(
                "vnext_plus196",
                "repo_candidate_pre_ratification_handoff_v196_reference.json",
            )
        ),
    )


def test_v196_reference_bundle_validates() -> None:
    matrix, conflict_register, gap_scan = _v70b_bundle()
    summary, handoff = _v70c_reference_bundle()

    assert summary.schema == REPO_CANDIDATE_REVIEW_CLASSIFICATION_SUMMARY_SCHEMA
    assert handoff.schema == REPO_CANDIDATE_PRE_RATIFICATION_HANDOFF_SCHEMA
    assert {row.summary_posture for row in summary.summary_rows} == {
        "classified_blocked_by_conflict",
        "classified_deferred_to_future_family",
        "classified_ready_for_later_review",
    }
    assert any(row.handoff_posture == "ready_for_v71_review" for row in handoff.handoff_rows)
    assert all("not a decision" in row.non_authority_guardrail for row in handoff.handoff_rows)

    validate_v70c_candidate_review_summary_bundle(
        source_index=_v70a_source_index(),
        classification_record=_v70a_classification(),
        adversarial_review_matrix=matrix,
        conflict_register=conflict_register,
        gap_scan=gap_scan,
        classification_summary=summary,
        pre_ratification_handoff=handoff,
    )


def test_v196_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_candidate_review_classification_summary.v1.json").validate(
        _load_fixture(
            "vnext_plus196",
            "repo_candidate_review_classification_summary_v196_reference.json",
        )
    )
    _schema_validator("repo_candidate_pre_ratification_handoff.v1.json").validate(
        _load_fixture(
            "vnext_plus196",
            "repo_candidate_pre_ratification_handoff_v196_reference.json",
        )
    )


def test_v196_derivation_helper_matches_reference_fixtures() -> None:
    *_upstream, summary, handoff = derive_v70c_repo_candidate_review_summary_bundle(
        repo_root=_repo_root()
    )

    assert summary.model_dump(mode="json") == _load_fixture(
        "vnext_plus196",
        "repo_candidate_review_classification_summary_v196_reference.json",
    )
    assert handoff.model_dump(mode="json") == _load_fixture(
        "vnext_plus196",
        "repo_candidate_pre_ratification_handoff_v196_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_candidate_review_v196_reject_stale_summary_hash.json",
            RepoCandidateReviewClassificationSummary,
            "hash identity",
        ),
        (
            "repo_candidate_review_v196_reject_stale_handoff_hash.json",
            RepoCandidatePreRatificationHandoff,
            "hash identity",
        ),
        (
            "repo_candidate_review_v196_reject_summary_without_classification_refs.json",
            RepoCandidateReviewClassificationSummary,
            "at least 1 item",
        ),
        (
            "repo_candidate_review_v196_reject_handoff_as_ratification.json",
            RepoCandidatePreRatificationHandoff,
            "authority",
        ),
        (
            "repo_candidate_review_v196_reject_ready_handoff_with_blockers.json",
            RepoCandidatePreRatificationHandoff,
            "ready_for_v71_review cannot carry unresolved blockers",
        ),
        (
            "repo_candidate_review_v196_reject_v72_integration_selected.json",
            RepoCandidatePreRatificationHandoff,
            "Input should be",
        ),
        (
            "repo_candidate_review_v196_reject_product_authorization.json",
            RepoCandidateReviewClassificationSummary,
            "authority",
        ),
        (
            "repo_candidate_review_v196_reject_family_closeout_claims_adoption.json",
            RepoCandidateReviewClassificationSummary,
            "authority",
        ),
    ],
)
def test_v196_rejects_invalid_surface_fixtures(
    fixture_name: str,
    model_type: type[
        RepoCandidateReviewClassificationSummary | RepoCandidatePreRatificationHandoff
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus196", fixture_name))


@pytest.mark.parametrize(
    ("summary_fixture", "match"),
    [
        (
            "repo_candidate_review_v196_reject_unresolved_conflict_omitted.json",
            "summary conflict_refs",
        ),
    ],
)
def test_v196_bundle_rejects_invalid_summary_preservation(summary_fixture: str, match: str) -> None:
    matrix, conflict_register, gap_scan = _v70b_bundle()
    summary = RepoCandidateReviewClassificationSummary.model_validate(
        _load_fixture("vnext_plus196", summary_fixture)
    )
    _reference_summary, handoff = _v70c_reference_bundle()
    handoff = handoff.model_copy(update={"summary_register_id": summary.summary_register_id})

    with pytest.raises(ValueError, match=match):
        validate_v70c_candidate_review_summary_bundle(
            source_index=_v70a_source_index(),
            classification_record=_v70a_classification(),
            adversarial_review_matrix=matrix,
            conflict_register=conflict_register,
            gap_scan=gap_scan,
            classification_summary=summary,
            pre_ratification_handoff=handoff,
        )


@pytest.mark.parametrize(
    ("handoff_fixture", "match"),
    [
        (
            "repo_candidate_review_v196_reject_unresolved_gap_omitted.json",
            "unresolved_gap_refs",
        ),
        (
            "repo_candidate_review_v196_reject_product_wedge_to_v71.json",
            "product wedge handoff",
        ),
        (
            "repo_candidate_review_v196_reject_unknown_handoff_blocker_ref.json",
            "blocking_conflict_refs",
        ),
    ],
)
def test_v196_bundle_rejects_invalid_handoff_preservation(handoff_fixture: str, match: str) -> None:
    matrix, conflict_register, gap_scan = _v70b_bundle()
    summary, _reference_handoff = _v70c_reference_bundle()
    handoff = RepoCandidatePreRatificationHandoff.model_validate(
        _load_fixture("vnext_plus196", handoff_fixture)
    )

    with pytest.raises(ValueError, match=match):
        validate_v70c_candidate_review_summary_bundle(
            source_index=_v70a_source_index(),
            classification_record=_v70a_classification(),
            adversarial_review_matrix=matrix,
            conflict_register=conflict_register,
            gap_scan=gap_scan,
            classification_summary=summary,
            pre_ratification_handoff=handoff,
        )
