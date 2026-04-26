from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CANDIDATE_EVIDENCE_CLASSIFICATION_RECORD_SCHEMA,
    REPO_CANDIDATE_EVIDENCE_SOURCE_INDEX_SCHEMA,
    REPO_CANDIDATE_REVIEW_BOUNDARY_GUARDRAIL_SCHEMA,
    RepoCandidateEvidenceClassificationRecord,
    RepoCandidateEvidenceSourceIndex,
    RepoCandidateReviewBoundaryGuardrail,
    derive_v70a_repo_candidate_review_classification_bundle,
    validate_v70a_review_classification_bundle,
)
from jsonschema import Draft202012Validator
from jsonschema.exceptions import ValidationError as JsonSchemaValidationError
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v194_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / "vnext_plus194"


def _load_v194(name: str) -> dict[str, Any]:
    return json.loads((_v194_root() / name).read_text(encoding="utf-8"))


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_repo_description" / "schema" / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _reference_bundle() -> tuple[
    RepoCandidateEvidenceSourceIndex,
    RepoCandidateEvidenceClassificationRecord,
    RepoCandidateReviewBoundaryGuardrail,
]:
    return (
        RepoCandidateEvidenceSourceIndex.model_validate(
            _load_v194("repo_candidate_evidence_source_index_v194_reference.json")
        ),
        RepoCandidateEvidenceClassificationRecord.model_validate(
            _load_v194("repo_candidate_evidence_classification_v194_reference.json")
        ),
        RepoCandidateReviewBoundaryGuardrail.model_validate(
            _load_v194("repo_candidate_review_boundary_guardrail_v194_reference.json")
        ),
    )


def test_v194_reference_bundle_validates() -> None:
    source_index, classification, boundary = _reference_bundle()

    assert source_index.schema == REPO_CANDIDATE_EVIDENCE_SOURCE_INDEX_SCHEMA
    assert classification.schema == REPO_CANDIDATE_EVIDENCE_CLASSIFICATION_RECORD_SCHEMA
    assert boundary.schema == REPO_CANDIDATE_REVIEW_BOUNDARY_GUARDRAIL_SCHEMA
    assert {row.evidence_classification for row in classification.claim_classification_rows} == {
        "authority_boundary_blocked",
        "requires_adversarial_review",
        "source_bound_for_review",
    }
    model_row = next(
        row
        for row in classification.claim_classification_rows
        if row.claim_ref == "claim:v70a:odeu-diff:adversarial-review-need"
    )
    assert model_row.adversarial_review_posture == "required_not_started"
    assert all(row.odeu_lanes == sorted(row.odeu_lanes) for row in classification.claim_rows)

    validate_v70a_review_classification_bundle(
        source_index=source_index,
        classification_record=classification,
        boundary_guardrail=boundary,
    )


def test_v194_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_candidate_evidence_source_index.v1.json").validate(
        _load_v194("repo_candidate_evidence_source_index_v194_reference.json")
    )
    _schema_validator("repo_candidate_evidence_classification_record.v1.json").validate(
        _load_v194("repo_candidate_evidence_classification_v194_reference.json")
    )
    _schema_validator("repo_candidate_review_boundary_guardrail.v1.json").validate(
        _load_v194("repo_candidate_review_boundary_guardrail_v194_reference.json")
    )


def test_v194_exported_schema_rejects_invalid_next_review_surface() -> None:
    validator = _schema_validator("repo_candidate_review_boundary_guardrail.v1.json")

    with pytest.raises(JsonSchemaValidationError, match="is not one of"):
        validator.validate(
            _load_v194(
                "repo_candidate_evidence_classification_v194_reject_product_authorization.json"
            )
        )


def test_v194_derivation_helper_matches_reference_fixtures() -> None:
    source_index, classification, boundary = (
        derive_v70a_repo_candidate_review_classification_bundle(repo_root=_repo_root())
    )

    assert source_index.model_dump(mode="json") == _load_v194(
        "repo_candidate_evidence_source_index_v194_reference.json"
    )
    assert classification.model_dump(mode="json") == _load_v194(
        "repo_candidate_evidence_classification_v194_reference.json"
    )
    assert boundary.model_dump(mode="json") == _load_v194(
        "repo_candidate_review_boundary_guardrail_v194_reference.json"
    )


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_candidate_evidence_classification_v194_reject_glob_as_evidence.json",
            "concrete source ref",
        ),
        (
            "repo_candidate_evidence_classification_v194_reject_support_doc_as_lock_authority.json",
            "support and review sources",
        ),
    ],
)
def test_v194_rejects_invalid_evidence_source_fixtures(
    fixture_name: str, match: str
) -> None:
    with pytest.raises(ValidationError, match=match):
        RepoCandidateEvidenceSourceIndex.model_validate(_load_v194(fixture_name))


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_candidate_evidence_classification_v194_reject_unadmitted_candidate.json",
            "known candidate_input_refs",
        ),
        (
            "repo_candidate_evidence_classification_v194_reject_dangling_claim_ref.json",
            "known claim rows",
        ),
        (
            "repo_candidate_evidence_classification_v194_reject_source_missing_without_absence_row.json",
            "at least 1 item",
        ),
        (
            "repo_candidate_evidence_classification_v194_reject_intake_as_truth.json",
            "verdict language",
        ),
        (
            "repo_candidate_evidence_classification_v194_reject_classification_as_ratification.json",
            "authority",
        ),
        (
            "repo_candidate_evidence_classification_v194_reject_required_adversarial_marked_not_required.json",
            "requires_adversarial_review",
        ),
        (
            "repo_candidate_evidence_classification_v194_reject_model_output_without_adversarial_review.json",
            "model-output comparison",
        ),
    ],
)
def test_v194_rejects_invalid_classification_fixtures(
    fixture_name: str, match: str
) -> None:
    with pytest.raises(ValidationError, match=match):
        RepoCandidateEvidenceClassificationRecord.model_validate(_load_v194(fixture_name))


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_candidate_evidence_classification_v194_reject_product_authorization.json",
            "Input should be",
        ),
        (
            "repo_candidate_evidence_classification_v194_reject_dispatch_authority.json",
            "authority",
        ),
    ],
)
def test_v194_rejects_invalid_boundary_guardrail_fixtures(
    fixture_name: str, match: str
) -> None:
    with pytest.raises(ValidationError, match=match):
        RepoCandidateReviewBoundaryGuardrail.model_validate(_load_v194(fixture_name))


def test_v194_bundle_rejects_missing_boundary_guardrail() -> None:
    source_index, classification, _boundary = _reference_bundle()
    missing_boundary = RepoCandidateReviewBoundaryGuardrail.model_validate(
        _load_v194(
            "repo_candidate_evidence_classification_v194_reject_missing_boundary_guardrail.json"
        )
    )

    with pytest.raises(ValueError, match="boundary guardrail rows"):
        validate_v70a_review_classification_bundle(
            source_index=source_index,
            classification_record=classification,
            boundary_guardrail=missing_boundary,
        )


def test_v194_bundle_rejects_cross_candidate_evidence_source_ref() -> None:
    source_index, classification, boundary = _reference_bundle()
    payload = classification.model_dump(mode="json")
    payload["claim_classification_rows"][0]["evidence_source_refs"] = [
        "evidence-source:v70a:gptpro-review"
    ]
    mismatched_classification = RepoCandidateEvidenceClassificationRecord.model_validate(payload)

    with pytest.raises(ValueError, match="classified candidate"):
        validate_v70a_review_classification_bundle(
            source_index=source_index,
            classification_record=mismatched_classification,
            boundary_guardrail=boundary,
        )


@pytest.mark.parametrize(
    ("surface_name", "field_name", "match"),
    [
        ("classification", "snapshot_id", "classification record snapshot_id"),
        ("boundary", "snapshot_id", "boundary guardrail snapshot_id"),
        ("classification", "source_set_id", "classification record source_set_id"),
        ("boundary", "source_set_id", "boundary guardrail source_set_id"),
    ],
)
def test_v194_bundle_rejects_mixed_snapshot_or_source_set_ids(
    surface_name: str, field_name: str, match: str
) -> None:
    source_index, classification, boundary = _reference_bundle()
    classification_payload = classification.model_dump(mode="json")
    boundary_payload = boundary.model_dump(mode="json")
    target_payload = (
        classification_payload if surface_name == "classification" else boundary_payload
    )
    target_payload[field_name] = f"drifted:{field_name}"

    drifted_classification = RepoCandidateEvidenceClassificationRecord.model_validate(
        classification_payload
    )
    drifted_boundary = RepoCandidateReviewBoundaryGuardrail.model_validate(boundary_payload)

    with pytest.raises(ValueError, match=match):
        validate_v70a_review_classification_bundle(
            source_index=source_index,
            classification_record=drifted_classification,
            boundary_guardrail=drifted_boundary,
        )
