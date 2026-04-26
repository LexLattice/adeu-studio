from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CANDIDATE_RATIFICATION_RECORD_SCHEMA,
    REPO_RATIFICATION_DISSENT_REGISTER_SCHEMA,
    REPO_REVIEW_SETTLEMENT_RECORD_SCHEMA,
    RepoCandidateRatificationRecord,
    RepoCandidateRatificationRequest,
    RepoRatificationAuthorityProfile,
    RepoRatificationDissentRegister,
    RepoRatificationRequestScopeBoundary,
    RepoReviewSettlementRecord,
    derive_v71b_repo_candidate_ratification_review_bundle,
    validate_v71b_candidate_ratification_review_bundle,
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


def _v71a_request() -> RepoCandidateRatificationRequest:
    return RepoCandidateRatificationRequest.model_validate(
        _load_fixture("vnext_plus197", "repo_candidate_ratification_request_v197_reference.json")
    )


def _v71a_authority_profile() -> RepoRatificationAuthorityProfile:
    return RepoRatificationAuthorityProfile.model_validate(
        _load_fixture("vnext_plus197", "repo_ratification_authority_profile_v197_reference.json")
    )


def _v71a_scope_boundary() -> RepoRatificationRequestScopeBoundary:
    return RepoRatificationRequestScopeBoundary.model_validate(
        _load_fixture(
            "vnext_plus197",
            "repo_ratification_request_scope_boundary_v197_reference.json",
        )
    )


def _v71b_settlement() -> RepoReviewSettlementRecord:
    return RepoReviewSettlementRecord.model_validate(
        _load_fixture("vnext_plus198", "repo_review_settlement_record_v198_reference.json")
    )


def _v71b_dissent() -> RepoRatificationDissentRegister:
    return RepoRatificationDissentRegister.model_validate(
        _load_fixture("vnext_plus198", "repo_ratification_dissent_register_v198_reference.json")
    )


def _v71b_ratification() -> RepoCandidateRatificationRecord:
    return RepoCandidateRatificationRecord.model_validate(
        _load_fixture("vnext_plus198", "repo_candidate_ratification_record_v198_reference.json")
    )


def test_v198_reference_bundle_validates() -> None:
    settlement = _v71b_settlement()
    dissent = _v71b_dissent()
    ratification = _v71b_ratification()

    assert settlement.schema == REPO_REVIEW_SETTLEMENT_RECORD_SCHEMA
    assert dissent.schema == REPO_RATIFICATION_DISSENT_REGISTER_SCHEMA
    assert ratification.schema == REPO_CANDIDATE_RATIFICATION_RECORD_SCHEMA
    assert {row.decision_posture for row in ratification.ratification_rows} == {
        "deferred",
        "ratified",
    }
    assert not any(
        row.candidate_ref == "candidate:internal:typed_adjudication_product_wedge"
        and row.allowed_next_review_surface == "v72_contained_integration_review"
        for row in ratification.ratification_rows
    )

    validate_v71b_candidate_ratification_review_bundle(
        ratification_request=_v71a_request(),
        authority_profile=_v71a_authority_profile(),
        request_scope_boundary=_v71a_scope_boundary(),
        settlement_record=settlement,
        dissent_register=dissent,
        ratification_record=ratification,
    )


def test_v198_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_review_settlement_record.v1.json").validate(
        _load_fixture("vnext_plus198", "repo_review_settlement_record_v198_reference.json")
    )
    _schema_validator("repo_ratification_dissent_register.v1.json").validate(
        _load_fixture("vnext_plus198", "repo_ratification_dissent_register_v198_reference.json")
    )
    _schema_validator("repo_candidate_ratification_record.v1.json").validate(
        _load_fixture("vnext_plus198", "repo_candidate_ratification_record_v198_reference.json")
    )


def test_v198_derivation_helper_matches_reference_fixtures() -> None:
    *_upstream, settlement, dissent, ratification = (
        derive_v71b_repo_candidate_ratification_review_bundle(repo_root=_repo_root())
    )

    assert settlement.model_dump(mode="json") == _load_fixture(
        "vnext_plus198",
        "repo_review_settlement_record_v198_reference.json",
    )
    assert dissent.model_dump(mode="json") == _load_fixture(
        "vnext_plus198",
        "repo_ratification_dissent_register_v198_reference.json",
    )
    assert ratification.model_dump(mode="json") == _load_fixture(
        "vnext_plus198",
        "repo_candidate_ratification_record_v198_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_candidate_ratification_v198_reject_dissent_dropped.json",
            RepoReviewSettlementRecord,
            "preserve dissent_refs",
        ),
        (
            "repo_candidate_ratification_v198_reject_product_wedge_integration_review.json",
            RepoCandidateRatificationRecord,
            "product wedge cannot be ratified",
        ),
        (
            "repo_candidate_ratification_v198_reject_ratification_as_implementation.json",
            RepoCandidateRatificationRecord,
            "downstream authority",
        ),
        (
            "repo_candidate_ratification_v198_reject_release_authority.json",
            RepoCandidateRatificationRecord,
            "must state",
        ),
    ],
)
def test_v198_rejects_invalid_surface_fixtures(
    fixture_name: str,
    model_type: type[
        RepoReviewSettlementRecord
        | RepoRatificationDissentRegister
        | RepoCandidateRatificationRecord
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus198", fixture_name))


def test_v198_rejects_settlement_register_with_uncovered_declared_request() -> None:
    payload = _load_fixture(
        "vnext_plus198",
        "repo_review_settlement_record_v198_reference.json",
    )
    payload["settlement_rows"] = [
        row
        for row in payload["settlement_rows"]
        if row["settlement_ref"] != "settlement:v71b:product-wedge:future-family"
    ]

    with pytest.raises(ValidationError, match="cover every declared request_ref"):
        RepoReviewSettlementRecord.model_validate(payload)


def test_v198_rejects_blocked_request_without_covering_settlement() -> None:
    ratification_rows = [
        row.model_copy(
            update={
                "decision_posture": "ratified",
                "settlement_refs": ["settlement:v71b:self-evidencing:complementary"],
            }
        )
        if row.ratification_ref == "ratification:v71b:odeu-diff:deferred-with-dissent"
        else row
        for row in _v71b_ratification().ratification_rows
    ]
    ratification = _v71b_ratification().model_copy(update={"ratification_rows": ratification_rows})

    with pytest.raises(ValueError, match="covering settlement"):
        validate_v71b_candidate_ratification_review_bundle(
            ratification_request=_v71a_request(),
            authority_profile=_v71a_authority_profile(),
            request_scope_boundary=_v71a_scope_boundary(),
            settlement_record=_v71b_settlement(),
            dissent_register=_v71b_dissent(),
            ratification_record=ratification,
        )


def test_v198_rejects_v71a_scope_boundary_violation() -> None:
    ratification_rows = [
        row.model_copy(update={"allowed_next_review_surface": "v72_contained_integration_review"})
        if row.ratification_ref == "ratification:v71b:odeu-diff:deferred-with-dissent"
        else row
        for row in _v71b_ratification().ratification_rows
    ]
    ratification = _v71b_ratification().model_copy(update={"ratification_rows": ratification_rows})

    with pytest.raises(ValueError, match="exceeds V71-A scope boundary"):
        validate_v71b_candidate_ratification_review_bundle(
            ratification_request=_v71a_request(),
            authority_profile=_v71a_authority_profile(),
            request_scope_boundary=_v71a_scope_boundary(),
            settlement_record=_v71b_settlement(),
            dissent_register=_v71b_dissent(),
            ratification_record=ratification,
        )


def test_v198_rejects_ratification_over_human_review_settlement_blocker() -> None:
    settlement_rows = [
        row.model_copy(update={"settlement_posture": "requires_human_review"})
        if row.settlement_ref == "settlement:v71b:self-evidencing:complementary"
        else row
        for row in _v71b_settlement().settlement_rows
    ]
    settlement = _v71b_settlement().model_copy(update={"settlement_rows": settlement_rows})

    with pytest.raises(ValueError, match="unresolved settlement blockers"):
        validate_v71b_candidate_ratification_review_bundle(
            ratification_request=_v71a_request(),
            authority_profile=_v71a_authority_profile(),
            request_scope_boundary=_v71a_scope_boundary(),
            settlement_record=settlement,
            dissent_register=_v71b_dissent(),
            ratification_record=_v71b_ratification(),
        )


def test_v198_rejects_ratification_that_drops_settlement_dissent_refs() -> None:
    ratification_rows = [
        row.model_copy(update={"dissent_refs": []})
        if row.ratification_ref == "ratification:v71b:odeu-diff:deferred-with-dissent"
        else row
        for row in _v71b_ratification().ratification_rows
    ]
    ratification = _v71b_ratification().model_copy(update={"ratification_rows": ratification_rows})

    with pytest.raises(ValueError, match="preserve dissent from settlement"):
        validate_v71b_candidate_ratification_review_bundle(
            ratification_request=_v71a_request(),
            authority_profile=_v71a_authority_profile(),
            request_scope_boundary=_v71a_scope_boundary(),
            settlement_record=_v71b_settlement(),
            dissent_register=_v71b_dissent(),
            ratification_record=ratification,
        )


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_candidate_ratification_v198_reject_missing_request_ref.json",
            "known request_refs",
        ),
        (
            "repo_candidate_ratification_v198_reject_unauthorized_authority_profile.json",
            "ratification requires ratification-authorized profile",
        ),
        (
            "repo_candidate_ratification_v198_reject_blocked_without_settlement.json",
            "covering settlement",
        ),
        (
            "repo_candidate_ratification_v198_reject_unresolved_gap_ratified.json",
            "unresolved settlement blockers cannot be ratified",
        ),
    ],
)
def test_v198_bundle_rejects_cross_surface_errors(fixture_name: str, match: str) -> None:
    settlement = _v71b_settlement()
    dissent = _v71b_dissent()
    ratification = _v71b_ratification()
    payload = _load_fixture("vnext_plus198", fixture_name)
    if payload["schema"] == REPO_REVIEW_SETTLEMENT_RECORD_SCHEMA:
        settlement = RepoReviewSettlementRecord.model_validate(payload)
        ratification_rows = list(ratification.ratification_rows)
        if "unresolved_gap" in fixture_name:
            ratification_rows = [
                row.model_copy(update={"decision_posture": "ratified"})
                if row.ratification_ref == "ratification:v71b:odeu-diff:deferred-with-dissent"
                else row
                for row in ratification_rows
            ]
        ratification = ratification.model_copy(
            update={
                "settlement_register_id": settlement.settlement_register_id,
                "ratification_rows": ratification_rows,
            }
        )
        dissent = dissent.model_copy(
            update={"settlement_register_id": settlement.settlement_register_id}
        )
    else:
        ratification = RepoCandidateRatificationRecord.model_validate(payload)

    with pytest.raises(ValueError, match=match):
        validate_v71b_candidate_ratification_review_bundle(
            ratification_request=_v71a_request(),
            authority_profile=_v71a_authority_profile(),
            request_scope_boundary=_v71a_scope_boundary(),
            settlement_record=settlement,
            dissent_register=dissent,
            ratification_record=ratification,
        )
