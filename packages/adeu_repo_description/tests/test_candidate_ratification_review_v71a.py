from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CANDIDATE_RATIFICATION_REQUEST_SCHEMA,
    REPO_RATIFICATION_AUTHORITY_PROFILE_SCHEMA,
    REPO_RATIFICATION_REQUEST_SCOPE_BOUNDARY_SCHEMA,
    RepoCandidatePreRatificationHandoff,
    RepoCandidateRatificationRequest,
    RepoCandidateReviewClassificationSummary,
    RepoRatificationAuthorityProfile,
    RepoRatificationRequestScopeBoundary,
    derive_v71a_repo_candidate_ratification_review_bundle,
    validate_v71a_candidate_ratification_review_bundle,
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


def _v70c_summary() -> RepoCandidateReviewClassificationSummary:
    return RepoCandidateReviewClassificationSummary.model_validate(
        _load_fixture(
            "vnext_plus196",
            "repo_candidate_review_classification_summary_v196_reference.json",
        )
    )


def _v70c_handoff() -> RepoCandidatePreRatificationHandoff:
    return RepoCandidatePreRatificationHandoff.model_validate(
        _load_fixture(
            "vnext_plus196",
            "repo_candidate_pre_ratification_handoff_v196_reference.json",
        )
    )


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


def test_v197_reference_bundle_validates() -> None:
    request = _v71a_request()
    authority_profile = _v71a_authority_profile()
    scope_boundary = _v71a_scope_boundary()

    assert request.schema == REPO_CANDIDATE_RATIFICATION_REQUEST_SCHEMA
    assert authority_profile.schema == REPO_RATIFICATION_AUTHORITY_PROFILE_SCHEMA
    assert scope_boundary.schema == REPO_RATIFICATION_REQUEST_SCOPE_BOUNDARY_SCHEMA
    assert {row.request_posture for row in request.request_rows} == {
        "deferred_to_future_family",
        "eligible_for_ratification_review",
        "requires_settlement_before_ratification",
    }
    assert not any(
        row.candidate_ref == "candidate:internal:typed_adjudication_product_wedge"
        and row.request_posture != "deferred_to_future_family"
        for row in request.request_rows
    )
    assert all(
        "implementation_task" in row.forbidden_downstream_roles
        and "commit_release_authority" in row.forbidden_downstream_roles
        for row in scope_boundary.request_scope_boundary_rows
    )

    validate_v71a_candidate_ratification_review_bundle(
        classification_summary=_v70c_summary(),
        pre_ratification_handoff=_v70c_handoff(),
        ratification_request=request,
        authority_profile=authority_profile,
        request_scope_boundary=scope_boundary,
    )


def test_v197_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_candidate_ratification_request.v1.json").validate(
        _load_fixture(
            "vnext_plus197",
            "repo_candidate_ratification_request_v197_reference.json",
        )
    )
    _schema_validator("repo_ratification_authority_profile.v1.json").validate(
        _load_fixture(
            "vnext_plus197",
            "repo_ratification_authority_profile_v197_reference.json",
        )
    )
    _schema_validator("repo_ratification_request_scope_boundary.v1.json").validate(
        _load_fixture(
            "vnext_plus197",
            "repo_ratification_request_scope_boundary_v197_reference.json",
        )
    )


def test_v197_derivation_helper_matches_reference_fixtures() -> None:
    *_upstream, request, authority_profile, scope_boundary = (
        derive_v71a_repo_candidate_ratification_review_bundle(repo_root=_repo_root())
    )

    assert request.model_dump(mode="json") == _load_fixture(
        "vnext_plus197",
        "repo_candidate_ratification_request_v197_reference.json",
    )
    assert authority_profile.model_dump(mode="json") == _load_fixture(
        "vnext_plus197",
        "repo_ratification_authority_profile_v197_reference.json",
    )
    assert scope_boundary.model_dump(mode="json") == _load_fixture(
        "vnext_plus197",
        "repo_ratification_request_scope_boundary_v197_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_candidate_ratification_v197_reject_request_without_source_refs.json",
            RepoCandidateRatificationRequest,
            "at least 1 item",
        ),
        (
            "repo_candidate_ratification_v197_reject_v71a_records_final_ratification.json",
            RepoCandidateRatificationRequest,
            "Extra inputs are not permitted",
        ),
        (
            "repo_candidate_ratification_v197_reject_product_wedge_to_v71.json",
            RepoCandidateRatificationRequest,
            "product wedge requests",
        ),
        (
            "repo_candidate_ratification_v197_reject_model_self_ratification.json",
            RepoRatificationAuthorityProfile,
            "only human or maintainer",
        ),
        (
            "repo_candidate_ratification_v197_reject_tool_pass_as_ratification.json",
            RepoRatificationAuthorityProfile,
            "lock or maintainer grant",
        ),
        (
            "repo_candidate_ratification_v197_reject_support_doc_as_ratification_authority.json",
            RepoRatificationAuthorityProfile,
            "lock or maintainer grant",
        ),
        (
            "repo_candidate_ratification_v197_reject_scope_allows_release.json",
            RepoRatificationRequestScopeBoundary,
            "forbid downstream roles",
        ),
    ],
)
def test_v197_rejects_invalid_surface_fixtures(
    fixture_name: str,
    model_type: type[
        RepoCandidateRatificationRequest
        | RepoRatificationAuthorityProfile
        | RepoRatificationRequestScopeBoundary
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus197", fixture_name))


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_candidate_ratification_v197_reject_blocked_handoff_marked_eligible.json",
            "blocked V70-C handoffs",
        ),
        (
            "repo_candidate_ratification_v197_reject_dangling_summary_ref.json",
            "known summary rows",
        ),
        (
            "repo_candidate_ratification_v197_reject_scope_unknown_request_ref.json",
            "scope request_refs",
        ),
    ],
)
def test_v197_bundle_rejects_cross_surface_errors(fixture_name: str, match: str) -> None:
    request = _v71a_request()
    authority_profile = _v71a_authority_profile()
    scope_boundary = _v71a_scope_boundary()
    if "scope" in fixture_name:
        scope_boundary = RepoRatificationRequestScopeBoundary.model_validate(
            _load_fixture("vnext_plus197", fixture_name)
        )
    else:
        request = RepoCandidateRatificationRequest.model_validate(
            _load_fixture("vnext_plus197", fixture_name)
        )
        scope_boundary = scope_boundary.model_copy(
            update={"ratification_request_id": request.ratification_request_id}
        )

    with pytest.raises(ValueError, match=match):
        validate_v71a_candidate_ratification_review_bundle(
            classification_summary=_v70c_summary(),
            pre_ratification_handoff=_v70c_handoff(),
            ratification_request=request,
            authority_profile=authority_profile,
            request_scope_boundary=scope_boundary,
        )


def test_v197_bundle_rejects_missing_v70c_handoff_coverage() -> None:
    request = _v71a_request()
    request = request.model_copy(update={"request_rows": request.request_rows[:-1]})

    with pytest.raises(ValueError, match="cover every V70-C handoff"):
        validate_v71a_candidate_ratification_review_bundle(
            classification_summary=_v70c_summary(),
            pre_ratification_handoff=_v70c_handoff(),
            ratification_request=request,
            authority_profile=_v71a_authority_profile(),
            request_scope_boundary=_v71a_scope_boundary(),
        )


def test_v197_bundle_rejects_advisory_profile_for_non_deferred_request() -> None:
    request = _v71a_request()
    first_row = request.request_rows[0].model_copy(
        update={"authority_profile_refs": ["authority:v71a:support-reviewer:advisory-only"]}
    )
    request = request.model_copy(update={"request_rows": [first_row, *request.request_rows[1:]]})

    with pytest.raises(ValueError, match="non-deferred requests"):
        validate_v71a_candidate_ratification_review_bundle(
            classification_summary=_v70c_summary(),
            pre_ratification_handoff=_v70c_handoff(),
            ratification_request=request,
            authority_profile=_v71a_authority_profile(),
            request_scope_boundary=_v71a_scope_boundary(),
        )
