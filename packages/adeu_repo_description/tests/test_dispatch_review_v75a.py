from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_DISPATCH_NON_EXECUTION_GUARDRAIL_SCHEMA,
    REPO_DISPATCH_REVIEW_REQUEST_SCHEMA,
    REPO_DISPATCH_SOURCE_INDEX_SCHEMA,
    RepoDispatchNonExecutionGuardrail,
    RepoDispatchReviewRequest,
    RepoDispatchSourceIndex,
    derive_v75a_dispatch_review_bundle,
    derive_v75a_repo_dispatch_non_execution_guardrail,
    validate_v75a_dispatch_review_bundle,
)
from adeu_repo_description.candidate_review_classification import _surface_id
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


def _v75a_source_index() -> RepoDispatchSourceIndex:
    return RepoDispatchSourceIndex.model_validate(
        _load_fixture("vnext_plus209", "repo_dispatch_source_index_v209_reference.json")
    )


def _v75a_request() -> RepoDispatchReviewRequest:
    return RepoDispatchReviewRequest.model_validate(
        _load_fixture("vnext_plus209", "repo_dispatch_review_request_v209_reference.json")
    )


def _v75a_guardrail() -> RepoDispatchNonExecutionGuardrail:
    return RepoDispatchNonExecutionGuardrail.model_validate(
        _load_fixture(
            "vnext_plus209",
            "repo_dispatch_non_execution_guardrail_v209_reference.json",
        )
    )


def _validate_reference_bundle_with(
    *,
    source_index: RepoDispatchSourceIndex | None = None,
    request: RepoDispatchReviewRequest | None = None,
    guardrail: RepoDispatchNonExecutionGuardrail | None = None,
) -> None:
    validate_v75a_dispatch_review_bundle(
        dispatch_source_index=source_index or _v75a_source_index(),
        dispatch_review_request=request or _v75a_request(),
        dispatch_non_execution_guardrail=guardrail or _v75a_guardrail(),
    )


def test_v209_reference_bundle_validates() -> None:
    source_index = _v75a_source_index()
    request = _v75a_request()
    guardrail = _v75a_guardrail()

    assert source_index.schema == REPO_DISPATCH_SOURCE_INDEX_SCHEMA
    assert request.schema == REPO_DISPATCH_REVIEW_REQUEST_SCHEMA
    assert guardrail.schema == REPO_DISPATCH_NON_EXECUTION_GUARDRAIL_SCHEMA
    assert {row.dispatch_review_posture for row in request.request_rows} == {
        "blocked_by_required_later_authority",
        "eligible_for_dispatch_review",
    }
    assert {row.requested_orchestration_horizon for row in request.request_rows} == {
        "multi_worker_orchestration_review",
        "product_review_later",
    }

    _validate_reference_bundle_with(
        source_index=source_index,
        request=request,
        guardrail=guardrail,
    )


def test_v209_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_dispatch_source_index.v1.json").validate(
        _load_fixture("vnext_plus209", "repo_dispatch_source_index_v209_reference.json")
    )
    _schema_validator("repo_dispatch_review_request.v1.json").validate(
        _load_fixture("vnext_plus209", "repo_dispatch_review_request_v209_reference.json")
    )
    _schema_validator("repo_dispatch_non_execution_guardrail.v1.json").validate(
        _load_fixture(
            "vnext_plus209",
            "repo_dispatch_non_execution_guardrail_v209_reference.json",
        )
    )


def test_v209_derivation_helper_matches_reference_fixtures() -> None:
    source_index, request, guardrail = derive_v75a_dispatch_review_bundle(repo_root=_repo_root())

    assert source_index.model_dump(mode="json") == _load_fixture(
        "vnext_plus209",
        "repo_dispatch_source_index_v209_reference.json",
    )
    assert request.model_dump(mode="json") == _load_fixture(
        "vnext_plus209",
        "repo_dispatch_review_request_v209_reference.json",
    )
    assert guardrail.model_dump(mode="json") == _load_fixture(
        "vnext_plus209",
        "repo_dispatch_non_execution_guardrail_v209_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_dispatch_review_v209_reject_missing_source_without_absence_posture.json",
            RepoDispatchSourceIndex,
            "non-absence dispatch source rows must be present",
        ),
        (
            "repo_dispatch_review_v209_reject_missing_v74c_handoff.json",
            RepoDispatchReviewRequest,
            "eligible dispatch-review requests require V74-C handoff refs",
        ),
        (
            "repo_dispatch_review_v209_reject_worker_assignment.json",
            RepoDispatchReviewRequest,
            "may not carry dispatch or downstream authority",
        ),
        (
            "repo_dispatch_review_v209_reject_command_execution.json",
            RepoDispatchReviewRequest,
            "may not carry dispatch or downstream authority",
        ),
        (
            "repo_dispatch_review_v209_reject_workbench_action_authority.json",
            RepoDispatchReviewRequest,
            "may not carry dispatch or downstream authority",
        ),
        (
            "repo_dispatch_review_v209_reject_product_without_authority_blocker.json",
            RepoDispatchReviewRequest,
            "product review pressure requires product authority blocker",
        ),
        (
            "repo_dispatch_review_v209_reject_runtime_without_authority_blocker.json",
            RepoDispatchReviewRequest,
            "eligible dispatch-review requests require dispatch authority gap",
        ),
        (
            "repo_dispatch_review_v209_reject_external_without_v43_branch.json",
            RepoDispatchReviewRequest,
            "product/runtime/external pressure is not eligible in V75-A",
        ),
        (
            "repo_dispatch_review_v209_reject_native_dispatch_exception_ref.json",
            RepoDispatchReviewRequest,
            "V75-A may only carry upstream V74 exception refs",
        ),
        (
            "repo_dispatch_review_v209_reject_free_floating_later_authority.json",
            RepoDispatchReviewRequest,
            "required later authority refs must resolve to row-shaped records",
        ),
        (
            "repo_dispatch_review_v209_reject_empty_guardrail_forbidden_actions.json",
            RepoDispatchNonExecutionGuardrail,
            "at least 1 item",
        ),
    ],
)
def test_v209_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoDispatchSourceIndex | RepoDispatchReviewRequest | RepoDispatchNonExecutionGuardrail
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus209", fixture_name))


def test_v209_bundle_rejects_support_only_eligibility_sources() -> None:
    source_index = _v75a_source_index()
    request = RepoDispatchReviewRequest.model_validate(
        _load_fixture(
            "vnext_plus209",
            "repo_dispatch_review_v209_reject_support_only_eligibility.json",
        )
    )
    guardrail = derive_v75a_repo_dispatch_non_execution_guardrail(
        repo_root=_repo_root(),
        dispatch_review_request=request,
    )

    with pytest.raises(
        ValueError,
        match="eligible dispatch-review requests require released V74-C eligibility sources",
    ):
        validate_v75a_dispatch_review_bundle(
            dispatch_source_index=source_index,
            dispatch_review_request=request,
            dispatch_non_execution_guardrail=guardrail,
        )


def test_v209_bundle_rejects_unknown_source_ref() -> None:
    request_payload = _v75a_request().model_dump(mode="json")
    request_payload["request_rows"][1]["source_refs"] = sorted(
        [*request_payload["request_rows"][1]["source_refs"], "docs/not-a-v75-source.md"]
    )
    request_payload["dispatch_review_request_id"] = _surface_id(
        "repo_dispatch_review_request",
        REPO_DISPATCH_REVIEW_REQUEST_SCHEMA,
        request_payload,
        "dispatch_review_request_id",
    )
    request = RepoDispatchReviewRequest.model_validate(request_payload)
    guardrail = derive_v75a_repo_dispatch_non_execution_guardrail(
        repo_root=_repo_root(),
        dispatch_review_request=request,
    )

    with pytest.raises(ValueError, match="dispatch request source refs must be known"):
        _validate_reference_bundle_with(request=request, guardrail=guardrail)
