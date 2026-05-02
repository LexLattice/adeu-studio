from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_EXTERNAL_BRANCH_NON_ACTIVATION_GUARDRAIL_SCHEMA,
    REPO_EXTERNAL_BRANCH_REVIEW_REQUEST_SCHEMA,
    REPO_EXTERNAL_BRANCH_SOURCE_INDEX_SCHEMA,
    RepoExternalBranchNonActivationGuardrail,
    RepoExternalBranchReviewRequest,
    RepoExternalBranchSourceIndex,
    derive_v80a_external_branch_review_bundle,
    derive_v80a_repo_external_branch_non_activation_guardrail,
    validate_v80a_external_branch_review_bundle,
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


def _v80a_source_index(
    name: str = "repo_external_branch_source_index_v224_reference.json",
) -> RepoExternalBranchSourceIndex:
    return RepoExternalBranchSourceIndex.model_validate(_load_fixture("vnext_plus224", name))


def _v80a_request(
    name: str = "repo_external_branch_review_request_v224_reference.json",
) -> RepoExternalBranchReviewRequest:
    return RepoExternalBranchReviewRequest.model_validate(_load_fixture("vnext_plus224", name))


def _v80a_guardrail(
    name: str = "repo_external_branch_non_activation_guardrail_v224_reference.json",
) -> RepoExternalBranchNonActivationGuardrail:
    return RepoExternalBranchNonActivationGuardrail.model_validate(
        _load_fixture("vnext_plus224", name)
    )


def _validate_reference_bundle_with(
    *,
    source_index: RepoExternalBranchSourceIndex | None = None,
    request: RepoExternalBranchReviewRequest | None = None,
    guardrail: RepoExternalBranchNonActivationGuardrail | None = None,
) -> None:
    validate_v80a_external_branch_review_bundle(
        external_branch_source_index=source_index or _v80a_source_index(),
        external_branch_review_request=request or _v80a_request(),
        external_branch_non_activation_guardrail=guardrail or _v80a_guardrail(),
    )


def test_v224_reference_bundle_validates() -> None:
    source_index = _v80a_source_index()
    request = _v80a_request()
    guardrail = _v80a_guardrail()

    assert source_index.schema == REPO_EXTERNAL_BRANCH_SOURCE_INDEX_SCHEMA
    assert request.schema == REPO_EXTERNAL_BRANCH_REVIEW_REQUEST_SCHEMA
    assert guardrail.schema == REPO_EXTERNAL_BRANCH_NON_ACTIVATION_GUARDRAIL_SCHEMA
    assert {row.branch_review_posture for row in request.request_rows} == {
        "blocked_by_missing_v43_branch_posture",
        "blocked_by_product_authority_gap",
    }
    assert {row.branch_posture_currentness for row in request.request_rows} == {
        "explicit_absence_marker"
    }
    assert {row.external_activation_posture for row in request.request_rows} == {
        "no_external_branch_activation_performed_by_v80"
    }
    assert {row.external_submission_posture for row in request.request_rows} == {
        "no_external_submission_performed_by_v80"
    }
    assert {row.external_tool_invocation_posture for row in request.request_rows} == {
        "no_external_tool_invocation_performed_by_v80"
    }
    assert {row.execution_posture for row in request.request_rows} == {
        "no_execution_performed_by_v80"
    }
    assert all(not hasattr(row, "data_boundary_refs") for row in request.request_rows)

    _validate_reference_bundle_with(
        source_index=source_index,
        request=request,
        guardrail=guardrail,
    )


def test_v224_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_external_branch_source_index.v1.json").validate(
        _load_fixture(
            "vnext_plus224",
            "repo_external_branch_source_index_v224_reference.json",
        )
    )
    _schema_validator("repo_external_branch_review_request.v1.json").validate(
        _load_fixture(
            "vnext_plus224",
            "repo_external_branch_review_request_v224_reference.json",
        )
    )
    _schema_validator("repo_external_branch_non_activation_guardrail.v1.json").validate(
        _load_fixture(
            "vnext_plus224",
            "repo_external_branch_non_activation_guardrail_v224_reference.json",
        )
    )


def test_v224_derivation_helper_matches_reference_fixtures() -> None:
    source_index, request, guardrail = derive_v80a_external_branch_review_bundle(
        repo_root=_repo_root()
    )

    assert source_index.model_dump(mode="json") == _load_fixture(
        "vnext_plus224",
        "repo_external_branch_source_index_v224_reference.json",
    )
    assert request.model_dump(mode="json") == _load_fixture(
        "vnext_plus224",
        "repo_external_branch_review_request_v224_reference.json",
    )
    assert guardrail.model_dump(mode="json") == _load_fixture(
        "vnext_plus224",
        "repo_external_branch_non_activation_guardrail_v224_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_external_branch_v224_reject_missing_source_without_absence_posture.json",
            RepoExternalBranchSourceIndex,
            "non-absence external branch source rows must be present",
        ),
        (
            "repo_external_branch_v224_reject_request_without_source_refs.json",
            RepoExternalBranchReviewRequest,
            "at least 1 item",
        ),
        (
            "repo_external_branch_v224_reject_product_pressure_external_ready.json",
            RepoExternalBranchReviewRequest,
            "product pressure must remain blocked in V80-A",
        ),
        (
            "repo_external_branch_v224_reject_external_activation_claim.json",
            RepoExternalBranchReviewRequest,
            "V80-A request rows must not activate external branches",
        ),
        (
            "repo_external_branch_v224_reject_future_surface_refs.json",
            RepoExternalBranchReviewRequest,
            "Extra inputs are not permitted",
        ),
        (
            "repo_external_branch_v224_reject_empty_forbidden_external_actions.json",
            RepoExternalBranchNonActivationGuardrail,
            "at least 1 item",
        ),
        (
            "repo_external_branch_v224_reject_empty_forbidden_downstream_authority.json",
            RepoExternalBranchNonActivationGuardrail,
            "at least 1 item",
        ),
    ],
)
def test_v224_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoExternalBranchSourceIndex
        | RepoExternalBranchReviewRequest
        | RepoExternalBranchNonActivationGuardrail
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus224", fixture_name))


def test_v224_bundle_rejects_support_only_eligibility_sources() -> None:
    request = _v80a_request("repo_external_branch_v224_reject_support_only_eligibility.json")
    guardrail = _v80a_guardrail(
        "repo_external_branch_v224_reject_support_only_eligibility_guardrail.json"
    )

    with pytest.raises(
        ValueError,
        match="eligible external branch requests require released V79-C sources",
    ):
        _validate_reference_bundle_with(request=request, guardrail=guardrail)


def test_v224_bundle_rejects_historical_v43_context_as_current_posture() -> None:
    request = _v80a_request(
        "repo_external_branch_v224_reject_historical_v43_as_current_posture.json"
    )
    guardrail = _v80a_guardrail(
        "repo_external_branch_v224_reject_historical_v43_as_current_posture_guardrail.json"
    )

    with pytest.raises(
        ValueError,
        match="eligible external branch requests require current V43 posture",
    ):
        _validate_reference_bundle_with(request=request, guardrail=guardrail)


def test_v224_bundle_rejects_external_objective_source_only_eligibility() -> None:
    source_index = _v80a_source_index(
        "repo_external_branch_v224_source_with_objective_context.json"
    )
    request = _v80a_request(
        "repo_external_branch_v224_reject_objective_source_only_eligibility.json"
    )
    guardrail = _v80a_guardrail(
        "repo_external_branch_v224_reject_objective_source_only_eligibility_guardrail.json"
    )

    with pytest.raises(
        ValueError,
        match="eligible external branch requests require current V43 posture",
    ):
        _validate_reference_bundle_with(
            source_index=source_index,
            request=request,
            guardrail=guardrail,
        )


def test_v224_bundle_rejects_unknown_source_ref() -> None:
    request_payload = _v80a_request().model_dump(mode="json")
    request_payload["request_rows"][0]["source_refs"] = sorted(
        [
            *request_payload["request_rows"][0]["source_refs"],
            "docs/not-a-v80-source.md",
        ]
    )
    request_payload["external_branch_review_request_id"] = _surface_id(
        "repo_external_branch_review_request",
        REPO_EXTERNAL_BRANCH_REVIEW_REQUEST_SCHEMA,
        request_payload,
        "external_branch_review_request_id",
    )
    request = RepoExternalBranchReviewRequest.model_validate(request_payload)
    guardrail = derive_v80a_repo_external_branch_non_activation_guardrail(
        repo_root=_repo_root(),
        external_branch_review_request=request,
    )

    with pytest.raises(ValueError, match="external branch request source refs must be known"):
        _validate_reference_bundle_with(request=request, guardrail=guardrail)


@pytest.mark.parametrize(
    ("source_name_fragment", "match"),
    [
        (
            "repo_controlled_execution_review_summary",
            "V79-C summary refs require a controlled-execution summary source",
        ),
        (
            "repo_post_controlled_execution_review_handoff",
            "V79-C handoff refs require a post-review handoff source",
        ),
    ],
)
def test_v224_bundle_rejects_v79_refs_without_matching_source_role(
    source_name_fragment: str,
    match: str,
) -> None:
    request_payload = _v80a_request().model_dump(mode="json")
    request_row = next(
        row
        for row in request_payload["request_rows"]
        if row["candidate_ref"] == "candidate:internal:self_evidencing_workflow_type_emergence"
    )
    request_row["source_refs"] = [
        source_ref
        for source_ref in request_row["source_refs"]
        if source_name_fragment not in source_ref
    ]
    request_payload["external_branch_review_request_id"] = _surface_id(
        "repo_external_branch_review_request",
        REPO_EXTERNAL_BRANCH_REVIEW_REQUEST_SCHEMA,
        request_payload,
        "external_branch_review_request_id",
    )
    request = RepoExternalBranchReviewRequest.model_validate(request_payload)
    guardrail = derive_v80a_repo_external_branch_non_activation_guardrail(
        repo_root=_repo_root(),
        external_branch_review_request=request,
    )

    with pytest.raises(ValueError, match=match):
        _validate_reference_bundle_with(request=request, guardrail=guardrail)


def test_v224_bundle_rejects_mismatched_request_provenance() -> None:
    request_payload = _v80a_request().model_dump(mode="json")
    request_payload["source_set_id"] = "source-set:v80a:mixed-provenance"
    request_payload["external_branch_review_request_id"] = _surface_id(
        "repo_external_branch_review_request",
        REPO_EXTERNAL_BRANCH_REVIEW_REQUEST_SCHEMA,
        request_payload,
        "external_branch_review_request_id",
    )
    request = RepoExternalBranchReviewRequest.model_validate(request_payload)
    guardrail = derive_v80a_repo_external_branch_non_activation_guardrail(
        repo_root=_repo_root(),
        external_branch_review_request=request,
    )

    with pytest.raises(
        ValueError,
        match="external branch request provenance must match source index",
    ):
        _validate_reference_bundle_with(request=request, guardrail=guardrail)


def test_v224_guardrail_derivation_preserves_multiple_guardrail_refs() -> None:
    request_payload = _v80a_request().model_dump(mode="json")
    request_payload["request_rows"][1]["guardrail_refs"] = sorted(
        [
            *request_payload["request_rows"][1]["guardrail_refs"],
            "guardrail:v80a:self-evidencing:secondary-non-activation",
        ]
    )
    request_payload["external_branch_review_request_id"] = _surface_id(
        "repo_external_branch_review_request",
        REPO_EXTERNAL_BRANCH_REVIEW_REQUEST_SCHEMA,
        request_payload,
        "external_branch_review_request_id",
    )
    request = RepoExternalBranchReviewRequest.model_validate(request_payload)

    guardrail = derive_v80a_repo_external_branch_non_activation_guardrail(
        repo_root=_repo_root(),
        external_branch_review_request=request,
    )

    assert {
        "guardrail:v80a:self-evidencing:non-activation",
        "guardrail:v80a:self-evidencing:secondary-non-activation",
    }.issubset({row.guardrail_ref for row in guardrail.guardrail_rows})
    _validate_reference_bundle_with(request=request, guardrail=guardrail)
