from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CONTROLLED_EXECUTION_NON_EXECUTION_GUARDRAIL_SCHEMA,
    REPO_CONTROLLED_EXECUTION_REVIEW_REQUEST_SCHEMA,
    REPO_CONTROLLED_EXECUTION_SOURCE_INDEX_SCHEMA,
    RepoControlledExecutionNonExecutionGuardrail,
    RepoControlledExecutionReviewRequest,
    RepoControlledExecutionSourceIndex,
    derive_v79a_controlled_execution_review_bundle,
    derive_v79a_repo_controlled_execution_non_execution_guardrail,
    validate_v79a_controlled_execution_review_bundle,
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


def _v79a_source_index() -> RepoControlledExecutionSourceIndex:
    return RepoControlledExecutionSourceIndex.model_validate(
        _load_fixture(
            "vnext_plus221",
            "repo_controlled_execution_source_index_v221_reference.json",
        )
    )


def _v79a_request() -> RepoControlledExecutionReviewRequest:
    return RepoControlledExecutionReviewRequest.model_validate(
        _load_fixture(
            "vnext_plus221",
            "repo_controlled_execution_review_request_v221_reference.json",
        )
    )


def _v79a_guardrail() -> RepoControlledExecutionNonExecutionGuardrail:
    return RepoControlledExecutionNonExecutionGuardrail.model_validate(
        _load_fixture(
            "vnext_plus221",
            "repo_controlled_execution_non_execution_guardrail_v221_reference.json",
        )
    )


def _validate_reference_bundle_with(
    *,
    source_index: RepoControlledExecutionSourceIndex | None = None,
    request: RepoControlledExecutionReviewRequest | None = None,
    guardrail: RepoControlledExecutionNonExecutionGuardrail | None = None,
) -> None:
    validate_v79a_controlled_execution_review_bundle(
        controlled_execution_source_index=source_index or _v79a_source_index(),
        controlled_execution_review_request=request or _v79a_request(),
        controlled_execution_non_execution_guardrail=guardrail or _v79a_guardrail(),
    )


def test_v221_reference_bundle_validates() -> None:
    source_index = _v79a_source_index()
    request = _v79a_request()
    guardrail = _v79a_guardrail()

    assert source_index.schema == REPO_CONTROLLED_EXECUTION_SOURCE_INDEX_SCHEMA
    assert request.schema == REPO_CONTROLLED_EXECUTION_REVIEW_REQUEST_SCHEMA
    assert guardrail.schema == REPO_CONTROLLED_EXECUTION_NON_EXECUTION_GUARDRAIL_SCHEMA
    assert {row.execution_review_posture for row in request.request_rows} == {
        "blocked_by_product_authority_gap",
        "eligible_for_controlled_execution_review",
    }
    assert {row.controlled_execution_action_posture for row in request.request_rows} == {
        "no_controlled_execution_performed_by_v79"
    }
    assert {row.execution_posture for row in request.request_rows} == {
        "no_execution_performed_by_v79"
    }
    assert {row.tool_invocation_posture for row in request.request_rows} == {
        "no_tool_invocation_performed_by_v79"
    }
    assert all(not hasattr(row, "requested_run_plan_refs") for row in request.request_rows)

    _validate_reference_bundle_with(
        source_index=source_index,
        request=request,
        guardrail=guardrail,
    )


def test_v221_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_controlled_execution_source_index.v1.json").validate(
        _load_fixture(
            "vnext_plus221",
            "repo_controlled_execution_source_index_v221_reference.json",
        )
    )
    _schema_validator("repo_controlled_execution_review_request.v1.json").validate(
        _load_fixture(
            "vnext_plus221",
            "repo_controlled_execution_review_request_v221_reference.json",
        )
    )
    _schema_validator("repo_controlled_execution_non_execution_guardrail.v1.json").validate(
        _load_fixture(
            "vnext_plus221",
            "repo_controlled_execution_non_execution_guardrail_v221_reference.json",
        )
    )


def test_v221_derivation_helper_matches_reference_fixtures() -> None:
    source_index, request, guardrail = derive_v79a_controlled_execution_review_bundle(
        repo_root=_repo_root()
    )

    assert source_index.model_dump(mode="json") == _load_fixture(
        "vnext_plus221",
        "repo_controlled_execution_source_index_v221_reference.json",
    )
    assert request.model_dump(mode="json") == _load_fixture(
        "vnext_plus221",
        "repo_controlled_execution_review_request_v221_reference.json",
    )
    assert guardrail.model_dump(mode="json") == _load_fixture(
        "vnext_plus221",
        "repo_controlled_execution_non_execution_guardrail_v221_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_controlled_execution_v221_reject_missing_source_without_absence_posture.json",
            RepoControlledExecutionSourceIndex,
            "non-absence controlled execution source rows must be present",
        ),
        (
            "repo_controlled_execution_v221_reject_request_without_source_refs.json",
            RepoControlledExecutionReviewRequest,
            "at least 1 item",
        ),
        (
            "repo_controlled_execution_v221_reject_product_pressure_execution_ready.json",
            RepoControlledExecutionReviewRequest,
            "product/external pressure is not execution-review-ready",
        ),
        (
            "repo_controlled_execution_v221_reject_external_pressure_execution_ready.json",
            RepoControlledExecutionReviewRequest,
            "product/external pressure is not execution-review-ready",
        ),
        (
            "repo_controlled_execution_v221_reject_command_execution_claim.json",
            RepoControlledExecutionReviewRequest,
            "may not carry controlled execution action",
        ),
        (
            "repo_controlled_execution_v221_reject_tool_invocation_claim.json",
            RepoControlledExecutionReviewRequest,
            "V79-A request rows must not invoke tools",
        ),
        (
            "repo_controlled_execution_v221_reject_future_surface_refs.json",
            RepoControlledExecutionReviewRequest,
            "Extra inputs are not permitted",
        ),
        (
            "repo_controlled_execution_v221_reject_local_command_output_authority.json",
            RepoControlledExecutionReviewRequest,
            "Extra inputs are not permitted",
        ),
        (
            "repo_controlled_execution_v221_reject_empty_forbidden_execution_actions.json",
            RepoControlledExecutionNonExecutionGuardrail,
            "at least 1 item",
        ),
        (
            "repo_controlled_execution_v221_reject_empty_forbidden_downstream_authority.json",
            RepoControlledExecutionNonExecutionGuardrail,
            "at least 1 item",
        ),
    ],
)
def test_v221_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoControlledExecutionSourceIndex
        | RepoControlledExecutionReviewRequest
        | RepoControlledExecutionNonExecutionGuardrail
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus221", fixture_name))


def test_v221_bundle_rejects_support_only_eligibility_sources() -> None:
    request = RepoControlledExecutionReviewRequest.model_validate(
        _load_fixture(
            "vnext_plus221",
            "repo_controlled_execution_v221_reject_support_only_eligibility.json",
        )
    )
    guardrail = RepoControlledExecutionNonExecutionGuardrail.model_validate(
        _load_fixture(
            "vnext_plus221",
            "repo_controlled_execution_v221_reject_support_only_eligibility_guardrail.json",
        )
    )

    with pytest.raises(
        ValueError,
        match="eligible controlled execution requests require released V78-C sources",
    ):
        validate_v79a_controlled_execution_review_bundle(
            controlled_execution_source_index=_v79a_source_index(),
            controlled_execution_review_request=request,
            controlled_execution_non_execution_guardrail=guardrail,
        )


def test_v221_bundle_rejects_unknown_source_ref() -> None:
    request_payload = _v79a_request().model_dump(mode="json")
    request_payload["request_rows"][0]["source_refs"] = sorted(
        [
            *request_payload["request_rows"][0]["source_refs"],
            "docs/not-a-v79-source.md",
        ]
    )
    request_payload["controlled_execution_review_request_id"] = _surface_id(
        "repo_controlled_execution_review_request",
        REPO_CONTROLLED_EXECUTION_REVIEW_REQUEST_SCHEMA,
        request_payload,
        "controlled_execution_review_request_id",
    )
    request = RepoControlledExecutionReviewRequest.model_validate(request_payload)
    guardrail = derive_v79a_repo_controlled_execution_non_execution_guardrail(
        repo_root=_repo_root(),
        controlled_execution_review_request=request,
    )

    with pytest.raises(ValueError, match="controlled execution request source refs must be known"):
        _validate_reference_bundle_with(request=request, guardrail=guardrail)


@pytest.mark.parametrize(
    ("source_name_fragment", "match"),
    [
        (
            "repo_runtime_authority_readiness_summary",
            "V78-C summary refs require a readiness-summary source",
        ),
        (
            "repo_pre_execution_authority_review_handoff",
            "V78-C handoff refs require a pre-execution handoff source",
        ),
    ],
)
def test_v221_bundle_rejects_v78_refs_without_matching_source_role(
    source_name_fragment: str,
    match: str,
) -> None:
    request_payload = _v79a_request().model_dump(mode="json")
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
    request_payload["controlled_execution_review_request_id"] = _surface_id(
        "repo_controlled_execution_review_request",
        REPO_CONTROLLED_EXECUTION_REVIEW_REQUEST_SCHEMA,
        request_payload,
        "controlled_execution_review_request_id",
    )
    request = RepoControlledExecutionReviewRequest.model_validate(request_payload)
    guardrail = derive_v79a_repo_controlled_execution_non_execution_guardrail(
        repo_root=_repo_root(),
        controlled_execution_review_request=request,
    )

    with pytest.raises(ValueError, match=match):
        _validate_reference_bundle_with(request=request, guardrail=guardrail)


def test_v221_bundle_rejects_mismatched_request_provenance() -> None:
    request_payload = _v79a_request().model_dump(mode="json")
    request_payload["source_set_id"] = "source-set:v79a:mixed-provenance"
    request_payload["controlled_execution_review_request_id"] = _surface_id(
        "repo_controlled_execution_review_request",
        REPO_CONTROLLED_EXECUTION_REVIEW_REQUEST_SCHEMA,
        request_payload,
        "controlled_execution_review_request_id",
    )
    request = RepoControlledExecutionReviewRequest.model_validate(request_payload)
    guardrail = derive_v79a_repo_controlled_execution_non_execution_guardrail(
        repo_root=_repo_root(),
        controlled_execution_review_request=request,
    )

    with pytest.raises(
        ValueError,
        match="controlled execution request provenance must match source index",
    ):
        _validate_reference_bundle_with(request=request, guardrail=guardrail)


def test_v221_guardrail_derivation_preserves_multiple_guardrail_refs() -> None:
    request_payload = _v79a_request().model_dump(mode="json")
    request_payload["request_rows"][1]["guardrail_refs"] = sorted(
        [
            *request_payload["request_rows"][1]["guardrail_refs"],
            "guardrail:v79a:self-evidencing:secondary-non-execution",
        ]
    )
    request_payload["controlled_execution_review_request_id"] = _surface_id(
        "repo_controlled_execution_review_request",
        REPO_CONTROLLED_EXECUTION_REVIEW_REQUEST_SCHEMA,
        request_payload,
        "controlled_execution_review_request_id",
    )
    request = RepoControlledExecutionReviewRequest.model_validate(request_payload)

    guardrail = derive_v79a_repo_controlled_execution_non_execution_guardrail(
        repo_root=_repo_root(),
        controlled_execution_review_request=request,
    )

    assert {
        "guardrail:v79a:self-evidencing:non-execution",
        "guardrail:v79a:self-evidencing:secondary-non-execution",
    }.issubset({row.guardrail_ref for row in guardrail.guardrail_rows})
    _validate_reference_bundle_with(request=request, guardrail=guardrail)
