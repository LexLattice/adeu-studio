from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_RUNTIME_NON_EXECUTION_GUARDRAIL_SCHEMA,
    REPO_RUNTIME_PERMISSION_REVIEW_REQUEST_SCHEMA,
    REPO_RUNTIME_PERMISSION_SOURCE_INDEX_SCHEMA,
    RepoRuntimeNonExecutionGuardrail,
    RepoRuntimePermissionReviewRequest,
    RepoRuntimePermissionSourceIndex,
    derive_v77a_repo_runtime_non_execution_guardrail,
    derive_v77a_runtime_permission_review_bundle,
    validate_v77a_runtime_permission_review_bundle,
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


def _v77a_source_index() -> RepoRuntimePermissionSourceIndex:
    return RepoRuntimePermissionSourceIndex.model_validate(
        _load_fixture(
            "vnext_plus215",
            "repo_runtime_permission_source_index_v215_reference.json",
        )
    )


def _v77a_request() -> RepoRuntimePermissionReviewRequest:
    return RepoRuntimePermissionReviewRequest.model_validate(
        _load_fixture(
            "vnext_plus215",
            "repo_runtime_permission_review_request_v215_reference.json",
        )
    )


def _v77a_guardrail() -> RepoRuntimeNonExecutionGuardrail:
    return RepoRuntimeNonExecutionGuardrail.model_validate(
        _load_fixture(
            "vnext_plus215",
            "repo_runtime_non_execution_guardrail_v215_reference.json",
        )
    )


def _validate_reference_bundle_with(
    *,
    source_index: RepoRuntimePermissionSourceIndex | None = None,
    request: RepoRuntimePermissionReviewRequest | None = None,
    guardrail: RepoRuntimeNonExecutionGuardrail | None = None,
) -> None:
    validate_v77a_runtime_permission_review_bundle(
        runtime_permission_source_index=source_index or _v77a_source_index(),
        runtime_permission_review_request=request or _v77a_request(),
        runtime_non_execution_guardrail=guardrail or _v77a_guardrail(),
    )


def test_v215_reference_bundle_validates() -> None:
    source_index = _v77a_source_index()
    request = _v77a_request()
    guardrail = _v77a_guardrail()

    assert source_index.schema == REPO_RUNTIME_PERMISSION_SOURCE_INDEX_SCHEMA
    assert request.schema == REPO_RUNTIME_PERMISSION_REVIEW_REQUEST_SCHEMA
    assert guardrail.schema == REPO_RUNTIME_NON_EXECUTION_GUARDRAIL_SCHEMA
    assert {row.runtime_review_posture for row in request.request_rows} == {
        "blocked_by_product_authority_gap",
        "eligible_for_runtime_permission_review",
    }
    assert {row.command_execution_posture for row in request.request_rows} == {
        "no_execution_authorized"
    }
    assert {row.tool_use_posture for row in guardrail.guardrail_rows} == {
        "tool_use_not_authorized_by_v77"
    }

    _validate_reference_bundle_with(
        source_index=source_index,
        request=request,
        guardrail=guardrail,
    )


def test_v215_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_runtime_permission_source_index.v1.json").validate(
        _load_fixture(
            "vnext_plus215",
            "repo_runtime_permission_source_index_v215_reference.json",
        )
    )
    _schema_validator("repo_runtime_permission_review_request.v1.json").validate(
        _load_fixture(
            "vnext_plus215",
            "repo_runtime_permission_review_request_v215_reference.json",
        )
    )
    _schema_validator("repo_runtime_non_execution_guardrail.v1.json").validate(
        _load_fixture(
            "vnext_plus215",
            "repo_runtime_non_execution_guardrail_v215_reference.json",
        )
    )


def test_v215_derivation_helper_matches_reference_fixtures() -> None:
    source_index, request, guardrail = derive_v77a_runtime_permission_review_bundle(
        repo_root=_repo_root()
    )

    assert source_index.model_dump(mode="json") == _load_fixture(
        "vnext_plus215",
        "repo_runtime_permission_source_index_v215_reference.json",
    )
    assert request.model_dump(mode="json") == _load_fixture(
        "vnext_plus215",
        "repo_runtime_permission_review_request_v215_reference.json",
    )
    assert guardrail.model_dump(mode="json") == _load_fixture(
        "vnext_plus215",
        "repo_runtime_non_execution_guardrail_v215_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_runtime_permission_v215_reject_missing_source_without_absence_posture.json",
            RepoRuntimePermissionSourceIndex,
            "non-absence runtime source rows must be present",
        ),
        (
            "repo_runtime_permission_v215_reject_request_without_source_refs.json",
            RepoRuntimePermissionReviewRequest,
            "at least 1 item",
        ),
        (
            "repo_runtime_permission_v215_reject_product_pressure_runtime_ready.json",
            RepoRuntimePermissionReviewRequest,
            "product/external pressure is not runtime-ready",
        ),
        (
            "repo_runtime_permission_v215_reject_command_intent_as_execution.json",
            RepoRuntimePermissionReviewRequest,
            "must not authorize command execution",
        ),
        (
            "repo_runtime_permission_v215_reject_local_command_output_permission_evidence.json",
            RepoRuntimePermissionReviewRequest,
            "Extra inputs are not permitted",
        ),
        (
            "repo_runtime_permission_v215_reject_empty_forbidden_runtime_actions.json",
            RepoRuntimeNonExecutionGuardrail,
            "at least 1 item",
        ),
        (
            "repo_runtime_permission_v215_reject_empty_forbidden_downstream_authority.json",
            RepoRuntimeNonExecutionGuardrail,
            "at least 1 item",
        ),
        (
            "repo_runtime_permission_v215_reject_tool_use_permission.json",
            RepoRuntimeNonExecutionGuardrail,
            "may not authorize tool use",
        ),
        (
            "repo_runtime_permission_v215_reject_v77b_surface_emitted.json",
            RepoRuntimePermissionReviewRequest,
            "Extra inputs are not permitted",
        ),
    ],
)
def test_v215_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoRuntimePermissionSourceIndex
        | RepoRuntimePermissionReviewRequest
        | RepoRuntimeNonExecutionGuardrail
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus215", fixture_name))


def test_v215_bundle_rejects_support_only_eligibility_sources() -> None:
    request = RepoRuntimePermissionReviewRequest.model_validate(
        _load_fixture(
            "vnext_plus215",
            "repo_runtime_permission_v215_reject_support_only_eligibility.json",
        )
    )
    guardrail = derive_v77a_repo_runtime_non_execution_guardrail(
        repo_root=_repo_root(),
        runtime_permission_review_request=request,
    )

    with pytest.raises(
        ValueError,
        match="eligible runtime-review requests require released V76-C eligibility sources",
    ):
        validate_v77a_runtime_permission_review_bundle(
            runtime_permission_source_index=_v77a_source_index(),
            runtime_permission_review_request=request,
            runtime_non_execution_guardrail=guardrail,
        )


def test_v215_bundle_rejects_unknown_source_ref() -> None:
    request = RepoRuntimePermissionReviewRequest.model_validate(
        _load_fixture(
            "vnext_plus215",
            "repo_runtime_permission_v215_reject_unknown_source_ref.json",
        )
    )
    guardrail = derive_v77a_repo_runtime_non_execution_guardrail(
        repo_root=_repo_root(),
        runtime_permission_review_request=request,
    )

    with pytest.raises(ValueError, match="runtime request source refs must be known"):
        _validate_reference_bundle_with(request=request, guardrail=guardrail)


def test_v215_bundle_rejects_mismatched_request_provenance() -> None:
    request_payload = _v77a_request().model_dump(mode="json")
    request_payload["source_set_id"] = "source-set:v77a:mixed-provenance"
    request_payload["runtime_permission_review_request_id"] = _surface_id(
        "repo_runtime_permission_review_request",
        REPO_RUNTIME_PERMISSION_REVIEW_REQUEST_SCHEMA,
        request_payload,
        "runtime_permission_review_request_id",
    )
    request = RepoRuntimePermissionReviewRequest.model_validate(request_payload)
    guardrail = derive_v77a_repo_runtime_non_execution_guardrail(
        repo_root=_repo_root(),
        runtime_permission_review_request=request,
    )

    with pytest.raises(
        ValueError,
        match="runtime request provenance must match the source index",
    ):
        _validate_reference_bundle_with(request=request, guardrail=guardrail)


def test_v215_bundle_rejects_guardrail_missing_authority_gap_ref() -> None:
    guardrail_payload = _v77a_guardrail().model_dump(mode="json")
    guardrail_payload["guardrail_rows"][0]["authority_gap_refs"] = []
    guardrail_payload["runtime_non_execution_guardrail_id"] = _surface_id(
        "repo_runtime_non_execution_guardrail",
        REPO_RUNTIME_NON_EXECUTION_GUARDRAIL_SCHEMA,
        guardrail_payload,
        "runtime_non_execution_guardrail_id",
    )
    guardrail = RepoRuntimeNonExecutionGuardrail.model_validate(guardrail_payload)

    with pytest.raises(
        ValueError,
        match="runtime guardrail rows must carry authority gap refs",
    ):
        _validate_reference_bundle_with(guardrail=guardrail)
