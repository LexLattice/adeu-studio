from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_RUNTIME_AUTHORITY_NON_ACTION_GUARDRAIL_SCHEMA,
    REPO_RUNTIME_AUTHORITY_SOURCE_INDEX_SCHEMA,
    REPO_RUNTIME_EXECUTION_AUTHORITY_REQUEST_SCHEMA,
    RepoRuntimeAuthorityNonActionGuardrail,
    RepoRuntimeAuthoritySourceIndex,
    RepoRuntimeExecutionAuthorityRequest,
    derive_v78a_repo_runtime_authority_non_action_guardrail,
    derive_v78a_runtime_execution_authority_bundle,
    validate_v78a_runtime_execution_authority_bundle,
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


def _v78a_source_index() -> RepoRuntimeAuthoritySourceIndex:
    return RepoRuntimeAuthoritySourceIndex.model_validate(
        _load_fixture(
            "vnext_plus218",
            "repo_runtime_authority_source_index_v218_reference.json",
        )
    )


def _v78a_request() -> RepoRuntimeExecutionAuthorityRequest:
    return RepoRuntimeExecutionAuthorityRequest.model_validate(
        _load_fixture(
            "vnext_plus218",
            "repo_runtime_execution_authority_request_v218_reference.json",
        )
    )


def _v78a_guardrail() -> RepoRuntimeAuthorityNonActionGuardrail:
    return RepoRuntimeAuthorityNonActionGuardrail.model_validate(
        _load_fixture(
            "vnext_plus218",
            "repo_runtime_authority_non_action_guardrail_v218_reference.json",
        )
    )


def _validate_reference_bundle_with(
    *,
    source_index: RepoRuntimeAuthoritySourceIndex | None = None,
    request: RepoRuntimeExecutionAuthorityRequest | None = None,
    guardrail: RepoRuntimeAuthorityNonActionGuardrail | None = None,
) -> None:
    validate_v78a_runtime_execution_authority_bundle(
        runtime_authority_source_index=source_index or _v78a_source_index(),
        runtime_execution_authority_request=request or _v78a_request(),
        runtime_authority_non_action_guardrail=guardrail or _v78a_guardrail(),
    )


def test_v218_reference_bundle_validates() -> None:
    source_index = _v78a_source_index()
    request = _v78a_request()
    guardrail = _v78a_guardrail()

    assert source_index.schema == REPO_RUNTIME_AUTHORITY_SOURCE_INDEX_SCHEMA
    assert request.schema == REPO_RUNTIME_EXECUTION_AUTHORITY_REQUEST_SCHEMA
    assert guardrail.schema == REPO_RUNTIME_AUTHORITY_NON_ACTION_GUARDRAIL_SCHEMA
    assert {row.authority_request_posture for row in request.request_rows} == {
        "blocked_by_product_authority_gap",
        "eligible_for_runtime_execution_authority_review",
    }
    assert {row.execution_posture for row in request.request_rows} == {
        "no_execution_performed_by_v78"
    }
    assert {row.tool_invocation_posture for row in request.request_rows} == {
        "no_tool_invocation_performed_by_v78"
    }
    assert {row.execution_posture for row in guardrail.guardrail_rows} == {
        "no_execution_performed_by_v78"
    }

    _validate_reference_bundle_with(
        source_index=source_index,
        request=request,
        guardrail=guardrail,
    )


def test_v218_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_runtime_authority_source_index.v1.json").validate(
        _load_fixture(
            "vnext_plus218",
            "repo_runtime_authority_source_index_v218_reference.json",
        )
    )
    _schema_validator("repo_runtime_execution_authority_request.v1.json").validate(
        _load_fixture(
            "vnext_plus218",
            "repo_runtime_execution_authority_request_v218_reference.json",
        )
    )
    _schema_validator("repo_runtime_authority_non_action_guardrail.v1.json").validate(
        _load_fixture(
            "vnext_plus218",
            "repo_runtime_authority_non_action_guardrail_v218_reference.json",
        )
    )


def test_v218_derivation_helper_matches_reference_fixtures() -> None:
    source_index, request, guardrail = derive_v78a_runtime_execution_authority_bundle(
        repo_root=_repo_root()
    )

    assert source_index.model_dump(mode="json") == _load_fixture(
        "vnext_plus218",
        "repo_runtime_authority_source_index_v218_reference.json",
    )
    assert request.model_dump(mode="json") == _load_fixture(
        "vnext_plus218",
        "repo_runtime_execution_authority_request_v218_reference.json",
    )
    assert guardrail.model_dump(mode="json") == _load_fixture(
        "vnext_plus218",
        "repo_runtime_authority_non_action_guardrail_v218_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_runtime_execution_authority_v218_reject_missing_source_without_absence_posture.json",
            RepoRuntimeAuthoritySourceIndex,
            "non-absence runtime authority source rows must be present",
        ),
        (
            "repo_runtime_execution_authority_v218_reject_request_without_source_refs.json",
            RepoRuntimeExecutionAuthorityRequest,
            "at least 1 item",
        ),
        (
            "repo_runtime_execution_authority_v218_reject_untyped_authority_source_ref.json",
            RepoRuntimeExecutionAuthorityRequest,
            "required authority source refs must resolve to row-shaped records",
        ),
        (
            "repo_runtime_execution_authority_v218_reject_product_pressure_runtime_ready.json",
            RepoRuntimeExecutionAuthorityRequest,
            "product/external pressure is not runtime-authority-ready",
        ),
        (
            "repo_runtime_execution_authority_v218_reject_external_branch_runtime_ready.json",
            RepoRuntimeExecutionAuthorityRequest,
            "product/external pressure is not runtime-authority-ready",
        ),
        (
            "repo_runtime_execution_authority_v218_reject_command_intent_as_execution.json",
            RepoRuntimeExecutionAuthorityRequest,
            "V78-A request rows must not perform execution",
        ),
        (
            "repo_runtime_execution_authority_v218_reject_tool_invocation_permission.json",
            RepoRuntimeExecutionAuthorityRequest,
            "V78-A request rows must not invoke tools",
        ),
        (
            "repo_runtime_execution_authority_v218_reject_local_command_output_authority.json",
            RepoRuntimeExecutionAuthorityRequest,
            "Extra inputs are not permitted",
        ),
        (
            "repo_runtime_execution_authority_v218_reject_command_scope_authorization.json",
            RepoRuntimeExecutionAuthorityRequest,
            "V78-A must not emit command-scope authorization refs",
        ),
        (
            "repo_runtime_execution_authority_v218_reject_empty_forbidden_runtime_actions.json",
            RepoRuntimeAuthorityNonActionGuardrail,
            "at least 1 item",
        ),
        (
            "repo_runtime_execution_authority_v218_reject_empty_forbidden_downstream_authority.json",
            RepoRuntimeAuthorityNonActionGuardrail,
            "at least 1 item",
        ),
        (
            "repo_runtime_execution_authority_v218_reject_guardrail_execution_permission.json",
            RepoRuntimeAuthorityNonActionGuardrail,
            "runtime authority guardrails must preserve no-execution posture",
        ),
        (
            "repo_runtime_execution_authority_v218_reject_guardrail_tool_invocation.json",
            RepoRuntimeAuthorityNonActionGuardrail,
            "runtime authority guardrails may not invoke tools",
        ),
    ],
)
def test_v218_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoRuntimeAuthoritySourceIndex
        | RepoRuntimeExecutionAuthorityRequest
        | RepoRuntimeAuthorityNonActionGuardrail
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus218", fixture_name))


def test_v218_bundle_rejects_support_only_eligibility_sources() -> None:
    request = RepoRuntimeExecutionAuthorityRequest.model_validate(
        _load_fixture(
            "vnext_plus218",
            "repo_runtime_execution_authority_v218_reject_support_only_eligibility.json",
        )
    )
    guardrail = derive_v78a_repo_runtime_authority_non_action_guardrail(
        repo_root=_repo_root(),
        runtime_execution_authority_request=request,
    )

    with pytest.raises(
        ValueError,
        match="eligible runtime authority requests require released V77-C sources",
    ):
        validate_v78a_runtime_execution_authority_bundle(
            runtime_authority_source_index=_v78a_source_index(),
            runtime_execution_authority_request=request,
            runtime_authority_non_action_guardrail=guardrail,
        )


def test_v218_bundle_rejects_unknown_source_ref() -> None:
    request_payload = _v78a_request().model_dump(mode="json")
    request_payload["request_rows"][0]["source_refs"] = sorted(
        [
            *request_payload["request_rows"][0]["source_refs"],
            "docs/not-a-v78-source.md",
        ]
    )
    request_payload["runtime_execution_authority_request_id"] = _surface_id(
        "repo_runtime_execution_authority_request",
        REPO_RUNTIME_EXECUTION_AUTHORITY_REQUEST_SCHEMA,
        request_payload,
        "runtime_execution_authority_request_id",
    )
    request = RepoRuntimeExecutionAuthorityRequest.model_validate(request_payload)
    guardrail = derive_v78a_repo_runtime_authority_non_action_guardrail(
        repo_root=_repo_root(),
        runtime_execution_authority_request=request,
    )

    with pytest.raises(ValueError, match="runtime authority request source refs must be known"):
        _validate_reference_bundle_with(request=request, guardrail=guardrail)


def test_v218_bundle_rejects_mismatched_request_provenance() -> None:
    request_payload = _v78a_request().model_dump(mode="json")
    request_payload["source_set_id"] = "source-set:v78a:mixed-provenance"
    request_payload["runtime_execution_authority_request_id"] = _surface_id(
        "repo_runtime_execution_authority_request",
        REPO_RUNTIME_EXECUTION_AUTHORITY_REQUEST_SCHEMA,
        request_payload,
        "runtime_execution_authority_request_id",
    )
    request = RepoRuntimeExecutionAuthorityRequest.model_validate(request_payload)
    guardrail = derive_v78a_repo_runtime_authority_non_action_guardrail(
        repo_root=_repo_root(),
        runtime_execution_authority_request=request,
    )

    with pytest.raises(
        ValueError,
        match="runtime authority request provenance must match source index",
    ):
        _validate_reference_bundle_with(request=request, guardrail=guardrail)


def test_v218_bundle_rejects_guardrail_missing_authority_gap_ref() -> None:
    guardrail_payload = _v78a_guardrail().model_dump(mode="json")
    guardrail_payload["guardrail_rows"][0]["authority_gap_refs"] = []
    guardrail_payload["runtime_authority_non_action_guardrail_id"] = _surface_id(
        "repo_runtime_authority_non_action_guardrail",
        REPO_RUNTIME_AUTHORITY_NON_ACTION_GUARDRAIL_SCHEMA,
        guardrail_payload,
        "runtime_authority_non_action_guardrail_id",
    )
    guardrail = RepoRuntimeAuthorityNonActionGuardrail.model_validate(guardrail_payload)

    with pytest.raises(
        ValueError,
        match="runtime authority guardrails must carry authority gap refs",
    ):
        _validate_reference_bundle_with(guardrail=guardrail)


def test_v218_rejects_auxiliary_verb_runtime_authority_claims() -> None:
    request_payload = _v78a_request().model_dump(mode="json")
    request_payload["request_rows"][0][
        "limitation_note"
    ] = "This row says execution is authorized."

    with pytest.raises(
        ValidationError,
        match="may not carry runtime action or authority",
    ):
        RepoRuntimeExecutionAuthorityRequest.model_validate(request_payload)
