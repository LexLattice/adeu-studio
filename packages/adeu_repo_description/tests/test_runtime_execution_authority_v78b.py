from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_COMMAND_SCOPE_AUTHORIZATION_BOUNDARY_SCHEMA,
    REPO_RUNTIME_AUTHORITY_EXCEPTION_REGISTER_SCHEMA,
    REPO_RUNTIME_EXECUTION_AUTHORITY_DECISION_SCHEMA,
    REPO_TOOL_USE_PERMISSION_ENVELOPE_SCHEMA,
    RepoCommandScopeAuthorizationBoundary,
    RepoRuntimeAuthorityExceptionRegister,
    RepoRuntimeAuthorityNonActionGuardrail,
    RepoRuntimeExecutionAuthorityDecision,
    RepoRuntimeExecutionAuthorityRequest,
    RepoToolUsePermissionEnvelope,
    derive_v78b_repo_runtime_execution_authority_decision,
    derive_v78b_repo_tool_use_permission_envelope,
    derive_v78b_runtime_execution_authority_bundle,
    validate_v78b_runtime_execution_authority_bundle,
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


def _v78b_exceptions() -> RepoRuntimeAuthorityExceptionRegister:
    return RepoRuntimeAuthorityExceptionRegister.model_validate(
        _load_fixture(
            "vnext_plus219",
            "repo_runtime_authority_exception_register_v219_reference.json",
        )
    )


def _v78b_command_scope() -> RepoCommandScopeAuthorizationBoundary:
    return RepoCommandScopeAuthorizationBoundary.model_validate(
        _load_fixture(
            "vnext_plus219",
            "repo_command_scope_authorization_boundary_v219_reference.json",
        )
    )


def _v78b_tool_permission() -> RepoToolUsePermissionEnvelope:
    return RepoToolUsePermissionEnvelope.model_validate(
        _load_fixture(
            "vnext_plus219",
            "repo_tool_use_permission_envelope_v219_reference.json",
        )
    )


def _v78b_decision() -> RepoRuntimeExecutionAuthorityDecision:
    return RepoRuntimeExecutionAuthorityDecision.model_validate(
        _load_fixture(
            "vnext_plus219",
            "repo_runtime_execution_authority_decision_v219_reference.json",
        )
    )


def _validate_reference_bundle_with(
    *,
    exceptions: RepoRuntimeAuthorityExceptionRegister | None = None,
    command_scope: RepoCommandScopeAuthorizationBoundary | None = None,
    tool_permission: RepoToolUsePermissionEnvelope | None = None,
    decision: RepoRuntimeExecutionAuthorityDecision | None = None,
) -> None:
    validate_v78b_runtime_execution_authority_bundle(
        runtime_execution_authority_request=_v78a_request(),
        runtime_authority_non_action_guardrail=_v78a_guardrail(),
        runtime_execution_authority_decision=decision or _v78b_decision(),
        tool_use_permission_envelope=tool_permission or _v78b_tool_permission(),
        command_scope_authorization_boundary=command_scope or _v78b_command_scope(),
        runtime_authority_exception_register=exceptions or _v78b_exceptions(),
    )


def _rehash_surface(
    payload: dict[str, Any],
    *,
    surface_name: str,
    schema: str,
    id_field: str,
) -> dict[str, Any]:
    payload[id_field] = _surface_id(surface_name, schema, payload, id_field)
    return payload


def test_v219_reference_bundle_validates() -> None:
    exceptions = _v78b_exceptions()
    command_scope = _v78b_command_scope()
    tool_permission = _v78b_tool_permission()
    decision = _v78b_decision()

    assert exceptions.schema == REPO_RUNTIME_AUTHORITY_EXCEPTION_REGISTER_SCHEMA
    assert command_scope.schema == REPO_COMMAND_SCOPE_AUTHORIZATION_BOUNDARY_SCHEMA
    assert tool_permission.schema == REPO_TOOL_USE_PERMISSION_ENVELOPE_SCHEMA
    assert decision.schema == REPO_RUNTIME_EXECUTION_AUTHORITY_DECISION_SCHEMA
    assert {row.exception_posture for row in exceptions.exception_rows} == {
        "blocking",
        "warning_only",
    }
    assert {row.execution_posture for row in command_scope.command_scope_rows} == {
        "no_execution_performed_by_v78"
    }
    assert {row.tool_invocation_posture for row in tool_permission.permission_rows} == {
        "no_tool_invocation_performed_by_v78"
    }
    assert {row.execution_authorization_posture for row in decision.decision_rows} == {
        "execution_not_authorized_by_v78"
    }

    _validate_reference_bundle_with(
        exceptions=exceptions,
        command_scope=command_scope,
        tool_permission=tool_permission,
        decision=decision,
    )


def test_v219_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_runtime_authority_exception_register.v1.json").validate(
        _load_fixture(
            "vnext_plus219",
            "repo_runtime_authority_exception_register_v219_reference.json",
        )
    )
    _schema_validator("repo_command_scope_authorization_boundary.v1.json").validate(
        _load_fixture(
            "vnext_plus219",
            "repo_command_scope_authorization_boundary_v219_reference.json",
        )
    )
    _schema_validator("repo_tool_use_permission_envelope.v1.json").validate(
        _load_fixture(
            "vnext_plus219",
            "repo_tool_use_permission_envelope_v219_reference.json",
        )
    )
    _schema_validator("repo_runtime_execution_authority_decision.v1.json").validate(
        _load_fixture(
            "vnext_plus219",
            "repo_runtime_execution_authority_decision_v219_reference.json",
        )
    )


def test_v219_derivation_helper_matches_reference_fixtures() -> None:
    (
        _request,
        _guardrail,
        exceptions,
        command_scope,
        tool_permission,
        decision,
    ) = derive_v78b_runtime_execution_authority_bundle(repo_root=_repo_root())

    assert exceptions.model_dump(mode="json") == _load_fixture(
        "vnext_plus219",
        "repo_runtime_authority_exception_register_v219_reference.json",
    )
    assert command_scope.model_dump(mode="json") == _load_fixture(
        "vnext_plus219",
        "repo_command_scope_authorization_boundary_v219_reference.json",
    )
    assert tool_permission.model_dump(mode="json") == _load_fixture(
        "vnext_plus219",
        "repo_tool_use_permission_envelope_v219_reference.json",
    )
    assert decision.model_dump(mode="json") == _load_fixture(
        "vnext_plus219",
        "repo_runtime_execution_authority_decision_v219_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_runtime_execution_authority_v219_reject_decision_exec_authorized.json",
            RepoRuntimeExecutionAuthorityDecision,
            "V78-B decisions must not authorize execution",
        ),
        (
            "repo_runtime_execution_authority_v219_reject_decision_grant_without_authority.json",
            RepoRuntimeExecutionAuthorityDecision,
            "grant-like decisions require authority source refs",
        ),
        (
            "repo_runtime_execution_authority_v219_reject_tool_global_permission.json",
            RepoToolUsePermissionEnvelope,
            "tool-use permission may not be global",
        ),
        (
            "repo_runtime_execution_authority_v219_reject_tool_invocation.json",
            RepoToolUsePermissionEnvelope,
            "tool-use permission envelopes must not invoke tools",
        ),
        (
            "repo_runtime_execution_authority_v219_reject_command_scope_glob_target.json",
            RepoCommandScopeAuthorizationBoundary,
            "may not contain glob target boundaries",
        ),
        (
            "repo_runtime_execution_authority_v219_reject_command_scope_no_telemetry.json",
            RepoCommandScopeAuthorizationBoundary,
            "bounded command scope requires telemetry refs",
        ),
        (
            "repo_runtime_execution_authority_v219_reject_exception_resolved_by_prose.json",
            RepoRuntimeAuthorityExceptionRegister,
            "runtime authority exceptions cannot be resolved by prose",
        ),
    ],
)
def test_v219_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoRuntimeExecutionAuthorityDecision
        | RepoToolUsePermissionEnvelope
        | RepoCommandScopeAuthorizationBoundary
        | RepoRuntimeAuthorityExceptionRegister
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus219", fixture_name))


def test_v219_bundle_rejects_unknown_authority_request_ref() -> None:
    decision = RepoRuntimeExecutionAuthorityDecision.model_validate(
        _load_fixture(
            "vnext_plus219",
            "repo_runtime_execution_authority_v219_reject_decision_unknown_request.json",
        )
    )

    with pytest.raises(
        ValueError,
        match="runtime authority decisions must reference known requests",
    ):
        _validate_reference_bundle_with(decision=decision)


def test_v219_bundle_rejects_unknown_tool_permission_ref() -> None:
    decision = RepoRuntimeExecutionAuthorityDecision.model_validate(
        _load_fixture(
            "vnext_plus219",
            "repo_runtime_execution_authority_v219_reject_decision_unknown_tool_permission.json",
        )
    )

    with pytest.raises(
        ValueError,
        match="runtime authority decisions must reference known tool permissions",
    ):
        _validate_reference_bundle_with(decision=decision)


def test_v219_bundle_rejects_stale_decision_provenance() -> None:
    decision_payload = _v78b_decision().model_dump(mode="json")
    decision_payload["snapshot_id"] = "vNext+217-stale-mixed-snapshot"
    decision = RepoRuntimeExecutionAuthorityDecision.model_validate(
        _rehash_surface(
            decision_payload,
            surface_name="repo_runtime_execution_authority_decision",
            schema=REPO_RUNTIME_EXECUTION_AUTHORITY_DECISION_SCHEMA,
            id_field="runtime_execution_authority_decision_id",
        )
    )

    with pytest.raises(
        ValueError,
        match="runtime authority decision provenance must match V78-A requests",
    ):
        _validate_reference_bundle_with(decision=decision)


def test_v219_bundle_rejects_decision_tool_permission_candidate_mismatch() -> None:
    decision_payload = _v78b_decision().model_dump(mode="json")
    decision_payload["decision_rows"][0]["tool_use_permission_refs"] = [
        "tool-permission:v78b:self-evidencing:python-review"
    ]
    decision = RepoRuntimeExecutionAuthorityDecision.model_validate(
        _rehash_surface(
            decision_payload,
            surface_name="repo_runtime_execution_authority_decision",
            schema=REPO_RUNTIME_EXECUTION_AUTHORITY_DECISION_SCHEMA,
            id_field="runtime_execution_authority_decision_id",
        )
    )

    with pytest.raises(
        ValueError,
        match="runtime authority decision tool permissions must match candidate",
    ):
        _validate_reference_bundle_with(decision=decision)


def test_v219_bundle_rejects_decision_command_scope_candidate_mismatch() -> None:
    decision_payload = _v78b_decision().model_dump(mode="json")
    decision_payload["decision_rows"][0]["command_scope_boundary_refs"] = [
        "command-scope:v78b:self-evidencing:runtime-authority-module"
    ]
    decision = RepoRuntimeExecutionAuthorityDecision.model_validate(
        _rehash_surface(
            decision_payload,
            surface_name="repo_runtime_execution_authority_decision",
            schema=REPO_RUNTIME_EXECUTION_AUTHORITY_DECISION_SCHEMA,
            id_field="runtime_execution_authority_decision_id",
        )
    )

    with pytest.raises(
        ValueError,
        match="runtime authority decision command scopes must match candidate",
    ):
        _validate_reference_bundle_with(decision=decision)


def test_v219_tool_permission_derivation_rejects_candidate_scope_collisions() -> None:
    command_scope_payload = _v78b_command_scope().model_dump(mode="json")
    duplicate_row = dict(command_scope_payload["command_scope_rows"][1])
    duplicate_row["command_scope_ref"] = (
        "command-scope:v78b:self-evidencing:runtime-authority-module-duplicate"
    )
    command_scope_payload["command_scope_rows"].append(duplicate_row)
    command_scope = RepoCommandScopeAuthorizationBoundary.model_validate(
        _rehash_surface(
            command_scope_payload,
            surface_name="repo_command_scope_authorization_boundary",
            schema=REPO_COMMAND_SCOPE_AUTHORIZATION_BOUNDARY_SCHEMA,
            id_field="command_scope_authorization_boundary_id",
        )
    )

    with pytest.raises(
        ValueError,
        match="command scope rows must contain at most one row per candidate",
    ):
        derive_v78b_repo_tool_use_permission_envelope(
            runtime_execution_authority_request=_v78a_request(),
            command_scope_authorization_boundary=command_scope,
            runtime_authority_exception_register=_v78b_exceptions(),
        )


def test_v219_decision_derivation_rejects_candidate_permission_collisions() -> None:
    permission_payload = _v78b_tool_permission().model_dump(mode="json")
    duplicate_row = dict(permission_payload["permission_rows"][1])
    duplicate_row["tool_permission_ref"] = (
        "tool-permission:v78b:self-evidencing:python-review-duplicate"
    )
    permission_payload["permission_rows"].append(duplicate_row)
    tool_permission = RepoToolUsePermissionEnvelope.model_validate(
        _rehash_surface(
            permission_payload,
            surface_name="repo_tool_use_permission_envelope",
            schema=REPO_TOOL_USE_PERMISSION_ENVELOPE_SCHEMA,
            id_field="tool_use_permission_envelope_id",
        )
    )

    with pytest.raises(
        ValueError,
        match="tool permission rows must contain at most one row per candidate",
    ):
        derive_v78b_repo_runtime_execution_authority_decision(
            runtime_execution_authority_request=_v78a_request(),
            runtime_authority_non_action_guardrail=_v78a_guardrail(),
            tool_use_permission_envelope=tool_permission,
            command_scope_authorization_boundary=_v78b_command_scope(),
            runtime_authority_exception_register=_v78b_exceptions(),
        )
