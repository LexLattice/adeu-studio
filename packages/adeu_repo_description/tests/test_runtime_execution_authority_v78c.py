from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_PRE_EXECUTION_AUTHORITY_REVIEW_HANDOFF_SCHEMA,
    REPO_RUNTIME_AUTHORITY_READINESS_SUMMARY_SCHEMA,
    REPO_RUNTIME_EXECUTION_AUTHORITY_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    RepoCommandScopeAuthorizationBoundary,
    RepoPreExecutionAuthorityReviewHandoff,
    RepoRuntimeAuthorityExceptionRegister,
    RepoRuntimeAuthorityNonActionGuardrail,
    RepoRuntimeAuthorityReadinessSummary,
    RepoRuntimeExecutionAuthorityDecision,
    RepoRuntimeExecutionAuthorityFamilyCloseoutAlignment,
    RepoRuntimeExecutionAuthorityRequest,
    RepoToolUsePermissionEnvelope,
    derive_v78c_runtime_execution_authority_closeout_bundle,
    validate_v78c_runtime_execution_authority_closeout_bundle,
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


def _v78b_decision() -> RepoRuntimeExecutionAuthorityDecision:
    return RepoRuntimeExecutionAuthorityDecision.model_validate(
        _load_fixture(
            "vnext_plus219",
            "repo_runtime_execution_authority_decision_v219_reference.json",
        )
    )


def _v78b_tool_permission() -> RepoToolUsePermissionEnvelope:
    return RepoToolUsePermissionEnvelope.model_validate(
        _load_fixture(
            "vnext_plus219",
            "repo_tool_use_permission_envelope_v219_reference.json",
        )
    )


def _v78b_command_scope() -> RepoCommandScopeAuthorizationBoundary:
    return RepoCommandScopeAuthorizationBoundary.model_validate(
        _load_fixture(
            "vnext_plus219",
            "repo_command_scope_authorization_boundary_v219_reference.json",
        )
    )


def _v78b_exceptions() -> RepoRuntimeAuthorityExceptionRegister:
    return RepoRuntimeAuthorityExceptionRegister.model_validate(
        _load_fixture(
            "vnext_plus219",
            "repo_runtime_authority_exception_register_v219_reference.json",
        )
    )


def _v78c_summary() -> RepoRuntimeAuthorityReadinessSummary:
    return RepoRuntimeAuthorityReadinessSummary.model_validate(
        _load_fixture(
            "vnext_plus220",
            "repo_runtime_authority_readiness_summary_v220_reference.json",
        )
    )


def _v78c_handoff() -> RepoPreExecutionAuthorityReviewHandoff:
    return RepoPreExecutionAuthorityReviewHandoff.model_validate(
        _load_fixture(
            "vnext_plus220",
            "repo_pre_execution_authority_review_handoff_v220_reference.json",
        )
    )


def _v78c_closeout() -> RepoRuntimeExecutionAuthorityFamilyCloseoutAlignment:
    return RepoRuntimeExecutionAuthorityFamilyCloseoutAlignment.model_validate(
        _load_fixture(
            "vnext_plus220",
            "repo_runtime_execution_authority_family_closeout_alignment_v220_reference.json",
        )
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


def _validate_reference_bundle_with(
    *,
    summary: RepoRuntimeAuthorityReadinessSummary | None = None,
    handoff: RepoPreExecutionAuthorityReviewHandoff | None = None,
    closeout: RepoRuntimeExecutionAuthorityFamilyCloseoutAlignment | None = None,
) -> None:
    validate_v78c_runtime_execution_authority_closeout_bundle(
        runtime_execution_authority_request=_v78a_request(),
        runtime_authority_non_action_guardrail=_v78a_guardrail(),
        runtime_execution_authority_decision=_v78b_decision(),
        tool_use_permission_envelope=_v78b_tool_permission(),
        command_scope_authorization_boundary=_v78b_command_scope(),
        runtime_authority_exception_register=_v78b_exceptions(),
        runtime_authority_readiness_summary=summary or _v78c_summary(),
        pre_execution_authority_review_handoff=handoff or _v78c_handoff(),
        runtime_execution_authority_family_closeout_alignment=closeout or _v78c_closeout(),
    )


def test_v220_reference_bundle_validates() -> None:
    summary = _v78c_summary()
    handoff = _v78c_handoff()
    closeout = _v78c_closeout()

    assert summary.schema == REPO_RUNTIME_AUTHORITY_READINESS_SUMMARY_SCHEMA
    assert handoff.schema == REPO_PRE_EXECUTION_AUTHORITY_REVIEW_HANDOFF_SCHEMA
    assert closeout.schema == REPO_RUNTIME_EXECUTION_AUTHORITY_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
    assert {row.summary_posture for row in summary.summary_rows} == {
        "authority_ready_with_nonblocking_warnings",
        "blocked_by_product_authority_gap",
    }
    assert {row.handoff_target for row in handoff.handoff_rows} == {
        "future_product_review",
        "future_runtime_execution_review",
    }
    assert closeout.closeout_rows[0].closed_slice_ladder == [
        "V78-A",
        "V78-B",
        "V78-C",
    ]

    _validate_reference_bundle_with(summary=summary, handoff=handoff, closeout=closeout)


def test_v220_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_runtime_authority_readiness_summary.v1.json").validate(
        _load_fixture(
            "vnext_plus220",
            "repo_runtime_authority_readiness_summary_v220_reference.json",
        )
    )
    _schema_validator("repo_pre_execution_authority_review_handoff.v1.json").validate(
        _load_fixture(
            "vnext_plus220",
            "repo_pre_execution_authority_review_handoff_v220_reference.json",
        )
    )
    _schema_validator(
        "repo_runtime_execution_authority_family_closeout_alignment.v1.json"
    ).validate(
        _load_fixture(
            "vnext_plus220",
            "repo_runtime_execution_authority_family_closeout_alignment_v220_reference.json",
        )
    )


def test_v220_derivation_helper_matches_reference_fixtures() -> None:
    summary, handoff, closeout = derive_v78c_runtime_execution_authority_closeout_bundle(
        repo_root=_repo_root()
    )

    assert summary.model_dump(mode="json") == _load_fixture(
        "vnext_plus220",
        "repo_runtime_authority_readiness_summary_v220_reference.json",
    )
    assert handoff.model_dump(mode="json") == _load_fixture(
        "vnext_plus220",
        "repo_pre_execution_authority_review_handoff_v220_reference.json",
    )
    assert closeout.model_dump(mode="json") == _load_fixture(
        "vnext_plus220",
        "repo_runtime_execution_authority_family_closeout_alignment_v220_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_runtime_execution_authority_v220_reject_summary_ready_with_blocker.json",
            RepoRuntimeAuthorityReadinessSummary,
            "ready posture cannot carry blocking exceptions",
        ),
        (
            "repo_runtime_execution_authority_v220_reject_handoff_executes.json",
            RepoPreExecutionAuthorityReviewHandoff,
            "pre-execution handoffs must not perform execution",
        ),
        (
            "repo_runtime_execution_authority_v220_reject_product_handoff_without_authority.json",
            RepoPreExecutionAuthorityReviewHandoff,
            "product handoffs require product authority refs",
        ),
        (
            "repo_runtime_execution_authority_v220_reject_closeout_selects_v79.json",
            RepoRuntimeExecutionAuthorityFamilyCloseoutAlignment,
            "runtime authority closeout must not select V79",
        ),
    ],
)
def test_v220_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoRuntimeAuthorityReadinessSummary
        | RepoPreExecutionAuthorityReviewHandoff
        | RepoRuntimeExecutionAuthorityFamilyCloseoutAlignment
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus220", fixture_name))


def test_v220_bundle_rejects_unknown_authority_request_ref() -> None:
    summary = RepoRuntimeAuthorityReadinessSummary.model_validate(
        _load_fixture(
            "vnext_plus220",
            "repo_runtime_execution_authority_v220_reject_summary_unknown_request.json",
        )
    )

    handoff_payload = _v78c_handoff().model_dump(mode="json")
    handoff_payload["runtime_authority_readiness_summary_id"] = (
        summary.runtime_authority_readiness_summary_id
    )
    handoff = RepoPreExecutionAuthorityReviewHandoff.model_validate(
        _rehash_surface(
            handoff_payload,
            surface_name="repo_pre_execution_authority_review_handoff",
            schema=REPO_PRE_EXECUTION_AUTHORITY_REVIEW_HANDOFF_SCHEMA,
            id_field="pre_execution_authority_review_handoff_id",
        )
    )

    closeout_payload = _v78c_closeout().model_dump(mode="json")
    closeout_payload["runtime_authority_readiness_summary_id"] = (
        summary.runtime_authority_readiness_summary_id
    )
    closeout_payload["pre_execution_authority_review_handoff_id"] = (
        handoff.pre_execution_authority_review_handoff_id
    )
    closeout = RepoRuntimeExecutionAuthorityFamilyCloseoutAlignment.model_validate(
        _rehash_surface(
            closeout_payload,
            surface_name="repo_runtime_execution_authority_family_closeout_alignment",
            schema=REPO_RUNTIME_EXECUTION_AUTHORITY_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            id_field="runtime_execution_authority_family_closeout_alignment_id",
        )
    )

    with pytest.raises(
        ValueError,
        match="runtime authority summaries must reference known requests",
    ):
        _validate_reference_bundle_with(summary=summary, handoff=handoff, closeout=closeout)
