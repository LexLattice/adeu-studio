from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_ACTION_EFFECT_ENVELOPE_SCHEMA,
    REPO_COMMAND_PREFLIGHT_CONTRACT_SCHEMA,
    REPO_RUNTIME_ROLLBACK_CONTRACT_SCHEMA,
    REPO_RUNTIME_TELEMETRY_REQUIREMENT_SCHEMA,
    RepoActionEffectEnvelope,
    RepoCommandPreflightContract,
    RepoRuntimeNonExecutionGuardrail,
    RepoRuntimePermissionReviewRequest,
    RepoRuntimeRollbackContract,
    RepoRuntimeTelemetryRequirement,
    derive_v77b_repo_action_effect_envelope,
    derive_v77b_repo_runtime_rollback_contract,
    derive_v77b_repo_runtime_telemetry_requirement,
    derive_v77b_runtime_preflight_bundle,
    validate_v77b_runtime_preflight_bundle,
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


def _v77b_preflight() -> RepoCommandPreflightContract:
    return RepoCommandPreflightContract.model_validate(
        _load_fixture(
            "vnext_plus216",
            "repo_command_preflight_contract_v216_reference.json",
        )
    )


def _v77b_envelope() -> RepoActionEffectEnvelope:
    return RepoActionEffectEnvelope.model_validate(
        _load_fixture(
            "vnext_plus216",
            "repo_action_effect_envelope_v216_reference.json",
        )
    )


def _v77b_telemetry() -> RepoRuntimeTelemetryRequirement:
    return RepoRuntimeTelemetryRequirement.model_validate(
        _load_fixture(
            "vnext_plus216",
            "repo_runtime_telemetry_requirement_v216_reference.json",
        )
    )


def _v77b_rollback() -> RepoRuntimeRollbackContract:
    return RepoRuntimeRollbackContract.model_validate(
        _load_fixture(
            "vnext_plus216",
            "repo_runtime_rollback_contract_v216_reference.json",
        )
    )


def _validate_reference_bundle_with(
    *,
    preflight: RepoCommandPreflightContract | None = None,
    envelope: RepoActionEffectEnvelope | None = None,
    telemetry: RepoRuntimeTelemetryRequirement | None = None,
    rollback: RepoRuntimeRollbackContract | None = None,
) -> None:
    validate_v77b_runtime_preflight_bundle(
        runtime_permission_review_request=_v77a_request(),
        runtime_non_execution_guardrail=_v77a_guardrail(),
        command_preflight_contract=preflight or _v77b_preflight(),
        action_effect_envelope=envelope or _v77b_envelope(),
        runtime_telemetry_requirement=telemetry or _v77b_telemetry(),
        runtime_rollback_contract=rollback or _v77b_rollback(),
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


def test_v216_reference_bundle_validates() -> None:
    preflight = _v77b_preflight()
    envelope = _v77b_envelope()
    telemetry = _v77b_telemetry()
    rollback = _v77b_rollback()

    assert preflight.schema == REPO_COMMAND_PREFLIGHT_CONTRACT_SCHEMA
    assert envelope.schema == REPO_ACTION_EFFECT_ENVELOPE_SCHEMA
    assert telemetry.schema == REPO_RUNTIME_TELEMETRY_REQUIREMENT_SCHEMA
    assert rollback.schema == REPO_RUNTIME_ROLLBACK_CONTRACT_SCHEMA
    assert {row.execution_posture for row in preflight.preflight_rows} == {
        "no_execution_authorized"
    }
    assert {row.effect_acceptance_posture for row in envelope.effect_envelope_rows} == {
        "no_effect_accepted"
    }
    assert {row.telemetry_posture for row in telemetry.telemetry_requirement_rows} == {
        "telemetry_future_family_only",
        "telemetry_required_later",
    }
    assert {row.rollback_posture for row in rollback.rollback_contract_rows} == {
        "rollback_future_family_only",
        "rollback_required_later",
    }

    _validate_reference_bundle_with(
        preflight=preflight,
        envelope=envelope,
        telemetry=telemetry,
        rollback=rollback,
    )


def test_v216_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_command_preflight_contract.v1.json").validate(
        _load_fixture(
            "vnext_plus216",
            "repo_command_preflight_contract_v216_reference.json",
        )
    )
    _schema_validator("repo_action_effect_envelope.v1.json").validate(
        _load_fixture(
            "vnext_plus216",
            "repo_action_effect_envelope_v216_reference.json",
        )
    )
    _schema_validator("repo_runtime_telemetry_requirement.v1.json").validate(
        _load_fixture(
            "vnext_plus216",
            "repo_runtime_telemetry_requirement_v216_reference.json",
        )
    )
    _schema_validator("repo_runtime_rollback_contract.v1.json").validate(
        _load_fixture(
            "vnext_plus216",
            "repo_runtime_rollback_contract_v216_reference.json",
        )
    )


def test_v216_derivation_helper_matches_reference_fixtures() -> None:
    preflight, envelope, telemetry, rollback = derive_v77b_runtime_preflight_bundle(
        repo_root=_repo_root()
    )

    assert preflight.model_dump(mode="json") == _load_fixture(
        "vnext_plus216",
        "repo_command_preflight_contract_v216_reference.json",
    )
    assert envelope.model_dump(mode="json") == _load_fixture(
        "vnext_plus216",
        "repo_action_effect_envelope_v216_reference.json",
    )
    assert telemetry.model_dump(mode="json") == _load_fixture(
        "vnext_plus216",
        "repo_runtime_telemetry_requirement_v216_reference.json",
    )
    assert rollback.model_dump(mode="json") == _load_fixture(
        "vnext_plus216",
        "repo_runtime_rollback_contract_v216_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_runtime_permission_v216_reject_command_intent_as_execution.json",
            RepoCommandPreflightContract,
            "must not authorize execution",
        ),
        (
            "repo_runtime_permission_v216_reject_target_glob_boundary.json",
            RepoCommandPreflightContract,
            "may not contain glob target boundaries",
        ),
        (
            "repo_runtime_permission_v216_reject_effect_accepted.json",
            RepoActionEffectEnvelope,
            "may not carry runtime or downstream authority",
        ),
        (
            "repo_runtime_permission_v216_reject_telemetry_success_without_source.json",
            RepoRuntimeTelemetryRequirement,
            "telemetry source-present rows require checked source refs",
        ),
        (
            "repo_runtime_permission_v216_reject_rollback_verified_without_source.json",
            RepoRuntimeRollbackContract,
            "rollback source-present rows require rollback source refs",
        ),
        (
            "repo_runtime_permission_v216_reject_v77c_surface_emitted.json",
            RepoCommandPreflightContract,
            "Extra inputs are not permitted",
        ),
    ],
)
def test_v216_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoCommandPreflightContract
        | RepoActionEffectEnvelope
        | RepoRuntimeTelemetryRequirement
        | RepoRuntimeRollbackContract
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus216", fixture_name))


def test_v216_bundle_rejects_unknown_runtime_review_ref() -> None:
    preflight = RepoCommandPreflightContract.model_validate(
        _load_fixture(
            "vnext_plus216",
            "repo_runtime_permission_v216_reject_unknown_runtime_review_ref.json",
        )
    )
    envelope = derive_v77b_repo_action_effect_envelope(command_preflight_contract=preflight)
    telemetry = derive_v77b_repo_runtime_telemetry_requirement(
        command_preflight_contract=preflight,
        action_effect_envelope=envelope,
    )
    rollback = derive_v77b_repo_runtime_rollback_contract(
        command_preflight_contract=preflight,
        action_effect_envelope=envelope,
    )

    with pytest.raises(
        ValueError,
        match="preflight runtime review refs must be known V77-A refs",
    ):
        _validate_reference_bundle_with(
            preflight=preflight,
            envelope=envelope,
            telemetry=telemetry,
            rollback=rollback,
        )


def test_v216_bundle_rejects_unknown_guardrail_ref() -> None:
    preflight = RepoCommandPreflightContract.model_validate(
        _load_fixture(
            "vnext_plus216",
            "repo_runtime_permission_v216_reject_unknown_guardrail_ref.json",
        )
    )
    envelope = derive_v77b_repo_action_effect_envelope(command_preflight_contract=preflight)
    telemetry = derive_v77b_repo_runtime_telemetry_requirement(
        command_preflight_contract=preflight,
        action_effect_envelope=envelope,
    )
    rollback = derive_v77b_repo_runtime_rollback_contract(
        command_preflight_contract=preflight,
        action_effect_envelope=envelope,
    )

    with pytest.raises(
        ValueError,
        match="preflight guardrail refs must be known V77-A refs",
    ):
        _validate_reference_bundle_with(
            preflight=preflight,
            envelope=envelope,
            telemetry=telemetry,
            rollback=rollback,
        )


def test_v216_bundle_rejects_effect_guardrail_candidate_mismatch() -> None:
    envelope_payload = _v77b_envelope().model_dump(mode="json")
    envelope_payload["effect_envelope_rows"][1]["non_execution_guardrail_refs"] = [
        "guardrail:v77a:product-wedge:non-execution"
    ]
    envelope = RepoActionEffectEnvelope.model_validate(
        _rehash_surface(
            envelope_payload,
            surface_name="repo_action_effect_envelope",
            schema=REPO_ACTION_EFFECT_ENVELOPE_SCHEMA,
            id_field="action_effect_envelope_id",
        )
    )
    telemetry = derive_v77b_repo_runtime_telemetry_requirement(
        command_preflight_contract=_v77b_preflight(),
        action_effect_envelope=envelope,
    )
    rollback = derive_v77b_repo_runtime_rollback_contract(
        command_preflight_contract=_v77b_preflight(),
        action_effect_envelope=envelope,
    )

    with pytest.raises(
        ValueError,
        match="effect envelope guardrails must match candidate",
    ):
        _validate_reference_bundle_with(envelope=envelope, telemetry=telemetry, rollback=rollback)


def test_v216_bundle_rejects_telemetry_candidate_mismatch() -> None:
    telemetry_payload = _v77b_telemetry().model_dump(mode="json")
    telemetry_payload["telemetry_requirement_rows"][1]["preflight_refs"] = [
        "preflight:v77b:product-wedge:blocked"
    ]
    telemetry = RepoRuntimeTelemetryRequirement.model_validate(
        _rehash_surface(
            telemetry_payload,
            surface_name="repo_runtime_telemetry_requirement",
            schema=REPO_RUNTIME_TELEMETRY_REQUIREMENT_SCHEMA,
            id_field="runtime_telemetry_requirement_id",
        )
    )

    with pytest.raises(
        ValueError,
        match="telemetry rows must match preflight candidate",
    ):
        _validate_reference_bundle_with(telemetry=telemetry)


def test_v216_bundle_rejects_rollback_candidate_mismatch() -> None:
    rollback_payload = _v77b_rollback().model_dump(mode="json")
    rollback_payload["rollback_contract_rows"][1]["effect_envelope_refs"] = [
        "effect-envelope:v77b:product-wedge:blocked"
    ]
    rollback = RepoRuntimeRollbackContract.model_validate(
        _rehash_surface(
            rollback_payload,
            surface_name="repo_runtime_rollback_contract",
            schema=REPO_RUNTIME_ROLLBACK_CONTRACT_SCHEMA,
            id_field="runtime_rollback_contract_id",
        )
    )

    with pytest.raises(
        ValueError,
        match="rollback rows must match effect candidate",
    ):
        _validate_reference_bundle_with(rollback=rollback)
