from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_POST_RUNTIME_PERMISSION_REVIEW_HANDOFF_SCHEMA,
    REPO_RUNTIME_PERMISSION_AUTHORITY_POSTURE_SCHEMA,
    REPO_RUNTIME_PERMISSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_RUNTIME_PERMISSION_REVIEW_SUMMARY_SCHEMA,
    RepoActionEffectEnvelope,
    RepoCommandPreflightContract,
    RepoPostRuntimePermissionReviewHandoff,
    RepoRuntimePermissionAuthorityPosture,
    RepoRuntimePermissionFamilyCloseoutAlignment,
    RepoRuntimePermissionReviewRequest,
    RepoRuntimePermissionReviewSummary,
    RepoRuntimeRollbackContract,
    RepoRuntimeTelemetryRequirement,
    derive_v77c_runtime_permission_closeout_bundle,
    validate_v77c_runtime_permission_closeout_bundle,
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


def _v77c_authority() -> RepoRuntimePermissionAuthorityPosture:
    return RepoRuntimePermissionAuthorityPosture.model_validate(
        _load_fixture(
            "vnext_plus217",
            "repo_runtime_permission_authority_posture_v217_reference.json",
        )
    )


def _v77c_summary() -> RepoRuntimePermissionReviewSummary:
    return RepoRuntimePermissionReviewSummary.model_validate(
        _load_fixture(
            "vnext_plus217",
            "repo_runtime_permission_review_summary_v217_reference.json",
        )
    )


def _v77c_handoff() -> RepoPostRuntimePermissionReviewHandoff:
    return RepoPostRuntimePermissionReviewHandoff.model_validate(
        _load_fixture(
            "vnext_plus217",
            "repo_post_runtime_permission_review_handoff_v217_reference.json",
        )
    )


def _v77c_closeout() -> RepoRuntimePermissionFamilyCloseoutAlignment:
    return RepoRuntimePermissionFamilyCloseoutAlignment.model_validate(
        _load_fixture(
            "vnext_plus217",
            "repo_runtime_permission_family_closeout_alignment_v217_reference.json",
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


def test_v217_reference_bundle_validates() -> None:
    authority = _v77c_authority()
    summary = _v77c_summary()
    handoff = _v77c_handoff()
    closeout = _v77c_closeout()

    assert authority.schema == REPO_RUNTIME_PERMISSION_AUTHORITY_POSTURE_SCHEMA
    assert summary.schema == REPO_RUNTIME_PERMISSION_REVIEW_SUMMARY_SCHEMA
    assert handoff.schema == REPO_POST_RUNTIME_PERMISSION_REVIEW_HANDOFF_SCHEMA
    assert closeout.schema == REPO_RUNTIME_PERMISSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
    assert {row.authority_decision_posture for row in authority.authority_posture_rows} == {
        "authority_future_family_only",
        "authority_required_later",
    }
    assert {row.runtime_permission_execution_posture for row in handoff.handoff_rows} == {
        "no_runtime_permission_granted_by_v77"
    }
    assert closeout.closeout_rows[0].closed_slice_ladder == ["V77-A", "V77-B", "V77-C"]

    validate_v77c_runtime_permission_closeout_bundle(
        runtime_permission_review_request=_v77a_request(),
        command_preflight_contract=_v77b_preflight(),
        action_effect_envelope=_v77b_envelope(),
        runtime_telemetry_requirement=_v77b_telemetry(),
        runtime_rollback_contract=_v77b_rollback(),
        runtime_permission_authority_posture=authority,
        runtime_permission_review_summary=summary,
        post_runtime_permission_review_handoff=handoff,
        runtime_permission_family_closeout_alignment=closeout,
    )


def test_v217_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_runtime_permission_authority_posture.v1.json").validate(
        _load_fixture(
            "vnext_plus217",
            "repo_runtime_permission_authority_posture_v217_reference.json",
        )
    )
    _schema_validator("repo_runtime_permission_review_summary.v1.json").validate(
        _load_fixture(
            "vnext_plus217",
            "repo_runtime_permission_review_summary_v217_reference.json",
        )
    )
    _schema_validator("repo_post_runtime_permission_review_handoff.v1.json").validate(
        _load_fixture(
            "vnext_plus217",
            "repo_post_runtime_permission_review_handoff_v217_reference.json",
        )
    )
    _schema_validator("repo_runtime_permission_family_closeout_alignment.v1.json").validate(
        _load_fixture(
            "vnext_plus217",
            "repo_runtime_permission_family_closeout_alignment_v217_reference.json",
        )
    )


def test_v217_derivation_helper_matches_reference_fixtures() -> None:
    authority, summary, handoff, closeout = derive_v77c_runtime_permission_closeout_bundle(
        repo_root=_repo_root()
    )

    assert authority.model_dump(mode="json") == _load_fixture(
        "vnext_plus217",
        "repo_runtime_permission_authority_posture_v217_reference.json",
    )
    assert summary.model_dump(mode="json") == _load_fixture(
        "vnext_plus217",
        "repo_runtime_permission_review_summary_v217_reference.json",
    )
    assert handoff.model_dump(mode="json") == _load_fixture(
        "vnext_plus217",
        "repo_post_runtime_permission_review_handoff_v217_reference.json",
    )
    assert closeout.model_dump(mode="json") == _load_fixture(
        "vnext_plus217",
        "repo_runtime_permission_family_closeout_alignment_v217_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_runtime_permission_v217_reject_authority_grants_runtime_permission.json",
            RepoRuntimePermissionAuthorityPosture,
            "may not carry runtime or downstream authority",
        ),
        (
            "repo_runtime_permission_v217_reject_summary_ready_with_blockers.json",
            RepoRuntimePermissionReviewSummary,
            "ready posture cannot carry blockers",
        ),
        (
            "repo_runtime_permission_v217_reject_handoff_grants_runtime_permission.json",
            RepoPostRuntimePermissionReviewHandoff,
            "Input should be 'no_runtime_permission_granted_by_v77'",
        ),
        (
            "repo_runtime_permission_v217_reject_product_handoff_without_authority.json",
            RepoPostRuntimePermissionReviewHandoff,
            "target requires matching authority kind",
        ),
        (
            "repo_runtime_permission_v217_reject_closeout_bad_slice_ladder.json",
            RepoRuntimePermissionFamilyCloseoutAlignment,
            "values must be unique",
        ),
    ],
)
def test_v217_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoRuntimePermissionAuthorityPosture
        | RepoRuntimePermissionReviewSummary
        | RepoPostRuntimePermissionReviewHandoff
        | RepoRuntimePermissionFamilyCloseoutAlignment
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus217", fixture_name))


def test_v217_bundle_rejects_unknown_summary_authority_ref() -> None:
    summary_payload = _v77c_summary().model_dump(mode="json")
    summary_payload["summary_rows"][0]["authority_posture_refs"] = [
        "authority-posture:v77c:unknown"
    ]
    summary_payload["summary_rows"][0]["carried_blocker_refs"] = [
        "authority-posture:v77c:unknown"
    ]
    summary = RepoRuntimePermissionReviewSummary.model_validate(
        _rehash_surface(
            summary_payload,
            surface_name="repo_runtime_permission_review_summary",
            schema=REPO_RUNTIME_PERMISSION_REVIEW_SUMMARY_SCHEMA,
            id_field="runtime_permission_review_summary_id",
        )
    )
    handoff_payload = _v77c_handoff().model_dump(mode="json")
    handoff_payload["runtime_permission_review_summary_id"] = (
        summary.runtime_permission_review_summary_id
    )
    handoff = RepoPostRuntimePermissionReviewHandoff.model_validate(
        _rehash_surface(
            handoff_payload,
            surface_name="repo_post_runtime_permission_review_handoff",
            schema=REPO_POST_RUNTIME_PERMISSION_REVIEW_HANDOFF_SCHEMA,
            id_field="post_runtime_permission_review_handoff_id",
        )
    )
    closeout_payload = _v77c_closeout().model_dump(mode="json")
    closeout_payload["runtime_permission_review_summary_id"] = (
        summary.runtime_permission_review_summary_id
    )
    closeout_payload["post_runtime_permission_review_handoff_id"] = (
        handoff.post_runtime_permission_review_handoff_id
    )
    closeout = RepoRuntimePermissionFamilyCloseoutAlignment.model_validate(
        _rehash_surface(
            closeout_payload,
            surface_name="repo_runtime_permission_family_closeout_alignment",
            schema=REPO_RUNTIME_PERMISSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            id_field="runtime_permission_family_closeout_alignment_id",
        )
    )

    with pytest.raises(ValueError, match="runtime summary authority refs must be known"):
        validate_v77c_runtime_permission_closeout_bundle(
            runtime_permission_review_request=_v77a_request(),
            command_preflight_contract=_v77b_preflight(),
            action_effect_envelope=_v77b_envelope(),
            runtime_telemetry_requirement=_v77b_telemetry(),
            runtime_rollback_contract=_v77b_rollback(),
            runtime_permission_authority_posture=_v77c_authority(),
            runtime_permission_review_summary=summary,
            post_runtime_permission_review_handoff=handoff,
            runtime_permission_family_closeout_alignment=closeout,
        )


def test_v217_bundle_rejects_handoff_authority_ref_without_resolved_kind() -> None:
    handoff_payload = _v77c_handoff().model_dump(mode="json")
    handoff_payload["handoff_rows"][0]["required_later_authority_refs"] = [
        "authority-posture:v77c:unknown"
    ]
    handoff = RepoPostRuntimePermissionReviewHandoff.model_validate(
        _rehash_surface(
            handoff_payload,
            surface_name="repo_post_runtime_permission_review_handoff",
            schema=REPO_POST_RUNTIME_PERMISSION_REVIEW_HANDOFF_SCHEMA,
            id_field="post_runtime_permission_review_handoff_id",
        )
    )
    closeout_payload = _v77c_closeout().model_dump(mode="json")
    closeout_payload["post_runtime_permission_review_handoff_id"] = (
        handoff.post_runtime_permission_review_handoff_id
    )
    closeout = RepoRuntimePermissionFamilyCloseoutAlignment.model_validate(
        _rehash_surface(
            closeout_payload,
            surface_name="repo_runtime_permission_family_closeout_alignment",
            schema=REPO_RUNTIME_PERMISSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            id_field="runtime_permission_family_closeout_alignment_id",
        )
    )

    with pytest.raises(ValueError, match="post-runtime handoff authority refs must be known"):
        validate_v77c_runtime_permission_closeout_bundle(
            runtime_permission_review_request=_v77a_request(),
            command_preflight_contract=_v77b_preflight(),
            action_effect_envelope=_v77b_envelope(),
            runtime_telemetry_requirement=_v77b_telemetry(),
            runtime_rollback_contract=_v77b_rollback(),
            runtime_permission_authority_posture=_v77c_authority(),
            runtime_permission_review_summary=_v77c_summary(),
            post_runtime_permission_review_handoff=handoff,
            runtime_permission_family_closeout_alignment=closeout,
        )
