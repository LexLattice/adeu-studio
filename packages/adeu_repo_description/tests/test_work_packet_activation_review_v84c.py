from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_POST_WORK_PACKET_ACTIVATION_REVIEW_HANDOFF_SCHEMA,
    REPO_WORK_PACKET_ACTIVATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_WORK_PACKET_ACTIVATION_READINESS_SUMMARY_SCHEMA,
    RepoPostWorkPacketActivationReviewHandoff,
    RepoWorkPacketActivationFamilyCloseoutAlignment,
    RepoWorkPacketActivationReadinessSummary,
    derive_v84b_work_packet_package_review_bundle,
    derive_v84c_work_packet_activation_closeout_bundle,
    validate_v84c_work_packet_activation_closeout_bundle,
)
from adeu_repo_description.work_packet_activation_review import _surface_id
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


def _rehash(payload: dict[str, Any], surface_name: str, id_field: str) -> dict[str, Any]:
    payload = deepcopy(payload)
    payload[id_field] = _surface_id(surface_name, payload["schema"], payload, id_field)
    return payload


def _v84c_summary(
    name: str = "repo_work_packet_activation_readiness_summary_v238_reference.json",
) -> RepoWorkPacketActivationReadinessSummary:
    return RepoWorkPacketActivationReadinessSummary.model_validate(
        _load_fixture("vnext_plus238", name)
    )


def _v84c_handoff(
    name: str = "repo_post_work_packet_activation_review_handoff_v238_reference.json",
) -> RepoPostWorkPacketActivationReviewHandoff:
    return RepoPostWorkPacketActivationReviewHandoff.model_validate(
        _load_fixture("vnext_plus238", name)
    )


def _v84c_closeout(
    name: str = "repo_work_packet_activation_family_closeout_alignment_v238_reference.json",
) -> RepoWorkPacketActivationFamilyCloseoutAlignment:
    return RepoWorkPacketActivationFamilyCloseoutAlignment.model_validate(
        _load_fixture("vnext_plus238", name)
    )


def _validate_reference_bundle_with(
    *,
    summary: RepoWorkPacketActivationReadinessSummary | None = None,
    handoff: RepoPostWorkPacketActivationReviewHandoff | None = None,
    closeout: RepoWorkPacketActivationFamilyCloseoutAlignment | None = None,
) -> None:
    (
        v83_source_index,
        v83_contract,
        v83_guardrail,
        v83_edge_decomposition,
        v83_obligation_map,
        v83_drift_register,
        v83_projection_packet,
        v83_handoff,
        v83_closeout,
        v84a_source_index,
        v84a_request,
        v84a_guardrail,
        v84b_scope,
        v84b_target_boundary,
        v84b_validation_plan,
        v84b_exception_register,
    ) = derive_v84b_work_packet_package_review_bundle()
    validate_v84c_work_packet_activation_closeout_bundle(
        v83_intent_source_index=v83_source_index,
        v83_semantic_intent_contract=v83_contract,
        v83_intent_non_implementation_guardrail=v83_guardrail,
        v83_intent_edge_decomposition=v83_edge_decomposition,
        v83_artifact_obligation_map=v83_obligation_map,
        v83_semantic_drift_ambiguity_register=v83_drift_register,
        v83_implementation_spec_projection_packet=v83_projection_packet,
        v83_intent_to_work_packet_handoff=v83_handoff,
        v83_semantic_implementation_spec_family_closeout_alignment=v83_closeout,
        work_packet_activation_source_index=v84a_source_index,
        work_packet_activation_review_request=v84a_request,
        work_packet_activation_non_execution_guardrail=v84a_guardrail,
        work_packet_scope_contract=v84b_scope,
        implementation_target_surface_boundary=v84b_target_boundary,
        work_packet_validation_evidence_plan=v84b_validation_plan,
        work_packet_activation_exception_register=v84b_exception_register,
        work_packet_activation_readiness_summary=summary or _v84c_summary(),
        post_work_packet_activation_review_handoff=handoff or _v84c_handoff(),
        work_packet_activation_family_closeout_alignment=closeout or _v84c_closeout(),
    )


def test_v84c_reference_fixtures_match_derivation() -> None:
    *_, summary, handoff, closeout = derive_v84c_work_packet_activation_closeout_bundle()

    assert summary.model_dump(mode="json") == _load_fixture(
        "vnext_plus238",
        "repo_work_packet_activation_readiness_summary_v238_reference.json",
    )
    assert handoff.model_dump(mode="json") == _load_fixture(
        "vnext_plus238",
        "repo_post_work_packet_activation_review_handoff_v238_reference.json",
    )
    assert closeout.model_dump(mode="json") == _load_fixture(
        "vnext_plus238",
        "repo_work_packet_activation_family_closeout_alignment_v238_reference.json",
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name"),
    [
        (
            REPO_WORK_PACKET_ACTIVATION_READINESS_SUMMARY_SCHEMA,
            "repo_work_packet_activation_readiness_summary.v1.json",
            "repo_work_packet_activation_readiness_summary_v238_reference.json",
        ),
        (
            REPO_POST_WORK_PACKET_ACTIVATION_REVIEW_HANDOFF_SCHEMA,
            "repo_post_work_packet_activation_review_handoff.v1.json",
            "repo_post_work_packet_activation_review_handoff_v238_reference.json",
        ),
        (
            REPO_WORK_PACKET_ACTIVATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            "repo_work_packet_activation_family_closeout_alignment.v1.json",
            "repo_work_packet_activation_family_closeout_alignment_v238_reference.json",
        ),
    ],
)
def test_v84c_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
) -> None:
    payload = _load_fixture("vnext_plus238", fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)


def test_v84c_reference_bundle_links_v84_package_and_preserves_boundary() -> None:
    summary = _v84c_summary()
    handoff = _v84c_handoff()
    closeout = _v84c_closeout()

    summary_row = summary.summary_rows[0]
    handoff_row = handoff.handoff_rows[0]
    assert summary_row.summary_posture == "ready_with_nonblocking_warnings"
    assert summary_row.coverage_posture == "edge_and_obligation_complete_for_review"
    assert summary_row.activation_authority_posture == "no_activation_authority_granted_by_v84"
    assert handoff_row.handoff_activation_status == "later_lock_review_requested"
    assert handoff_row.implementation_lock_status == "no_implementation_lock_created_by_v84"
    assert "v85_selection" in closeout.unselected_future_surfaces

    _validate_reference_bundle_with(summary=summary, handoff=handoff, closeout=closeout)


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "message"),
    [
        (
            "repo_work_packet_activation_v238_reject_summary_ready_with_warnings.json",
            RepoWorkPacketActivationReadinessSummary,
            "ready summaries cannot carry blockers or warnings",
        ),
        (
            "repo_work_packet_activation_v238_reject_summary_missing_coverage.json",
            RepoWorkPacketActivationReadinessSummary,
            "warning-ready summaries require complete coverage",
        ),
        (
            "repo_work_packet_activation_v238_reject_handoff_creates_lock.json",
            RepoPostWorkPacketActivationReviewHandoff,
            "cannot create implementation locks",
        ),
        (
            "repo_work_packet_activation_v238_reject_handoff_ready_with_exceptions.json",
            RepoPostWorkPacketActivationReviewHandoff,
            "ready handoffs cannot carry exceptions",
        ),
        (
            "repo_work_packet_activation_v238_reject_closeout_selects_v85.json",
            RepoWorkPacketActivationFamilyCloseoutAlignment,
            "must not select V85",
        ),
        (
            "repo_work_packet_activation_v238_reject_closeout_claims_activation.json",
            RepoWorkPacketActivationFamilyCloseoutAlignment,
            "must mention no activation",
        ),
    ],
)
def test_v84c_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoWorkPacketActivationReadinessSummary
        | RepoPostWorkPacketActivationReviewHandoff
        | RepoWorkPacketActivationFamilyCloseoutAlignment
    ],
    message: str,
) -> None:
    with pytest.raises(ValidationError, match=message):
        model_type.model_validate(_load_fixture("vnext_plus238", fixture_name))


def test_v84c_bundle_rejects_handoff_package_mismatch() -> None:
    summary = _v84c_summary()
    handoff_payload = _load_fixture(
        "vnext_plus238",
        "repo_post_work_packet_activation_review_handoff_v238_reference.json",
    )
    handoff_payload["handoff_rows"][0]["activation_package_ref"] = "activation-package:v84a:wrong"
    handoff_payload = _rehash(
        handoff_payload,
        "repo_post_work_packet_activation_review_handoff",
        "post_work_packet_activation_review_handoff_id",
    )
    closeout_payload = _load_fixture(
        "vnext_plus238",
        "repo_work_packet_activation_family_closeout_alignment_v238_reference.json",
    )
    closeout_payload["post_work_packet_activation_review_handoff_id"] = handoff_payload[
        "post_work_packet_activation_review_handoff_id"
    ]
    closeout_payload = _rehash(
        closeout_payload,
        "repo_work_packet_activation_family_closeout_alignment",
        "work_packet_activation_family_closeout_alignment_id",
    )

    with pytest.raises(ValueError, match="handoff scope refs must match activation package"):
        _validate_reference_bundle_with(
            summary=summary,
            handoff=RepoPostWorkPacketActivationReviewHandoff.model_validate(handoff_payload),
            closeout=RepoWorkPacketActivationFamilyCloseoutAlignment.model_validate(
                closeout_payload
            ),
        )
