from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_WORK_PACKET_ACTIVATION_NON_EXECUTION_GUARDRAIL_SCHEMA,
    REPO_WORK_PACKET_ACTIVATION_REVIEW_REQUEST_SCHEMA,
    REPO_WORK_PACKET_ACTIVATION_SOURCE_INDEX_SCHEMA,
    RepoWorkPacketActivationNonExecutionGuardrail,
    RepoWorkPacketActivationReviewRequest,
    RepoWorkPacketActivationSourceIndex,
    derive_v84a_work_packet_activation_review_bundle,
    validate_v84a_work_packet_activation_review_bundle,
)
from adeu_repo_description.semantic_implementation_spec import (
    derive_v83c_semantic_implementation_projection_bundle,
)
from adeu_repo_description.work_packet_activation_review import _reject_v84_action_claim
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


def _v84a_source_index(
    name: str = "repo_work_packet_activation_source_index_v236_reference.json",
) -> RepoWorkPacketActivationSourceIndex:
    return RepoWorkPacketActivationSourceIndex.model_validate(_load_fixture("vnext_plus236", name))


def _v84a_request(
    name: str = "repo_work_packet_activation_review_request_v236_reference.json",
) -> RepoWorkPacketActivationReviewRequest:
    return RepoWorkPacketActivationReviewRequest.model_validate(
        _load_fixture("vnext_plus236", name)
    )


def _v84a_guardrail(
    name: str = "repo_work_packet_activation_non_execution_guardrail_v236_reference.json",
) -> RepoWorkPacketActivationNonExecutionGuardrail:
    return RepoWorkPacketActivationNonExecutionGuardrail.model_validate(
        _load_fixture("vnext_plus236", name)
    )


def _validate_reference_bundle_with(
    *,
    source_index: RepoWorkPacketActivationSourceIndex | None = None,
    request: RepoWorkPacketActivationReviewRequest | None = None,
    guardrail: RepoWorkPacketActivationNonExecutionGuardrail | None = None,
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
    ) = derive_v83c_semantic_implementation_projection_bundle()
    validate_v84a_work_packet_activation_review_bundle(
        v83_intent_source_index=v83_source_index,
        v83_semantic_intent_contract=v83_contract,
        v83_intent_non_implementation_guardrail=v83_guardrail,
        v83_intent_edge_decomposition=v83_edge_decomposition,
        v83_artifact_obligation_map=v83_obligation_map,
        v83_semantic_drift_ambiguity_register=v83_drift_register,
        v83_implementation_spec_projection_packet=v83_projection_packet,
        v83_intent_to_work_packet_handoff=v83_handoff,
        v83_semantic_implementation_spec_family_closeout_alignment=v83_closeout,
        work_packet_activation_source_index=source_index or _v84a_source_index(),
        work_packet_activation_review_request=request or _v84a_request(),
        work_packet_activation_non_execution_guardrail=guardrail or _v84a_guardrail(),
    )


def test_v84a_reference_fixtures_match_derivation() -> None:
    *_, source_index, request, guardrail = derive_v84a_work_packet_activation_review_bundle()
    assert source_index.model_dump(mode="json") == _load_fixture(
        "vnext_plus236",
        "repo_work_packet_activation_source_index_v236_reference.json",
    )
    assert request.model_dump(mode="json") == _load_fixture(
        "vnext_plus236",
        "repo_work_packet_activation_review_request_v236_reference.json",
    )
    assert guardrail.model_dump(mode="json") == _load_fixture(
        "vnext_plus236",
        "repo_work_packet_activation_non_execution_guardrail_v236_reference.json",
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name"),
    [
        (
            REPO_WORK_PACKET_ACTIVATION_SOURCE_INDEX_SCHEMA,
            "repo_work_packet_activation_source_index.v1.json",
            "repo_work_packet_activation_source_index_v236_reference.json",
        ),
        (
            REPO_WORK_PACKET_ACTIVATION_REVIEW_REQUEST_SCHEMA,
            "repo_work_packet_activation_review_request.v1.json",
            "repo_work_packet_activation_review_request_v236_reference.json",
        ),
        (
            REPO_WORK_PACKET_ACTIVATION_NON_EXECUTION_GUARDRAIL_SCHEMA,
            "repo_work_packet_activation_non_execution_guardrail.v1.json",
            "repo_work_packet_activation_non_execution_guardrail_v236_reference.json",
        ),
    ],
)
def test_v84a_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
) -> None:
    payload = _load_fixture("vnext_plus236", fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)


def test_v84a_reference_bundle_links_released_v83c_substrate() -> None:
    _validate_reference_bundle_with()


def test_v84a_reference_preserves_activation_review_boundary() -> None:
    request = _v84a_request()
    eligible_rows = [
        row
        for row in request.activation_request_rows
        if row.activation_review_eligibility_posture
        == "eligible_for_work_packet_activation_review"
    ]
    assert len(eligible_rows) == 1
    eligible = eligible_rows[0]
    assert eligible.activation_package_ref
    assert eligible.activation_authority_posture == "no_activation_authority_granted_by_v84"
    assert eligible.implementation_lock_status == "no_implementation_lock_created_by_v84"
    assert eligible.activation_execution_posture == "no_activation_performed_by_v84"
    assert eligible.work_packet_execution_posture == "no_work_packet_execution_performed_by_v84"
    assert eligible.implementation_execution_posture == "no_implementation_performed_by_v84"
    assert eligible.target_surface_posture == "bounded_for_later_review"
    assert eligible.validation_evidence_posture == "edge_bound_for_later_review"
    assert eligible.canonical_lock_requirement == "canonical_implementation_lock_required"


@pytest.mark.parametrize(
    ("fixture_name", "message"),
    [
        (
            "repo_work_packet_activation_v236_reject_generated_candidate_missing_provenance.json",
            "generated candidates require V83 projection and quality gate refs",
        ),
        (
            "repo_work_packet_activation_v236_reject_stale_source_index_id.json",
            "work_packet_activation_source_index_id must match canonical surface id",
        ),
    ],
)
def test_v84a_source_index_rejects_invalid_rows(fixture_name: str, message: str) -> None:
    with pytest.raises(ValidationError, match=message):
        RepoWorkPacketActivationSourceIndex.model_validate(
            _load_fixture("vnext_plus236", fixture_name)
        )


@pytest.mark.parametrize(
    ("fixture_name", "message"),
    [
        (
            "repo_work_packet_activation_v236_reject_support_only_eligible.json",
            "support or absence-only requests cannot be eligible",
        ),
        (
            "repo_work_packet_activation_v236_reject_missing_quality_gate.json",
            "eligible activation review requires quality_gate_refs",
        ),
        (
            "repo_work_packet_activation_v236_reject_carried_blocker_eligible.json",
            "eligible activation review may not carry blockers",
        ),
        (
            "repo_work_packet_activation_v236_reject_tests_only_validation.json",
            "eligible activation review requires edge-bound validation evidence",
        ),
        (
            "repo_work_packet_activation_v236_reject_ready_to_implement_now.json",
            "may not carry V84 activation or implementation authority",
        ),
        (
            "repo_work_packet_activation_v236_reject_missing_guardrail_ref.json",
            "List should have at least 1 item",
        ),
    ],
)
def test_v84a_requests_reject_activation_or_implementation_leaks(
    fixture_name: str,
    message: str,
) -> None:
    with pytest.raises(ValidationError, match=message):
        RepoWorkPacketActivationReviewRequest.model_validate(
            _load_fixture("vnext_plus236", fixture_name)
        )


def test_v84a_bundle_rejects_request_guardrail_mismatch() -> None:
    guardrail = _v84a_guardrail(
        "repo_work_packet_activation_v236_reject_guardrail_request_mismatch.json"
    )
    with pytest.raises(ValueError, match="activation request guardrails must link back to request"):
        _validate_reference_bundle_with(guardrail=guardrail)


def test_v84a_action_claim_scanner_allows_negated_suffixes() -> None:
    note = "Work-packet authority granted is forbidden; no implementation occurs."
    assert _reject_v84_action_claim(note, field_name="limitation_note") == note


@pytest.mark.parametrize(
    ("fixture_name", "message"),
    [
        (
            "repo_work_packet_activation_v236_reject_guardrail_missing_forbidden_runtime.json",
            "guardrails must forbid required runtime actions",
        ),
        (
            "repo_work_packet_activation_v236_reject_guardrail_v85_selection_claim.json",
            "may not carry V84 activation or implementation authority",
        ),
    ],
)
def test_v84a_guardrails_reject_missing_or_overreaching_prohibitions(
    fixture_name: str,
    message: str,
) -> None:
    with pytest.raises(ValidationError, match=message):
        RepoWorkPacketActivationNonExecutionGuardrail.model_validate(
            _load_fixture("vnext_plus236", fixture_name)
        )
