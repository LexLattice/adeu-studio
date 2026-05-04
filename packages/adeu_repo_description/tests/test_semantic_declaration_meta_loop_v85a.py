from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_SEMANTIC_DECLARATION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
    REPO_SEMANTIC_DECLARATION_SOURCE_INDEX_SCHEMA,
    REPO_TURN_SEMANTIC_DECLARATION_REQUEST_SCHEMA,
    RepoSemanticDeclarationNonAuthorityGuardrail,
    RepoSemanticDeclarationSourceIndex,
    RepoTurnSemanticDeclarationRequest,
    derive_v85a_repo_semantic_declaration_non_authority_guardrail,
    derive_v85a_semantic_declaration_review_bundle,
    validate_v85a_semantic_declaration_review_bundle,
)
from adeu_repo_description.semantic_declaration_meta_loop import (
    _reject_v85_authority_claim,
)
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


def _v85a_source_index(
    name: str = "repo_semantic_declaration_source_index_v239_reference.json",
) -> RepoSemanticDeclarationSourceIndex:
    return RepoSemanticDeclarationSourceIndex.model_validate(_load_fixture("vnext_plus239", name))


def _v85a_request(
    name: str = "repo_turn_semantic_declaration_request_v239_reference.json",
) -> RepoTurnSemanticDeclarationRequest:
    return RepoTurnSemanticDeclarationRequest.model_validate(
        _load_fixture("vnext_plus239", name)
    )


def _v85a_guardrail(
    name: str = "repo_semantic_declaration_non_authority_guardrail_v239_reference.json",
) -> RepoSemanticDeclarationNonAuthorityGuardrail:
    return RepoSemanticDeclarationNonAuthorityGuardrail.model_validate(
        _load_fixture("vnext_plus239", name)
    )


def _request_payload_with_row(
    request_ref: str = "declaration-request:v85a:intent-to-declaration-office",
) -> tuple[dict[str, Any], dict[str, Any]]:
    payload = deepcopy(
        _load_fixture("vnext_plus239", "repo_turn_semantic_declaration_request_v239_reference.json")
    )
    for row in payload["declaration_request_rows"]:
        if row["declaration_request_ref"] == request_ref:
            return payload, row
    raise AssertionError(f"missing request row {request_ref}")


def _validate_reference_bundle_with(
    *,
    source_index: RepoSemanticDeclarationSourceIndex | None = None,
    request: RepoTurnSemanticDeclarationRequest | None = None,
    guardrail: RepoSemanticDeclarationNonAuthorityGuardrail | None = None,
) -> None:
    v84_readiness, v84_handoff, v84_closeout, derived_source, derived_request, derived_guardrail = (
        derive_v85a_semantic_declaration_review_bundle()
    )
    validate_v85a_semantic_declaration_review_bundle(
        v84_work_packet_activation_readiness_summary=v84_readiness,
        v84_post_work_packet_activation_review_handoff=v84_handoff,
        v84_work_packet_activation_family_closeout_alignment=v84_closeout,
        semantic_declaration_source_index=source_index or derived_source,
        turn_semantic_declaration_request=request or derived_request,
        semantic_declaration_non_authority_guardrail=guardrail or derived_guardrail,
    )


def test_v85a_reference_fixtures_match_derivation() -> None:
    *_, source_index, request, guardrail = derive_v85a_semantic_declaration_review_bundle()
    assert source_index.model_dump(mode="json") == _load_fixture(
        "vnext_plus239",
        "repo_semantic_declaration_source_index_v239_reference.json",
    )
    assert request.model_dump(mode="json") == _load_fixture(
        "vnext_plus239",
        "repo_turn_semantic_declaration_request_v239_reference.json",
    )
    assert guardrail.model_dump(mode="json") == _load_fixture(
        "vnext_plus239",
        "repo_semantic_declaration_non_authority_guardrail_v239_reference.json",
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name"),
    [
        (
            REPO_SEMANTIC_DECLARATION_SOURCE_INDEX_SCHEMA,
            "repo_semantic_declaration_source_index.v1.json",
            "repo_semantic_declaration_source_index_v239_reference.json",
        ),
        (
            REPO_TURN_SEMANTIC_DECLARATION_REQUEST_SCHEMA,
            "repo_turn_semantic_declaration_request.v1.json",
            "repo_turn_semantic_declaration_request_v239_reference.json",
        ),
        (
            REPO_SEMANTIC_DECLARATION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            "repo_semantic_declaration_non_authority_guardrail.v1.json",
            "repo_semantic_declaration_non_authority_guardrail_v239_reference.json",
        ),
    ],
)
def test_v85a_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
) -> None:
    payload = _load_fixture("vnext_plus239", fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)


def test_v85a_reference_bundle_links_released_v84c_substrate() -> None:
    _validate_reference_bundle_with(
        source_index=_v85a_source_index(),
        request=_v85a_request(),
        guardrail=_v85a_guardrail(),
    )


def test_v85a_reference_preserves_declaration_review_boundary() -> None:
    request = _v85a_request()
    eligible_rows = [
        row
        for row in request.declaration_request_rows
        if row.declaration_review_eligibility_posture
        == "eligible_for_semantic_declaration_review"
    ]
    assert len(eligible_rows) == 1
    eligible = eligible_rows[0]
    assert eligible.semantic_declaration_session_ref
    assert eligible.declaration_selection_status == "not_selected_by_v85a"
    assert eligible.canonical_lookup_status == "lookup_required_later"
    assert eligible.non_authority_posture == "no_declaration_authority_granted_by_v85"
    assert eligible.guardrail_refs == ["guardrail:v85a:intent-to-declaration-office"]
    assert {row.competency_kind for row in eligible.resident_model_competency_rows} == {
        "artifact_shape_obedience",
        "bounded_local_judgment",
        "declared_uncertainty_routing",
        "duplicate_preservation",
        "no_unauthorized_transition",
        "order_preservation",
        "pointer_obedience",
        "stop_at_schema_boundary",
        "unknown_pointer_abstention",
    }
    assert {
        row.witness_strength
        for row in eligible.semantic_act_witness_rows
        if row.witness_ref in eligible.source_witness_refs
    } == {"direct"}


@pytest.mark.parametrize(
    ("fixture_name", "message"),
    [
        (
            "repo_semantic_declaration_v239_reject_missing_pointer_competency.json",
            "resident model competencies missing: pointer_obedience",
        ),
    ],
)
def test_v85a_source_index_rejects_invalid_rows(fixture_name: str, message: str) -> None:
    with pytest.raises(ValidationError, match=message):
        RepoSemanticDeclarationSourceIndex.model_validate(
            _load_fixture("vnext_plus239", fixture_name)
        )


@pytest.mark.parametrize(
    ("fixture_name", "message"),
    [
        (
            "repo_semantic_declaration_v239_reject_generated_candidate_missing_witnesses.json",
            "List should have at least 1 item",
        ),
        (
            "repo_semantic_declaration_v239_reject_support_only_eligible.json",
            "support or absence-only declarations cannot be eligible",
        ),
        (
            "repo_semantic_declaration_v239_reject_ambiguous_selected.json",
            "ambiguous declarations cannot be eligible",
        ),
        (
            "repo_semantic_declaration_v239_reject_unknown_class_repaired.json",
            "registry gap acts must use unknown_class_registry_gap",
        ),
        (
            "repo_semantic_declaration_v239_reject_missing_guardrail_ref.json",
            "List should have at least 1 item",
        ),
    ],
)
def test_v85a_requests_reject_declaration_authority_leaks(
    fixture_name: str,
    message: str,
) -> None:
    with pytest.raises(ValidationError, match=message):
        RepoTurnSemanticDeclarationRequest.model_validate(
            _load_fixture("vnext_plus239", fixture_name)
        )


def test_v85a_bundle_rejects_opaque_pointer_as_natural_binding() -> None:
    request = RepoTurnSemanticDeclarationRequest.model_validate(
        _load_fixture(
            "vnext_plus239",
            "repo_semantic_declaration_v239_reject_opaque_pointer_truth.json",
        )
    )
    source_index = _v85a_source_index()
    guardrail = derive_v85a_repo_semantic_declaration_non_authority_guardrail(
        semantic_declaration_source_index=source_index,
        turn_semantic_declaration_request=request,
    )
    with pytest.raises(
        ValueError,
        match="opaque pointer competence cannot establish natural binding",
    ):
        _validate_reference_bundle_with(
            source_index=source_index,
            request=request,
            guardrail=guardrail,
        )


def test_v85a_authority_claim_scanner_allows_negated_suffixes() -> None:
    note = "Declaration authority granted is forbidden; no implementation occurs."
    assert _reject_v85_authority_claim(note, field_name="limitation_note") == note


def test_v85a_authority_claim_scanner_checks_all_matches() -> None:
    note = (
        "No implementation lock created by V85-A. "
        "This row says implementation lock created for execution."
    )
    with pytest.raises(ValueError, match="may not carry V85 declaration authority"):
        _reject_v85_authority_claim(note, field_name="limitation_note")


def test_v85a_request_source_refs_reject_absolute_paths() -> None:
    payload, row = _request_payload_with_row()
    row["source_refs"] = ["/tmp/not-repo-relative"]
    with pytest.raises(ValidationError, match="source_refs must be repo-relative"):
        RepoTurnSemanticDeclarationRequest.model_validate(payload)


def test_v85a_request_binding_basis_must_resolve_to_selected_witnesses() -> None:
    payload, row = _request_payload_with_row()
    row["binding_basis_refs"] = ["witness:v85a:support:canonical-loop"]
    with pytest.raises(ValueError, match="binding basis refs must be a subset"):
        RepoTurnSemanticDeclarationRequest.model_validate(payload)


def test_v85a_request_eligible_direct_witnesses_must_be_referenced() -> None:
    payload, row = _request_payload_with_row()
    row["binding_basis_refs"] = ["witness:v85a:support:canonical-loop"]
    row["source_witness_refs"] = ["witness:v85a:support:canonical-loop"]
    with pytest.raises(
        ValidationError,
        match="eligible semantic declaration requires direct/current witnesses",
    ):
        RepoTurnSemanticDeclarationRequest.model_validate(payload)


def test_v85a_declared_act_rejects_ambiguous_status_without_ambiguity() -> None:
    payload, row = _request_payload_with_row()
    row["declared_semantic_act_rows"][0]["declaration_candidate_status"] = (
        "ambiguous_candidate"
    )
    with pytest.raises(ValueError, match="ambiguous candidates must carry an ambiguous posture"):
        RepoTurnSemanticDeclarationRequest.model_validate(payload)


def test_v85a_request_status_must_match_declared_act_statuses() -> None:
    payload, row = _request_payload_with_row()
    row["declaration_candidate_status"] = "ambiguous_candidate"
    row["declaration_review_eligibility_posture"] = "blocked_by_ambiguous_binding"
    row["binding_posture"] = "ambiguous"
    row["binding_resolution_posture"] = "ambiguous_requires_review"
    with pytest.raises(ValueError, match="ambiguous request requires at least one ambiguous act"):
        RepoTurnSemanticDeclarationRequest.model_validate(payload)


def test_v85a_bundle_requires_core_identifier_consistency() -> None:
    guardrail = _v85a_guardrail().model_copy(update={"snapshot_id": "mismatched-snapshot"})
    with pytest.raises(
        ValueError,
        match="V85-A bundle components must share review, snapshot, and source set IDs",
    ):
        _validate_reference_bundle_with(
            source_index=_v85a_source_index(),
            request=_v85a_request(),
            guardrail=guardrail,
        )


@pytest.mark.parametrize(
    ("fixture_name", "message"),
    [
        (
            "repo_semantic_declaration_v239_reject_guardrail_missing_downstream_action.json",
            "guardrails must forbid required downstream actions",
        ),
        (
            "repo_semantic_declaration_v239_reject_guardrail_v86_selection_claim.json",
            "V85-A guardrails cannot select V86",
        ),
    ],
)
def test_v85a_guardrails_reject_missing_or_overreaching_prohibitions(
    fixture_name: str,
    message: str,
) -> None:
    with pytest.raises(ValidationError, match=message):
        RepoSemanticDeclarationNonAuthorityGuardrail.model_validate(
            _load_fixture("vnext_plus239", fixture_name)
        )
