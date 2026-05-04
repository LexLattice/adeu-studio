from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_POST_SEMANTIC_DECLARATION_REVIEW_HANDOFF_SCHEMA,
    REPO_SEMANTIC_DECLARATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_SEMANTIC_DECLARATION_REVIEW_SUMMARY_SCHEMA,
    RepoCanonicalMetaLookupIndex,
    RepoObligationFamilyRegistry,
    RepoPostSemanticDeclarationReviewHandoff,
    RepoSemanticDeclarationFamilyCloseoutAlignment,
    RepoSemanticDeclarationNonAuthorityGuardrail,
    RepoSemanticDeclarationReviewSummary,
    RepoSemanticDeclarationSourceIndex,
    RepoSemanticOperatorClassRegistry,
    RepoSemanticPointerLookupFixture,
    RepoTurnSemanticDeclarationRequest,
    derive_v85c_semantic_declaration_closeout_bundle,
    validate_v85c_semantic_declaration_closeout_bundle,
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


def _v85a_source_index() -> RepoSemanticDeclarationSourceIndex:
    return RepoSemanticDeclarationSourceIndex.model_validate(
        _load_fixture(
            "vnext_plus239",
            "repo_semantic_declaration_source_index_v239_reference.json",
        )
    )


def _v85a_request() -> RepoTurnSemanticDeclarationRequest:
    return RepoTurnSemanticDeclarationRequest.model_validate(
        _load_fixture(
            "vnext_plus239",
            "repo_turn_semantic_declaration_request_v239_reference.json",
        )
    )


def _v85a_guardrail() -> RepoSemanticDeclarationNonAuthorityGuardrail:
    return RepoSemanticDeclarationNonAuthorityGuardrail.model_validate(
        _load_fixture(
            "vnext_plus239",
            "repo_semantic_declaration_non_authority_guardrail_v239_reference.json",
        )
    )


def _v85b_lookup() -> RepoCanonicalMetaLookupIndex:
    return RepoCanonicalMetaLookupIndex.model_validate(
        _load_fixture("vnext_plus240", "repo_canonical_meta_lookup_index_v240_reference.json")
    )


def _v85b_registry() -> RepoSemanticOperatorClassRegistry:
    return RepoSemanticOperatorClassRegistry.model_validate(
        _load_fixture(
            "vnext_plus240",
            "repo_semantic_operator_class_registry_v240_reference.json",
        )
    )


def _v85b_obligations() -> RepoObligationFamilyRegistry:
    return RepoObligationFamilyRegistry.model_validate(
        _load_fixture("vnext_plus240", "repo_obligation_family_registry_v240_reference.json")
    )


def _v85b_fixture() -> RepoSemanticPointerLookupFixture:
    return RepoSemanticPointerLookupFixture.model_validate(
        _load_fixture("vnext_plus240", "repo_semantic_pointer_lookup_fixture_v240_reference.json")
    )


def _v85c_summary(
    name: str = "repo_semantic_declaration_review_summary_v241_reference.json",
) -> RepoSemanticDeclarationReviewSummary:
    return RepoSemanticDeclarationReviewSummary.model_validate(_load_fixture("vnext_plus241", name))


def _v85c_handoff(
    name: str = "repo_post_semantic_declaration_review_handoff_v241_reference.json",
) -> RepoPostSemanticDeclarationReviewHandoff:
    return RepoPostSemanticDeclarationReviewHandoff.model_validate(
        _load_fixture("vnext_plus241", name)
    )


def _v85c_closeout(
    name: str = "repo_semantic_declaration_family_closeout_alignment_v241_reference.json",
) -> RepoSemanticDeclarationFamilyCloseoutAlignment:
    return RepoSemanticDeclarationFamilyCloseoutAlignment.model_validate(
        _load_fixture("vnext_plus241", name)
    )


def _validate_reference_bundle_with(
    *,
    summary: RepoSemanticDeclarationReviewSummary | None = None,
    handoff: RepoPostSemanticDeclarationReviewHandoff | None = None,
    closeout: RepoSemanticDeclarationFamilyCloseoutAlignment | None = None,
) -> None:
    validate_v85c_semantic_declaration_closeout_bundle(
        semantic_declaration_source_index=_v85a_source_index(),
        turn_semantic_declaration_request=_v85a_request(),
        semantic_declaration_non_authority_guardrail=_v85a_guardrail(),
        canonical_meta_lookup_index=_v85b_lookup(),
        semantic_operator_class_registry=_v85b_registry(),
        obligation_family_registry=_v85b_obligations(),
        semantic_pointer_lookup_fixture=_v85b_fixture(),
        semantic_declaration_review_summary=summary or _v85c_summary(),
        post_semantic_declaration_review_handoff=handoff or _v85c_handoff(),
        semantic_declaration_family_closeout_alignment=closeout or _v85c_closeout(),
    )


def test_v85c_reference_fixtures_match_derivation() -> None:
    *_, summary, handoff, closeout = derive_v85c_semantic_declaration_closeout_bundle()
    assert summary.model_dump(mode="json") == _load_fixture(
        "vnext_plus241",
        "repo_semantic_declaration_review_summary_v241_reference.json",
    )
    assert handoff.model_dump(mode="json") == _load_fixture(
        "vnext_plus241",
        "repo_post_semantic_declaration_review_handoff_v241_reference.json",
    )
    assert closeout.model_dump(mode="json") == _load_fixture(
        "vnext_plus241",
        "repo_semantic_declaration_family_closeout_alignment_v241_reference.json",
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name"),
    [
        (
            REPO_SEMANTIC_DECLARATION_REVIEW_SUMMARY_SCHEMA,
            "repo_semantic_declaration_review_summary.v1.json",
            "repo_semantic_declaration_review_summary_v241_reference.json",
        ),
        (
            REPO_POST_SEMANTIC_DECLARATION_REVIEW_HANDOFF_SCHEMA,
            "repo_post_semantic_declaration_review_handoff.v1.json",
            "repo_post_semantic_declaration_review_handoff_v241_reference.json",
        ),
        (
            REPO_SEMANTIC_DECLARATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            "repo_semantic_declaration_family_closeout_alignment.v1.json",
            "repo_semantic_declaration_family_closeout_alignment_v241_reference.json",
        ),
    ],
)
def test_v85c_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
) -> None:
    payload = _load_fixture("vnext_plus241", fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)


def test_v85c_reference_bundle_links_released_v85a_and_v85b_substrate() -> None:
    _validate_reference_bundle_with()


def test_v85c_reference_preserves_review_only_handoff_boundary() -> None:
    summary = _v85c_summary()
    ready = next(
        row
        for row in summary.summary_rows
        if row.summary_ref == "summary:v85c:ready-obligation-expansion-review"
    )
    assert ready.summary_posture == "ready_for_later_obligation_expansion_review"
    assert ready.obligation_expansion_posture == "no_obligation_expansion_performed_by_v85"
    assert ready.future_family_selection_posture == "no_future_family_selected_by_v85"

    handoff = _v85c_handoff().handoff_rows[0]
    assert handoff.handoff_target == "future_obligation_expansion_review"
    assert handoff.handoff_sequence_posture == "immediate_next_pressure"
    assert handoff.obligation_expansion_status == "no_obligation_expansion_performed_by_v85"
    assert handoff.future_family_selection_status == "no_future_family_selected_by_v85"


@pytest.mark.parametrize(
    ("model", "fixture_name", "message"),
    [
        (
            RepoSemanticDeclarationReviewSummary,
            "repo_semantic_declaration_closeout_v241_reject_ready_missing_lookup.json",
            "ready summary requires lookup refs",
        ),
        (
            RepoSemanticDeclarationReviewSummary,
            "repo_semantic_declaration_closeout_v241_reject_warning_hides_blocker.json",
            "blocking declaration issues cannot be warning-only",
        ),
        (
            RepoPostSemanticDeclarationReviewHandoff,
            "repo_semantic_declaration_closeout_v241_reject_downstream_skip.json",
            "downstream handoffs cannot skip obligation expansion review",
        ),
        (
            RepoPostSemanticDeclarationReviewHandoff,
            "repo_semantic_declaration_closeout_v241_reject_handoff_expands_obligation.json",
            "V85-C handoffs cannot expand obligations",
        ),
        (
            RepoSemanticDeclarationFamilyCloseoutAlignment,
            "repo_semantic_declaration_closeout_v241_reject_closeout_selects_v86.json",
            "V85 closeout cannot select V86",
        ),
    ],
)
def test_v85c_surfaces_reject_authority_leaks(
    model: type,
    fixture_name: str,
    message: str,
) -> None:
    with pytest.raises(ValidationError, match=message):
        model.model_validate(_load_fixture("vnext_plus241", fixture_name))


def test_v85c_bundle_rejects_mixed_candidate_lineage() -> None:
    summary = _v85c_summary()
    summary_rows = list(summary.summary_rows)
    summary_rows[0] = summary_rows[0].model_copy(update={"candidate_ref": "candidate:v85:other"})
    summary = summary.model_copy(update={"summary_rows": summary_rows})
    handoff_payload = deepcopy(
        _load_fixture(
            "vnext_plus241",
            "repo_post_semantic_declaration_review_handoff_v241_reference.json",
        )
    )
    handoff_payload["semantic_declaration_review_summary_id"] = (
        summary.semantic_declaration_review_summary_id
    )
    handoff = RepoPostSemanticDeclarationReviewHandoff.model_validate(handoff_payload)
    closeout_payload = deepcopy(
        _load_fixture(
            "vnext_plus241",
            "repo_semantic_declaration_family_closeout_alignment_v241_reference.json",
        )
    )
    closeout_payload["semantic_declaration_review_summary_id"] = (
        summary.semantic_declaration_review_summary_id
    )
    closeout_payload["post_semantic_declaration_review_handoff_id"] = (
        handoff.post_semantic_declaration_review_handoff_id
    )
    closeout = RepoSemanticDeclarationFamilyCloseoutAlignment.model_validate(closeout_payload)
    with pytest.raises(ValueError, match="summary rows must preserve candidate lineage"):
        _validate_reference_bundle_with(summary=summary, handoff=handoff, closeout=closeout)


def test_v85c_bundle_rejects_unknown_summary_source_index_ref() -> None:
    summary = _v85c_summary()
    summary_rows = list(summary.summary_rows)
    summary_rows[0] = summary_rows[0].model_copy(
        update={"source_index_refs": ["source-index:v85a:missing"]}
    )
    summary = summary.model_copy(update={"summary_rows": summary_rows})

    with pytest.raises(
        ValueError,
        match="summary source index refs must resolve to released V85-A source index",
    ):
        _validate_reference_bundle_with(summary=summary)


def test_v85c_bundle_rejects_unknown_handoff_selected_declaration_ref() -> None:
    handoff = _v85c_handoff()
    handoff_rows = list(handoff.handoff_rows)
    handoff_rows[0] = handoff_rows[0].model_copy(
        update={"selected_declaration_refs": ["semantic-act:v85a:missing"]}
    )
    handoff = handoff.model_copy(update={"handoff_rows": handoff_rows})

    with pytest.raises(
        ValueError,
        match="handoff declaration refs must resolve to released V85-A acts",
    ):
        _validate_reference_bundle_with(handoff=handoff)


def test_v85c_bundle_rejects_handoff_selected_declaration_not_in_summary() -> None:
    handoff = _v85c_handoff()
    handoff_rows = list(handoff.handoff_rows)
    handoff_rows[0] = handoff_rows[0].model_copy(
        update={"selected_declaration_refs": ["semantic-act:v85a:ambiguous-natural-binding"]}
    )
    handoff = handoff.model_copy(update={"handoff_rows": handoff_rows})

    with pytest.raises(
        ValueError,
        match="handoff declaration refs must match referenced summaries",
    ):
        _validate_reference_bundle_with(handoff=handoff)
