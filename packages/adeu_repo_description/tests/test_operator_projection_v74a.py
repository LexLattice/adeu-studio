from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_OPERATOR_PROJECTION_CASE_VIEW_SCHEMA,
    REPO_OPERATOR_PROJECTION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
    REPO_OPERATOR_PROJECTION_SOURCE_INDEX_SCHEMA,
    RepoOperatorCognitionOutcomeSignal,
    RepoOperatorProjectionCaseView,
    RepoOperatorProjectionNonAuthorityGuardrail,
    RepoOperatorProjectionSourceIndex,
    RepoOutcomePromotionDemotionRecommendation,
    RepoOutcomeReviewFamilyCloseoutAlignment,
    RepoSelfImprovementOutcomeLedger,
    derive_v74a_operator_projection_bundle,
    derive_v74a_repo_operator_projection_non_authority_guardrail,
    validate_v74a_operator_projection_bundle,
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


def _v73c_ledger() -> RepoSelfImprovementOutcomeLedger:
    return RepoSelfImprovementOutcomeLedger.model_validate(
        _load_fixture("vnext_plus205", "repo_self_improvement_outcome_ledger_v205_reference.json")
    )


def _v73c_operator_signal() -> RepoOperatorCognitionOutcomeSignal:
    return RepoOperatorCognitionOutcomeSignal.model_validate(
        _load_fixture(
            "vnext_plus205",
            "repo_operator_cognition_outcome_signal_v205_reference.json",
        )
    )


def _v73c_recommendation() -> RepoOutcomePromotionDemotionRecommendation:
    return RepoOutcomePromotionDemotionRecommendation.model_validate(
        _load_fixture(
            "vnext_plus205",
            "repo_outcome_promotion_demotion_recommendation_v205_reference.json",
        )
    )


def _v73c_family_closeout() -> RepoOutcomeReviewFamilyCloseoutAlignment:
    return RepoOutcomeReviewFamilyCloseoutAlignment.model_validate(
        _load_fixture(
            "vnext_plus205",
            "repo_outcome_review_family_closeout_alignment_v205_reference.json",
        )
    )


def _v74a_source_index() -> RepoOperatorProjectionSourceIndex:
    return RepoOperatorProjectionSourceIndex.model_validate(
        _load_fixture(
            "vnext_plus206",
            "repo_operator_projection_source_index_v206_reference.json",
        )
    )


def _v74a_case_view() -> RepoOperatorProjectionCaseView:
    return RepoOperatorProjectionCaseView.model_validate(
        _load_fixture(
            "vnext_plus206",
            "repo_operator_projection_case_view_v206_reference.json",
        )
    )


def _v74a_guardrail() -> RepoOperatorProjectionNonAuthorityGuardrail:
    return RepoOperatorProjectionNonAuthorityGuardrail.model_validate(
        _load_fixture(
            "vnext_plus206",
            "repo_operator_projection_non_authority_guardrail_v206_reference.json",
        )
    )


def _validate_reference_bundle_with(
    *,
    source_index: RepoOperatorProjectionSourceIndex | None = None,
    case_view: RepoOperatorProjectionCaseView | None = None,
    guardrail: RepoOperatorProjectionNonAuthorityGuardrail | None = None,
) -> None:
    validate_v74a_operator_projection_bundle(
        self_improvement_outcome_ledger=_v73c_ledger(),
        operator_cognition_outcome_signal=_v73c_operator_signal(),
        outcome_promotion_demotion_recommendation=_v73c_recommendation(),
        outcome_review_family_closeout_alignment=_v73c_family_closeout(),
        operator_projection_source_index=source_index or _v74a_source_index(),
        operator_projection_case_view=case_view or _v74a_case_view(),
        operator_projection_non_authority_guardrail=guardrail or _v74a_guardrail(),
    )


def test_v206_reference_bundle_validates() -> None:
    source_index = _v74a_source_index()
    case_view = _v74a_case_view()
    guardrail = _v74a_guardrail()

    assert source_index.schema == REPO_OPERATOR_PROJECTION_SOURCE_INDEX_SCHEMA
    assert case_view.schema == REPO_OPERATOR_PROJECTION_CASE_VIEW_SCHEMA
    assert guardrail.schema == REPO_OPERATOR_PROJECTION_NON_AUTHORITY_GUARDRAIL_SCHEMA
    assert {row.projection_case_kind for row in case_view.case_view_rows} == {
        "product_pressure_case",
        "self_improvement_outcome_case",
    }
    assert {row.visible_authority_state for row in case_view.case_view_rows} == {
        "product_authority_missing",
        "ratification_required",
    }
    assert {
        row.required_later_authority for row in guardrail.guardrail_rows
    } == {"human_ratification_required", "product_authority_required"}

    _validate_reference_bundle_with(
        source_index=source_index,
        case_view=case_view,
        guardrail=guardrail,
    )


def test_v206_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_operator_projection_source_index.v1.json").validate(
        _load_fixture(
            "vnext_plus206",
            "repo_operator_projection_source_index_v206_reference.json",
        )
    )
    _schema_validator("repo_operator_projection_case_view.v1.json").validate(
        _load_fixture(
            "vnext_plus206",
            "repo_operator_projection_case_view_v206_reference.json",
        )
    )
    _schema_validator("repo_operator_projection_non_authority_guardrail.v1.json").validate(
        _load_fixture(
            "vnext_plus206",
            "repo_operator_projection_non_authority_guardrail_v206_reference.json",
        )
    )


def test_v206_derivation_helper_matches_reference_fixtures() -> None:
    *_, source_index, case_view, guardrail = derive_v74a_operator_projection_bundle(
        repo_root=_repo_root()
    )

    assert source_index.model_dump(mode="json") == _load_fixture(
        "vnext_plus206",
        "repo_operator_projection_source_index_v206_reference.json",
    )
    assert case_view.model_dump(mode="json") == _load_fixture(
        "vnext_plus206",
        "repo_operator_projection_case_view_v206_reference.json",
    )
    assert guardrail.model_dump(mode="json") == _load_fixture(
        "vnext_plus206",
        "repo_operator_projection_non_authority_guardrail_v206_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_operator_projection_v206_reject_missing_source_without_absence_posture.json",
            RepoOperatorProjectionSourceIndex,
            "integrated projection source rows must be present",
        ),
        (
            "repo_operator_projection_v206_reject_case_without_source_refs.json",
            RepoOperatorProjectionCaseView,
            "at least 1 item",
        ),
        (
            "repo_operator_projection_v206_reject_product_without_authority_missing.json",
            RepoOperatorProjectionCaseView,
            "product-pressure cases require missing product authority",
        ),
        (
            "repo_operator_projection_v206_reject_product_authorized.json",
            RepoOperatorProjectionCaseView,
            "may not carry projection authority",
        ),
        (
            "repo_operator_projection_v206_reject_model_comparison_benchmark_truth.json",
            RepoOperatorProjectionCaseView,
            "may not carry projection authority",
        ),
        (
            "repo_operator_projection_v206_reject_hidden_blocker_omitted.json",
            RepoOperatorProjectionCaseView,
            "future-family product-pressure cases require visible blockers",
        ),
        (
            "repo_operator_projection_v206_reject_empty_guardrail_forbidden_authorities.json",
            RepoOperatorProjectionNonAuthorityGuardrail,
            "at least 1 item",
        ),
        (
            "repo_operator_projection_v206_reject_operator_action_dispatch.json",
            RepoOperatorProjectionNonAuthorityGuardrail,
            "Input should be",
        ),
    ],
)
def test_v206_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoOperatorProjectionSourceIndex
        | RepoOperatorProjectionCaseView
        | RepoOperatorProjectionNonAuthorityGuardrail
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus206", fixture_name))


def test_v206_bundle_rejects_product_case_without_product_guardrail() -> None:
    guardrail_payload = _v74a_guardrail().model_dump(mode="json")
    guardrail_payload["guardrail_rows"][0]["required_later_authority"] = (
        "human_ratification_required"
    )
    guardrail_payload["operator_projection_non_authority_guardrail_id"] = _surface_id(
        "repo_operator_projection_non_authority_guardrail",
        REPO_OPERATOR_PROJECTION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
        guardrail_payload,
        "operator_projection_non_authority_guardrail_id",
    )
    guardrail = RepoOperatorProjectionNonAuthorityGuardrail.model_validate(guardrail_payload)

    with pytest.raises(ValueError, match="product-pressure cases require product authority"):
        _validate_reference_bundle_with(guardrail=guardrail)


def test_v206_bundle_rejects_case_source_not_in_source_index() -> None:
    case_payload = _v74a_case_view().model_dump(mode="json")
    case_payload["case_view_rows"][0]["source_refs"] = sorted(
        [*case_payload["case_view_rows"][0]["source_refs"], "docs/not-a-known-source.md"]
    )
    case_payload["operator_projection_case_view_id"] = _surface_id(
        "repo_operator_projection_case_view",
        REPO_OPERATOR_PROJECTION_CASE_VIEW_SCHEMA,
        case_payload,
        "operator_projection_case_view_id",
    )
    case_view = RepoOperatorProjectionCaseView.model_validate(case_payload)
    guardrail = derive_v74a_repo_operator_projection_non_authority_guardrail(
        repo_root=_repo_root(),
        operator_projection_case_view=case_view,
    )

    with pytest.raises(ValueError, match="case view source refs must be known"):
        _validate_reference_bundle_with(case_view=case_view, guardrail=guardrail)
