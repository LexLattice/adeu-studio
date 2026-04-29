from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_MODEL_OUTPUT_COMPARISON_PROJECTION_SCHEMA,
    REPO_OPERATOR_PROJECTION_CASE_VIEW_SCHEMA,
    REPO_OPERATOR_PROJECTION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
    REPO_OPERATOR_PROJECTION_SOURCE_INDEX_SCHEMA,
    REPO_PROJECTION_EXCEPTION_VISIBILITY_REGISTER_SCHEMA,
    REPO_TYPED_ADJUDICATION_CASE_VIEW_SCHEMA,
    RepoModelOutputComparisonProjection,
    RepoOperatorProjectionCaseView,
    RepoOperatorProjectionNonAuthorityGuardrail,
    RepoOperatorProjectionSourceIndex,
    RepoProjectionExceptionVisibilityRegister,
    RepoTypedAdjudicationCaseView,
    derive_v74b_operator_projection_bundle,
    validate_v74b_operator_projection_bundle,
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


def _v74b_typed_case_view() -> RepoTypedAdjudicationCaseView:
    return RepoTypedAdjudicationCaseView.model_validate(
        _load_fixture(
            "vnext_plus207",
            "repo_typed_adjudication_case_view_v207_reference.json",
        )
    )


def _v74b_comparison_projection() -> RepoModelOutputComparisonProjection:
    return RepoModelOutputComparisonProjection.model_validate(
        _load_fixture(
            "vnext_plus207",
            "repo_model_output_comparison_projection_v207_reference.json",
        )
    )


def _v74b_exception_register() -> RepoProjectionExceptionVisibilityRegister:
    return RepoProjectionExceptionVisibilityRegister.model_validate(
        _load_fixture(
            "vnext_plus207",
            "repo_projection_exception_visibility_register_v207_reference.json",
        )
    )


def _validate_reference_bundle_with(
    *,
    typed_case_view: RepoTypedAdjudicationCaseView | None = None,
    comparison_projection: RepoModelOutputComparisonProjection | None = None,
    exception_register: RepoProjectionExceptionVisibilityRegister | None = None,
) -> None:
    validate_v74b_operator_projection_bundle(
        operator_projection_source_index=_v74a_source_index(),
        operator_projection_case_view=_v74a_case_view(),
        operator_projection_non_authority_guardrail=_v74a_guardrail(),
        typed_adjudication_case_view=typed_case_view or _v74b_typed_case_view(),
        model_output_comparison_projection=comparison_projection or _v74b_comparison_projection(),
        projection_exception_visibility_register=exception_register or _v74b_exception_register(),
    )


def test_v207_reference_bundle_validates() -> None:
    source_index = _v74a_source_index()
    case_view = _v74a_case_view()
    guardrail = _v74a_guardrail()
    typed_case_view = _v74b_typed_case_view()
    comparison_projection = _v74b_comparison_projection()
    exception_register = _v74b_exception_register()

    assert source_index.schema == REPO_OPERATOR_PROJECTION_SOURCE_INDEX_SCHEMA
    assert case_view.schema == REPO_OPERATOR_PROJECTION_CASE_VIEW_SCHEMA
    assert guardrail.schema == REPO_OPERATOR_PROJECTION_NON_AUTHORITY_GUARDRAIL_SCHEMA
    assert typed_case_view.schema == REPO_TYPED_ADJUDICATION_CASE_VIEW_SCHEMA
    assert comparison_projection.schema == REPO_MODEL_OUTPUT_COMPARISON_PROJECTION_SCHEMA
    assert exception_register.schema == REPO_PROJECTION_EXCEPTION_VISIBILITY_REGISTER_SCHEMA
    assert {row.typed_case_posture for row in typed_case_view.typed_case_rows} == {
        "blocked_by_unresolved_exception",
        "projection_ready",
    }
    assert {row.exception_kind for row in exception_register.exception_rows} == {
        "comparison_axis_unchecked",
        "product_authority_missing",
    }

    validate_v74b_operator_projection_bundle(
        operator_projection_source_index=source_index,
        operator_projection_case_view=case_view,
        operator_projection_non_authority_guardrail=guardrail,
        typed_adjudication_case_view=typed_case_view,
        model_output_comparison_projection=comparison_projection,
        projection_exception_visibility_register=exception_register,
    )


def test_v207_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_typed_adjudication_case_view.v1.json").validate(
        _load_fixture(
            "vnext_plus207",
            "repo_typed_adjudication_case_view_v207_reference.json",
        )
    )
    _schema_validator("repo_model_output_comparison_projection.v1.json").validate(
        _load_fixture(
            "vnext_plus207",
            "repo_model_output_comparison_projection_v207_reference.json",
        )
    )
    _schema_validator("repo_projection_exception_visibility_register.v1.json").validate(
        _load_fixture(
            "vnext_plus207",
            "repo_projection_exception_visibility_register_v207_reference.json",
        )
    )


def test_v207_derivation_helper_matches_reference_fixtures() -> None:
    *_, typed_case_view, comparison_projection, exception_register = (
        derive_v74b_operator_projection_bundle(repo_root=_repo_root())
    )

    assert typed_case_view.model_dump(mode="json") == _load_fixture(
        "vnext_plus207",
        "repo_typed_adjudication_case_view_v207_reference.json",
    )
    assert comparison_projection.model_dump(mode="json") == _load_fixture(
        "vnext_plus207",
        "repo_model_output_comparison_projection_v207_reference.json",
    )
    assert exception_register.model_dump(mode="json") == _load_fixture(
        "vnext_plus207",
        "repo_projection_exception_visibility_register_v207_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_operator_projection_v207_reject_typed_case_without_source_case_refs.json",
            RepoTypedAdjudicationCaseView,
            "at least 1 item",
        ),
        (
            "repo_operator_projection_v207_reject_conceptual_diff_support_as_released_schema.json",
            RepoTypedAdjudicationCaseView,
            "conceptual-diff schema support",
        ),
        (
            "repo_operator_projection_v207_reject_comparison_without_prompt_source_refs.json",
            RepoModelOutputComparisonProjection,
            "at least 1 item",
        ),
        (
            "repo_operator_projection_v207_reject_comparison_without_model_output_provenance_rows.json",
            RepoModelOutputComparisonProjection,
            "at least 1 item",
        ),
        (
            "repo_operator_projection_v207_reject_comparison_global_model_ranking.json",
            RepoModelOutputComparisonProjection,
            "may not carry projection authority",
        ),
        (
            "repo_operator_projection_v207_reject_axis_without_source_evidence.json",
            RepoModelOutputComparisonProjection,
            "at least 1 item",
        ),
        (
            "repo_operator_projection_v207_reject_axis_without_bounded_guardrail.json",
            RepoModelOutputComparisonProjection,
            "must state bounded",
        ),
        (
            "repo_operator_projection_v207_reject_product_authorization.json",
            RepoTypedAdjudicationCaseView,
            "may not carry projection authority",
        ),
        (
            "repo_operator_projection_v207_reject_exception_resolved.json",
            RepoProjectionExceptionVisibilityRegister,
            "may not carry typed projection authority",
        ),
        (
            "repo_operator_projection_v207_reject_typed_case_new_ratification.json",
            RepoTypedAdjudicationCaseView,
            "may not carry typed projection authority",
        ),
        (
            "repo_operator_projection_v207_reject_comparison_authorizes_dispatch.json",
            RepoModelOutputComparisonProjection,
            "may not carry projection authority",
        ),
    ],
)
def test_v207_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoTypedAdjudicationCaseView
        | RepoModelOutputComparisonProjection
        | RepoProjectionExceptionVisibilityRegister
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus207", fixture_name))


def test_v207_bundle_rejects_omitted_known_v74a_blocker() -> None:
    exception_register = RepoProjectionExceptionVisibilityRegister.model_validate(
        _load_fixture(
            "vnext_plus207",
            "repo_operator_projection_v207_reject_exception_omits_known_blocker.json",
        )
    )

    with pytest.raises(ValueError, match="typed case exception refs must be visible"):
        _validate_reference_bundle_with(exception_register=exception_register)
