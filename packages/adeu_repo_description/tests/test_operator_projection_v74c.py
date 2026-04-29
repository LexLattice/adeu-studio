from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_DECISION_VISIBILITY_CONTRACT_SCHEMA,
    REPO_OPERATOR_PROJECTION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_POST_PROJECTION_HANDOFF_SCHEMA,
    REPO_RATIFICATION_REVIEW_WORKBENCH_PROJECTION_SCHEMA,
    RepoDecisionVisibilityContract,
    RepoOperatorProjectionCaseView,
    RepoOperatorProjectionFamilyCloseoutAlignment,
    RepoOperatorProjectionSourceIndex,
    RepoPostProjectionHandoff,
    RepoProjectionExceptionVisibilityRegister,
    RepoRatificationReviewWorkbenchProjection,
    RepoTypedAdjudicationCaseView,
    derive_v74c_operator_projection_bundle,
    validate_v74c_operator_projection_bundle,
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


def _v74b_typed_case_view() -> RepoTypedAdjudicationCaseView:
    return RepoTypedAdjudicationCaseView.model_validate(
        _load_fixture(
            "vnext_plus207",
            "repo_typed_adjudication_case_view_v207_reference.json",
        )
    )


def _v74b_exception_register() -> RepoProjectionExceptionVisibilityRegister:
    return RepoProjectionExceptionVisibilityRegister.model_validate(
        _load_fixture(
            "vnext_plus207",
            "repo_projection_exception_visibility_register_v207_reference.json",
        )
    )


def _v74c_decision_contract() -> RepoDecisionVisibilityContract:
    return RepoDecisionVisibilityContract.model_validate(
        _load_fixture(
            "vnext_plus208",
            "repo_decision_visibility_contract_v208_reference.json",
        )
    )


def _v74c_workbench_projection() -> RepoRatificationReviewWorkbenchProjection:
    return RepoRatificationReviewWorkbenchProjection.model_validate(
        _load_fixture(
            "vnext_plus208",
            "repo_ratification_review_workbench_projection_v208_reference.json",
        )
    )


def _v74c_handoff() -> RepoPostProjectionHandoff:
    return RepoPostProjectionHandoff.model_validate(
        _load_fixture(
            "vnext_plus208",
            "repo_post_projection_handoff_v208_reference.json",
        )
    )


def _v74c_family_closeout() -> RepoOperatorProjectionFamilyCloseoutAlignment:
    return RepoOperatorProjectionFamilyCloseoutAlignment.model_validate(
        _load_fixture(
            "vnext_plus208",
            "repo_operator_projection_family_closeout_alignment_v208_reference.json",
        )
    )


def _validate_reference_bundle_with(
    *,
    decision_contract: RepoDecisionVisibilityContract | None = None,
    workbench_projection: RepoRatificationReviewWorkbenchProjection | None = None,
    handoff: RepoPostProjectionHandoff | None = None,
    family_closeout: RepoOperatorProjectionFamilyCloseoutAlignment | None = None,
) -> None:
    validate_v74c_operator_projection_bundle(
        operator_projection_source_index=_v74a_source_index(),
        operator_projection_case_view=_v74a_case_view(),
        typed_adjudication_case_view=_v74b_typed_case_view(),
        projection_exception_visibility_register=_v74b_exception_register(),
        decision_visibility_contract=decision_contract or _v74c_decision_contract(),
        ratification_review_workbench_projection=(
            workbench_projection or _v74c_workbench_projection()
        ),
        post_projection_handoff=handoff or _v74c_handoff(),
        operator_projection_family_closeout_alignment=family_closeout
        or _v74c_family_closeout(),
    )


def test_v208_reference_bundle_validates() -> None:
    decision_contract = _v74c_decision_contract()
    workbench_projection = _v74c_workbench_projection()
    handoff = _v74c_handoff()
    family_closeout = _v74c_family_closeout()

    assert decision_contract.schema == REPO_DECISION_VISIBILITY_CONTRACT_SCHEMA
    assert (
        workbench_projection.schema == REPO_RATIFICATION_REVIEW_WORKBENCH_PROJECTION_SCHEMA
    )
    assert handoff.schema == REPO_POST_PROJECTION_HANDOFF_SCHEMA
    assert family_closeout.schema == REPO_OPERATOR_PROJECTION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
    assert {row.contract_posture for row in decision_contract.visibility_contract_rows} == {
        "blocked_by_authority_boundary",
        "visibility_contract_ready",
    }
    assert {row.handoff_target for row in handoff.handoff_rows} == {
        "future_product_review",
        "v75_dispatch_review",
    }

    _validate_reference_bundle_with(
        decision_contract=decision_contract,
        workbench_projection=workbench_projection,
        handoff=handoff,
        family_closeout=family_closeout,
    )


def test_v208_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_decision_visibility_contract.v1.json").validate(
        _load_fixture(
            "vnext_plus208",
            "repo_decision_visibility_contract_v208_reference.json",
        )
    )
    _schema_validator("repo_ratification_review_workbench_projection.v1.json").validate(
        _load_fixture(
            "vnext_plus208",
            "repo_ratification_review_workbench_projection_v208_reference.json",
        )
    )
    _schema_validator("repo_post_projection_handoff.v1.json").validate(
        _load_fixture(
            "vnext_plus208",
            "repo_post_projection_handoff_v208_reference.json",
        )
    )
    _schema_validator("repo_operator_projection_family_closeout_alignment.v1.json").validate(
        _load_fixture(
            "vnext_plus208",
            "repo_operator_projection_family_closeout_alignment_v208_reference.json",
        )
    )


def test_v208_derivation_helper_matches_reference_fixtures() -> None:
    *_, decision_contract, workbench_projection, handoff, family_closeout = (
        derive_v74c_operator_projection_bundle(repo_root=_repo_root())
    )

    assert decision_contract.model_dump(mode="json") == _load_fixture(
        "vnext_plus208",
        "repo_decision_visibility_contract_v208_reference.json",
    )
    assert workbench_projection.model_dump(mode="json") == _load_fixture(
        "vnext_plus208",
        "repo_ratification_review_workbench_projection_v208_reference.json",
    )
    assert handoff.model_dump(mode="json") == _load_fixture(
        "vnext_plus208",
        "repo_post_projection_handoff_v208_reference.json",
    )
    assert family_closeout.model_dump(mode="json") == _load_fixture(
        "vnext_plus208",
        "repo_operator_projection_family_closeout_alignment_v208_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_operator_projection_v208_reject_visibility_contract_without_case_refs.json",
            RepoDecisionVisibilityContract,
            "at least 1 item",
        ),
        (
            "repo_operator_projection_v208_reject_hidden_authority_boundary.json",
            RepoDecisionVisibilityContract,
            "visibility obligations",
        ),
        (
            "repo_operator_projection_v208_reject_mixed_visibility_authority_list.json",
            RepoDecisionVisibilityContract,
            "Input should be",
        ),
        (
            "repo_operator_projection_v208_reject_free_floating_later_authority.json",
            RepoDecisionVisibilityContract,
            "required later authority",
        ),
        (
            "repo_operator_projection_v208_reject_workbench_without_visibility_contract.json",
            RepoRatificationReviewWorkbenchProjection,
            "at least 1 item",
        ),
        (
            "repo_operator_projection_v208_reject_workbench_permits_ratification.json",
            RepoRatificationReviewWorkbenchProjection,
            "Input should be",
        ),
        (
            "repo_operator_projection_v208_reject_handoff_performs_dispatch.json",
            RepoPostProjectionHandoff,
            "workbench or handoff authority",
        ),
        (
            "repo_operator_projection_v208_reject_v75_handoff_without_dispatch_authority.json",
            RepoPostProjectionHandoff,
            "V75 handoff rows require dispatch authority",
        ),
        (
            "repo_operator_projection_v208_reject_product_selected.json",
            RepoDecisionVisibilityContract,
            "workbench or handoff authority",
        ),
        (
            "repo_operator_projection_v208_reject_family_closeout_downstream_authority.json",
            RepoOperatorProjectionFamilyCloseoutAlignment,
            "may not carry projection authority",
        ),
    ],
)
def test_v208_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoDecisionVisibilityContract
        | RepoRatificationReviewWorkbenchProjection
        | RepoPostProjectionHandoff
        | RepoOperatorProjectionFamilyCloseoutAlignment
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus208", fixture_name))


def test_v208_bundle_rejects_ready_handoff_with_blocking_exception() -> None:
    exception_register = _v74b_exception_register()
    exception_rows = [
        row.model_copy(update={"blocking_posture": "blocking"})
        if row.exception_ref == "exception:v74b:comparison-axis:operator-legibility-unchecked"
        else row
        for row in exception_register.exception_rows
    ]
    exception_register = exception_register.model_copy(update={"exception_rows": exception_rows})

    with pytest.raises(ValueError, match="blocking carried exceptions cannot be ready"):
        validate_v74c_operator_projection_bundle(
            operator_projection_source_index=_v74a_source_index(),
            operator_projection_case_view=_v74a_case_view(),
            typed_adjudication_case_view=_v74b_typed_case_view(),
            projection_exception_visibility_register=exception_register,
            decision_visibility_contract=_v74c_decision_contract(),
            ratification_review_workbench_projection=_v74c_workbench_projection(),
            post_projection_handoff=_v74c_handoff(),
            operator_projection_family_closeout_alignment=_v74c_family_closeout(),
        )


def test_v208_bundle_rejects_unknown_visibility_contract_source_refs() -> None:
    decision_contract = _v74c_decision_contract()
    rows = list(decision_contract.visibility_contract_rows)
    first_row = rows[0].model_copy(
        update={
            "visible_source_refs": sorted(
                [
                    *rows[0].visible_source_refs,
                    "docs/support/arc_series_mapping/UNKNOWN_SOURCE.json",
                ]
            )
        }
    )
    decision_contract = decision_contract.model_copy(
        update={"visibility_contract_rows": [first_row, *rows[1:]]}
    )

    with pytest.raises(ValueError, match="visibility contract source refs must be known"):
        _validate_reference_bundle_with(decision_contract=decision_contract)
