from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_EXTERNAL_BRANCH_READINESS_SUMMARY_SCHEMA,
    REPO_EXTERNAL_BRANCH_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_POST_EXTERNAL_BRANCH_REVIEW_HANDOFF_SCHEMA,
    RepoExternalBranchExceptionRegister,
    RepoExternalBranchNonActivationGuardrail,
    RepoExternalBranchReadinessSummary,
    RepoExternalBranchReviewFamilyCloseoutAlignment,
    RepoExternalBranchReviewRequest,
    RepoExternalBranchSourceIndex,
    RepoExternalDataBoundary,
    RepoExternalResultProvenanceContract,
    RepoExternalSubmissionAuthorityReview,
    RepoExternalToolBoundary,
    RepoPostExternalBranchReviewHandoff,
    derive_v80c_external_branch_review_closeout_bundle,
    validate_v80c_external_branch_review_closeout_bundle,
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


def _v80a_source_index() -> RepoExternalBranchSourceIndex:
    return RepoExternalBranchSourceIndex.model_validate(
        _load_fixture("vnext_plus224", "repo_external_branch_source_index_v224_reference.json")
    )


def _v80a_request() -> RepoExternalBranchReviewRequest:
    return RepoExternalBranchReviewRequest.model_validate(
        _load_fixture("vnext_plus224", "repo_external_branch_review_request_v224_reference.json")
    )


def _v80a_guardrail() -> RepoExternalBranchNonActivationGuardrail:
    return RepoExternalBranchNonActivationGuardrail.model_validate(
        _load_fixture(
            "vnext_plus224",
            "repo_external_branch_non_activation_guardrail_v224_reference.json",
        )
    )


def _data_boundary() -> RepoExternalDataBoundary:
    return RepoExternalDataBoundary.model_validate(
        _load_fixture("vnext_plus225", "repo_external_data_boundary_v225_reference.json")
    )


def _tool_boundary() -> RepoExternalToolBoundary:
    return RepoExternalToolBoundary.model_validate(
        _load_fixture("vnext_plus225", "repo_external_tool_boundary_v225_reference.json")
    )


def _submission_authority() -> RepoExternalSubmissionAuthorityReview:
    return RepoExternalSubmissionAuthorityReview.model_validate(
        _load_fixture(
            "vnext_plus225",
            "repo_external_submission_authority_review_v225_reference.json",
        )
    )


def _result_provenance() -> RepoExternalResultProvenanceContract:
    return RepoExternalResultProvenanceContract.model_validate(
        _load_fixture(
            "vnext_plus225",
            "repo_external_result_provenance_contract_v225_reference.json",
        )
    )


def _exceptions() -> RepoExternalBranchExceptionRegister:
    return RepoExternalBranchExceptionRegister.model_validate(
        _load_fixture(
            "vnext_plus225",
            "repo_external_branch_exception_register_v225_reference.json",
        )
    )


def _summary(
    name: str = "repo_external_branch_readiness_summary_v226_reference.json",
) -> RepoExternalBranchReadinessSummary:
    return RepoExternalBranchReadinessSummary.model_validate(_load_fixture("vnext_plus226", name))


def _handoff(
    name: str = "repo_post_external_branch_review_handoff_v226_reference.json",
) -> RepoPostExternalBranchReviewHandoff:
    return RepoPostExternalBranchReviewHandoff.model_validate(_load_fixture("vnext_plus226", name))


def _closeout(
    name: str = "repo_external_branch_review_family_closeout_alignment_v226_reference.json",
) -> RepoExternalBranchReviewFamilyCloseoutAlignment:
    return RepoExternalBranchReviewFamilyCloseoutAlignment.model_validate(
        _load_fixture("vnext_plus226", name)
    )


def _validate_reference_bundle_with(
    *,
    summary: RepoExternalBranchReadinessSummary | None = None,
    handoff: RepoPostExternalBranchReviewHandoff | None = None,
    closeout: RepoExternalBranchReviewFamilyCloseoutAlignment | None = None,
) -> None:
    resolved_summary = summary or _summary()
    resolved_handoff = handoff or _handoff()
    resolved_closeout = closeout or _closeout()
    if summary is not None and handoff is None:
        resolved_handoff = resolved_handoff.model_copy(
            update={
                "external_branch_readiness_summary_id": (
                    resolved_summary.external_branch_readiness_summary_id
                )
            }
        )
    if (summary is not None or handoff is not None) and closeout is None:
        resolved_closeout = resolved_closeout.model_copy(
            update={
                "external_branch_readiness_summary_id": (
                    resolved_summary.external_branch_readiness_summary_id
                ),
                "post_external_branch_review_handoff_id": (
                    resolved_handoff.post_external_branch_review_handoff_id
                ),
            }
        )
    validate_v80c_external_branch_review_closeout_bundle(
        external_branch_source_index=_v80a_source_index(),
        external_branch_review_request=_v80a_request(),
        external_branch_non_activation_guardrail=_v80a_guardrail(),
        external_data_boundary=_data_boundary(),
        external_tool_boundary=_tool_boundary(),
        external_submission_authority_review=_submission_authority(),
        external_result_provenance_contract=_result_provenance(),
        external_branch_exception_register=_exceptions(),
        external_branch_readiness_summary=resolved_summary,
        post_external_branch_review_handoff=resolved_handoff,
        external_branch_review_family_closeout_alignment=resolved_closeout,
    )


def test_v226_reference_bundle_validates() -> None:
    summary = _summary()
    handoff = _handoff()
    closeout = _closeout()

    assert summary.schema == REPO_EXTERNAL_BRANCH_READINESS_SUMMARY_SCHEMA
    assert handoff.schema == REPO_POST_EXTERNAL_BRANCH_REVIEW_HANDOFF_SCHEMA
    assert closeout.schema == REPO_EXTERNAL_BRANCH_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
    assert {row.external_activation_posture for row in summary.summary_rows} == {
        "no_external_branch_activation_performed_by_v80"
    }
    assert {row.external_submission_posture for row in handoff.handoff_rows} == {
        "no_external_submission_performed_by_v80"
    }
    assert "v81_selection" in closeout.unselected_future_surfaces

    _validate_reference_bundle_with(summary=summary, handoff=handoff, closeout=closeout)


def test_v226_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_external_branch_readiness_summary.v1.json").validate(
        _load_fixture(
            "vnext_plus226",
            "repo_external_branch_readiness_summary_v226_reference.json",
        )
    )
    _schema_validator("repo_post_external_branch_review_handoff.v1.json").validate(
        _load_fixture(
            "vnext_plus226",
            "repo_post_external_branch_review_handoff_v226_reference.json",
        )
    )
    _schema_validator(
        "repo_external_branch_review_family_closeout_alignment.v1.json"
    ).validate(
        _load_fixture(
            "vnext_plus226",
            "repo_external_branch_review_family_closeout_alignment_v226_reference.json",
        )
    )


def test_v226_derivation_helper_matches_reference_fixtures() -> None:
    (*_, summary, handoff, closeout) = derive_v80c_external_branch_review_closeout_bundle(
        repo_root=_repo_root()
    )

    assert summary.model_dump(mode="json") == _load_fixture(
        "vnext_plus226",
        "repo_external_branch_readiness_summary_v226_reference.json",
    )
    assert handoff.model_dump(mode="json") == _load_fixture(
        "vnext_plus226",
        "repo_post_external_branch_review_handoff_v226_reference.json",
    )
    assert closeout.model_dump(mode="json") == _load_fixture(
        "vnext_plus226",
        "repo_external_branch_review_family_closeout_alignment_v226_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_external_branch_v226_reject_summary_external_activation.json",
            RepoExternalBranchReadinessSummary,
            "V80-C summaries must not activate external branches",
        ),
        (
            "repo_external_branch_v226_reject_ready_summary_missing_data_boundary.json",
            RepoExternalBranchReadinessSummary,
            "ready external branch summaries require boundary refs",
        ),
        (
            "repo_external_branch_v226_reject_handoff_activates_external_branch.json",
            RepoPostExternalBranchReviewHandoff,
            "V80-C handoffs must not activate external branches",
        ),
        (
            "repo_external_branch_v226_reject_handoff_submits_externally.json",
            RepoPostExternalBranchReviewHandoff,
            "V80-C handoffs must not submit externally",
        ),
        (
            "repo_external_branch_v226_reject_product_handoff_ready.json",
            RepoPostExternalBranchReviewHandoff,
            "product handoffs cannot be external activation ready",
        ),
        (
            "repo_external_branch_v226_reject_closeout_selects_v81.json",
            RepoExternalBranchReviewFamilyCloseoutAlignment,
            "external branch closeout must not select V81",
        ),
    ],
)
def test_v226_reject_fixtures_fail_model_validation(
    fixture_name: str,
    model_type: type[
        RepoExternalBranchReadinessSummary
        | RepoPostExternalBranchReviewHandoff
        | RepoExternalBranchReviewFamilyCloseoutAlignment
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus226", fixture_name))


def test_v226_bundle_rejects_unknown_summary_request_ref() -> None:
    summary = _summary("repo_external_branch_v226_reject_summary_unknown_request_ref.json")

    with pytest.raises(ValueError, match="summary request refs must be known"):
        _validate_reference_bundle_with(summary=summary)


def test_v226_bundle_rejects_warning_ready_with_blocking_exception() -> None:
    summary = _summary(
        "repo_external_branch_v226_reject_warning_ready_carries_blocking_exception.json"
    )

    with pytest.raises(ValueError, match="ready summaries cannot hide blocking exceptions"):
        _validate_reference_bundle_with(summary=summary)


def test_v226_bundle_rejects_unknown_handoff_data_ref() -> None:
    handoff = _handoff("repo_external_branch_v226_reject_handoff_unknown_data_boundary_ref.json")

    with pytest.raises(ValueError, match="handoff data refs must be known"):
        _validate_reference_bundle_with(handoff=handoff)


def test_v226_bundle_rejects_closeout_unknown_summary_ref() -> None:
    closeout = _closeout("repo_external_branch_v226_reject_closeout_unknown_summary_ref.json")

    with pytest.raises(ValueError, match="V80-C closeout must reference released summary"):
        _validate_reference_bundle_with(closeout=closeout)
