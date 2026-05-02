from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CONTROLLED_EXECUTION_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_CONTROLLED_EXECUTION_REVIEW_SUMMARY_SCHEMA,
    REPO_POST_CONTROLLED_EXECUTION_REVIEW_HANDOFF_SCHEMA,
    RepoControlledExecutionExceptionRegister,
    RepoControlledExecutionNonExecutionGuardrail,
    RepoControlledExecutionReviewFamilyCloseoutAlignment,
    RepoControlledExecutionReviewRequest,
    RepoControlledExecutionReviewSummary,
    RepoControlledExecutionSourceIndex,
    RepoExecutionEffectMonitoringContract,
    RepoExecutionRunPlan,
    RepoPostControlledExecutionReviewHandoff,
    RepoToolInvocationPlan,
    derive_v79c_controlled_execution_review_closeout_bundle,
    validate_v79c_controlled_execution_review_closeout_bundle,
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


def _v79a_source_index() -> RepoControlledExecutionSourceIndex:
    return RepoControlledExecutionSourceIndex.model_validate(
        _load_fixture(
            "vnext_plus221",
            "repo_controlled_execution_source_index_v221_reference.json",
        )
    )


def _v79a_request() -> RepoControlledExecutionReviewRequest:
    return RepoControlledExecutionReviewRequest.model_validate(
        _load_fixture(
            "vnext_plus221",
            "repo_controlled_execution_review_request_v221_reference.json",
        )
    )


def _v79a_guardrail() -> RepoControlledExecutionNonExecutionGuardrail:
    return RepoControlledExecutionNonExecutionGuardrail.model_validate(
        _load_fixture(
            "vnext_plus221",
            "repo_controlled_execution_non_execution_guardrail_v221_reference.json",
        )
    )


def _run_plan() -> RepoExecutionRunPlan:
    return RepoExecutionRunPlan.model_validate(
        _load_fixture("vnext_plus222", "repo_execution_run_plan_v222_reference.json")
    )


def _tool_plan() -> RepoToolInvocationPlan:
    return RepoToolInvocationPlan.model_validate(
        _load_fixture("vnext_plus222", "repo_tool_invocation_plan_v222_reference.json")
    )


def _monitoring() -> RepoExecutionEffectMonitoringContract:
    return RepoExecutionEffectMonitoringContract.model_validate(
        _load_fixture(
            "vnext_plus222",
            "repo_execution_effect_monitoring_contract_v222_reference.json",
        )
    )


def _exceptions() -> RepoControlledExecutionExceptionRegister:
    return RepoControlledExecutionExceptionRegister.model_validate(
        _load_fixture(
            "vnext_plus222",
            "repo_controlled_execution_exception_register_v222_reference.json",
        )
    )


def _summary() -> RepoControlledExecutionReviewSummary:
    return RepoControlledExecutionReviewSummary.model_validate(
        _load_fixture(
            "vnext_plus223",
            "repo_controlled_execution_review_summary_v223_reference.json",
        )
    )


def _handoff() -> RepoPostControlledExecutionReviewHandoff:
    return RepoPostControlledExecutionReviewHandoff.model_validate(
        _load_fixture(
            "vnext_plus223",
            "repo_post_controlled_execution_review_handoff_v223_reference.json",
        )
    )


def _closeout() -> RepoControlledExecutionReviewFamilyCloseoutAlignment:
    return RepoControlledExecutionReviewFamilyCloseoutAlignment.model_validate(
        _load_fixture(
            "vnext_plus223",
            "repo_controlled_execution_review_family_closeout_alignment_v223_reference.json",
        )
    )


def _validate_reference_bundle_with(
    *,
    summary: RepoControlledExecutionReviewSummary | None = None,
    handoff: RepoPostControlledExecutionReviewHandoff | None = None,
    closeout: RepoControlledExecutionReviewFamilyCloseoutAlignment | None = None,
) -> None:
    validate_v79c_controlled_execution_review_closeout_bundle(
        controlled_execution_source_index=_v79a_source_index(),
        controlled_execution_review_request=_v79a_request(),
        controlled_execution_non_execution_guardrail=_v79a_guardrail(),
        execution_run_plan=_run_plan(),
        tool_invocation_plan=_tool_plan(),
        execution_effect_monitoring_contract=_monitoring(),
        controlled_execution_exception_register=_exceptions(),
        controlled_execution_review_summary=summary or _summary(),
        post_controlled_execution_review_handoff=handoff or _handoff(),
        controlled_execution_review_family_closeout_alignment=closeout or _closeout(),
    )


def test_v223_reference_bundle_validates() -> None:
    summary = _summary()
    handoff = _handoff()
    closeout = _closeout()

    assert summary.schema == REPO_CONTROLLED_EXECUTION_REVIEW_SUMMARY_SCHEMA
    assert handoff.schema == REPO_POST_CONTROLLED_EXECUTION_REVIEW_HANDOFF_SCHEMA
    assert closeout.schema == REPO_CONTROLLED_EXECUTION_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
    assert {row.execution_posture for row in summary.summary_rows} == {
        "no_execution_performed_by_v79"
    }
    assert {row.tool_invocation_posture for row in handoff.handoff_rows} == {
        "no_tool_invocation_performed_by_v79"
    }
    assert "v80_selection" in closeout.unselected_future_surfaces

    _validate_reference_bundle_with(summary=summary, handoff=handoff, closeout=closeout)


def test_v223_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_controlled_execution_review_summary.v1.json").validate(
        _load_fixture(
            "vnext_plus223",
            "repo_controlled_execution_review_summary_v223_reference.json",
        )
    )
    _schema_validator("repo_post_controlled_execution_review_handoff.v1.json").validate(
        _load_fixture(
            "vnext_plus223",
            "repo_post_controlled_execution_review_handoff_v223_reference.json",
        )
    )
    _schema_validator(
        "repo_controlled_execution_review_family_closeout_alignment.v1.json"
    ).validate(
        _load_fixture(
            "vnext_plus223",
            "repo_controlled_execution_review_family_closeout_alignment_v223_reference.json",
        )
    )


def test_v223_derivation_helper_matches_reference_fixtures() -> None:
    (*_, summary, handoff, closeout) = derive_v79c_controlled_execution_review_closeout_bundle(
        repo_root=_repo_root()
    )

    assert summary.model_dump(mode="json") == _load_fixture(
        "vnext_plus223",
        "repo_controlled_execution_review_summary_v223_reference.json",
    )
    assert handoff.model_dump(mode="json") == _load_fixture(
        "vnext_plus223",
        "repo_post_controlled_execution_review_handoff_v223_reference.json",
    )
    assert closeout.model_dump(mode="json") == _load_fixture(
        "vnext_plus223",
        "repo_controlled_execution_review_family_closeout_alignment_v223_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_controlled_execution_v223_reject_summary_execution_claim.json",
            RepoControlledExecutionReviewSummary,
            "V79-C summaries must not execute commands",
        ),
        (
            "repo_controlled_execution_v223_reject_ready_summary_missing_run_plan.json",
            RepoControlledExecutionReviewSummary,
            "ready summaries require complete review package refs",
        ),
        (
            "repo_controlled_execution_v223_reject_execution_trial_handoff_missing_authority.json",
            RepoPostControlledExecutionReviewHandoff,
            "execution-trial handoffs require review package refs",
        ),
        (
            "repo_controlled_execution_v223_reject_product_handoff_ready.json",
            RepoPostControlledExecutionReviewHandoff,
            "product handoffs cannot be execution-trial ready",
        ),
        (
            "repo_controlled_execution_v223_reject_handoff_schedules_execution.json",
            RepoPostControlledExecutionReviewHandoff,
            "V79-C handoffs must not schedule or perform execution",
        ),
        (
            "repo_controlled_execution_v223_reject_closeout_selects_v80.json",
            RepoControlledExecutionReviewFamilyCloseoutAlignment,
            "controlled execution closeout must not select V80",
        ),
    ],
)
def test_v223_reject_fixtures_fail_model_validation(
    fixture_name: str,
    model_type: type[
        RepoControlledExecutionReviewSummary
        | RepoPostControlledExecutionReviewHandoff
        | RepoControlledExecutionReviewFamilyCloseoutAlignment
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus223", fixture_name))


def test_v223_bundle_rejects_ready_summary_with_blocking_exception() -> None:
    summary = RepoControlledExecutionReviewSummary.model_validate(
        _load_fixture(
            "vnext_plus223",
            "repo_controlled_execution_v223_reject_ready_summary_hides_blocker.json",
        )
    )
    closeout = _closeout().model_copy(
        update={
            "controlled_execution_review_summary_id": (
                summary.controlled_execution_review_summary_id
            )
        }
    )
    handoff = _handoff().model_copy(
        update={
            "controlled_execution_review_summary_id": (
                summary.controlled_execution_review_summary_id
            )
        }
    )

    with pytest.raises(ValueError, match="ready summaries cannot hide blocking exceptions"):
        _validate_reference_bundle_with(summary=summary, handoff=handoff, closeout=closeout)


def test_v223_bundle_rejects_ready_handoff_with_blocking_exception() -> None:
    handoff = RepoPostControlledExecutionReviewHandoff.model_validate(
        _load_fixture(
            "vnext_plus223",
            "repo_controlled_execution_v223_reject_handoff_ready_with_blocker.json",
        )
    )
    closeout = _closeout().model_copy(
        update={
            "post_controlled_execution_review_handoff_id": (
                handoff.post_controlled_execution_review_handoff_id
            )
        }
    )

    with pytest.raises(ValueError, match="handoffs with blocking exceptions cannot be ready"):
        _validate_reference_bundle_with(handoff=handoff, closeout=closeout)


def test_v223_bundle_rejects_handoff_summary_candidate_mismatch() -> None:
    handoff = _handoff()
    row = handoff.handoff_rows[0].model_copy(update={"candidate_ref": "candidate:v79:other"})
    mismatched_handoff = handoff.model_copy(
        update={"handoff_rows": [row, *handoff.handoff_rows[1:]]}
    )

    with pytest.raises(ValueError, match="handoff summary refs must match candidate"):
        _validate_reference_bundle_with(handoff=mismatched_handoff)
