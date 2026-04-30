from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_DISPATCH_RECONCILIATION_CONTRACT_SCHEMA,
    REPO_DISPATCH_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_POST_DISPATCH_REVIEW_HANDOFF_SCHEMA,
    REPO_WORKER_OUTPUT_RECONCILIATION_PLAN_SCHEMA,
    RepoDispatchExceptionRegister,
    RepoDispatchNonExecutionGuardrail,
    RepoDispatchReconciliationContract,
    RepoDispatchReviewFamilyCloseoutAlignment,
    RepoDispatchReviewRequest,
    RepoDispatchSourceIndex,
    RepoMultiWorkerAssignmentPlan,
    RepoPostDispatchReviewHandoff,
    RepoWorkerIOContract,
    RepoWorkerOutputReconciliationPlan,
    RepoWorkerRoleCapacityProfile,
    RepoWorkerToolApplicabilityMatrix,
    derive_v75c_dispatch_review_closeout_bundle,
    derive_v75c_repo_dispatch_reconciliation_contract,
    derive_v75c_repo_post_dispatch_review_handoff,
    validate_v75c_dispatch_review_closeout_bundle,
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


def _v75a_source_index() -> RepoDispatchSourceIndex:
    return RepoDispatchSourceIndex.model_validate(
        _load_fixture("vnext_plus209", "repo_dispatch_source_index_v209_reference.json")
    )


def _v75a_request() -> RepoDispatchReviewRequest:
    return RepoDispatchReviewRequest.model_validate(
        _load_fixture("vnext_plus209", "repo_dispatch_review_request_v209_reference.json")
    )


def _v75a_guardrail() -> RepoDispatchNonExecutionGuardrail:
    return RepoDispatchNonExecutionGuardrail.model_validate(
        _load_fixture(
            "vnext_plus209",
            "repo_dispatch_non_execution_guardrail_v209_reference.json",
        )
    )


def _role_profile() -> RepoWorkerRoleCapacityProfile:
    return RepoWorkerRoleCapacityProfile.model_validate(
        _load_fixture(
            "vnext_plus210",
            "repo_worker_role_capacity_profile_v210_reference.json",
        )
    )


def _assignment_plan() -> RepoMultiWorkerAssignmentPlan:
    return RepoMultiWorkerAssignmentPlan.model_validate(
        _load_fixture(
            "vnext_plus210",
            "repo_multi_worker_assignment_plan_v210_reference.json",
        )
    )


def _io_contract() -> RepoWorkerIOContract:
    return RepoWorkerIOContract.model_validate(
        _load_fixture("vnext_plus210", "repo_worker_io_contract_v210_reference.json")
    )


def _tool_matrix() -> RepoWorkerToolApplicabilityMatrix:
    return RepoWorkerToolApplicabilityMatrix.model_validate(
        _load_fixture(
            "vnext_plus210",
            "repo_worker_tool_applicability_matrix_v210_reference.json",
        )
    )


def _exception_register() -> RepoDispatchExceptionRegister:
    return RepoDispatchExceptionRegister.model_validate(
        _load_fixture(
            "vnext_plus210",
            "repo_dispatch_exception_register_v210_reference.json",
        )
    )


def _reconciliation_plan() -> RepoWorkerOutputReconciliationPlan:
    return RepoWorkerOutputReconciliationPlan.model_validate(
        _load_fixture(
            "vnext_plus211",
            "repo_worker_output_reconciliation_plan_v211_reference.json",
        )
    )


def _contract() -> RepoDispatchReconciliationContract:
    return RepoDispatchReconciliationContract.model_validate(
        _load_fixture(
            "vnext_plus211",
            "repo_dispatch_reconciliation_contract_v211_reference.json",
        )
    )


def _handoff() -> RepoPostDispatchReviewHandoff:
    return RepoPostDispatchReviewHandoff.model_validate(
        _load_fixture("vnext_plus211", "repo_post_dispatch_review_handoff_v211_reference.json")
    )


def _family_closeout() -> RepoDispatchReviewFamilyCloseoutAlignment:
    return RepoDispatchReviewFamilyCloseoutAlignment.model_validate(
        _load_fixture(
            "vnext_plus211",
            "repo_dispatch_review_family_closeout_alignment_v211_reference.json",
        )
    )


def _handoff_from_payload(payload: dict[str, Any]) -> RepoPostDispatchReviewHandoff:
    payload["post_dispatch_review_handoff_id"] = _surface_id(
        "repo_post_dispatch_review_handoff",
        REPO_POST_DISPATCH_REVIEW_HANDOFF_SCHEMA,
        payload,
        "post_dispatch_review_handoff_id",
    )
    return RepoPostDispatchReviewHandoff.model_validate(payload)


def _validate_reference_bundle_with(
    *,
    reconciliation_plan: RepoWorkerOutputReconciliationPlan | None = None,
    contract: RepoDispatchReconciliationContract | None = None,
    handoff: RepoPostDispatchReviewHandoff | None = None,
    family_closeout: RepoDispatchReviewFamilyCloseoutAlignment | None = None,
) -> None:
    validate_v75c_dispatch_review_closeout_bundle(
        dispatch_source_index=_v75a_source_index(),
        dispatch_review_request=_v75a_request(),
        dispatch_non_execution_guardrail=_v75a_guardrail(),
        worker_role_capacity_profile=_role_profile(),
        multi_worker_assignment_plan=_assignment_plan(),
        worker_io_contract=_io_contract(),
        worker_tool_applicability_matrix=_tool_matrix(),
        dispatch_exception_register=_exception_register(),
        worker_output_reconciliation_plan=reconciliation_plan or _reconciliation_plan(),
        dispatch_reconciliation_contract=contract or _contract(),
        post_dispatch_review_handoff=handoff or _handoff(),
        dispatch_review_family_closeout_alignment=family_closeout or _family_closeout(),
    )


def test_v211_reference_bundle_validates() -> None:
    reconciliation_plan = _reconciliation_plan()
    contract = _contract()
    handoff = _handoff()
    family_closeout = _family_closeout()

    assert reconciliation_plan.schema == REPO_WORKER_OUTPUT_RECONCILIATION_PLAN_SCHEMA
    assert contract.schema == REPO_DISPATCH_RECONCILIATION_CONTRACT_SCHEMA
    assert handoff.schema == REPO_POST_DISPATCH_REVIEW_HANDOFF_SCHEMA
    assert family_closeout.schema == REPO_DISPATCH_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
    dispatch_execution_postures = {
        row.dispatch_execution_posture for row in reconciliation_plan.reconciliation_plan_rows
    }
    assert dispatch_execution_postures == {"no_dispatch_executed_by_v75"}
    assert {
        row.output_presence_posture for row in reconciliation_plan.reconciliation_plan_rows
    } == {"projected_not_observed"}
    assert family_closeout.closed_slice_ladder == ["V75-A", "V75-B", "V75-C"]

    _validate_reference_bundle_with(
        reconciliation_plan=reconciliation_plan,
        contract=contract,
        handoff=handoff,
        family_closeout=family_closeout,
    )


def test_v211_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_worker_output_reconciliation_plan.v1.json").validate(
        _load_fixture(
            "vnext_plus211",
            "repo_worker_output_reconciliation_plan_v211_reference.json",
        )
    )
    _schema_validator("repo_dispatch_reconciliation_contract.v1.json").validate(
        _load_fixture(
            "vnext_plus211",
            "repo_dispatch_reconciliation_contract_v211_reference.json",
        )
    )
    _schema_validator("repo_post_dispatch_review_handoff.v1.json").validate(
        _load_fixture("vnext_plus211", "repo_post_dispatch_review_handoff_v211_reference.json")
    )
    _schema_validator("repo_dispatch_review_family_closeout_alignment.v1.json").validate(
        _load_fixture(
            "vnext_plus211",
            "repo_dispatch_review_family_closeout_alignment_v211_reference.json",
        )
    )


def test_v211_derivation_helper_matches_reference_fixtures() -> None:
    reconciliation_plan, contract, handoff, family_closeout = (
        derive_v75c_dispatch_review_closeout_bundle(repo_root=_repo_root())
    )

    assert reconciliation_plan.model_dump(mode="json") == _load_fixture(
        "vnext_plus211",
        "repo_worker_output_reconciliation_plan_v211_reference.json",
    )
    assert contract.model_dump(mode="json") == _load_fixture(
        "vnext_plus211",
        "repo_dispatch_reconciliation_contract_v211_reference.json",
    )
    assert handoff.model_dump(mode="json") == _load_fixture(
        "vnext_plus211",
        "repo_post_dispatch_review_handoff_v211_reference.json",
    )
    assert family_closeout.model_dump(mode="json") == _load_fixture(
        "vnext_plus211",
        "repo_dispatch_review_family_closeout_alignment_v211_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_dispatch_review_v211_reject_worker_output_truth.json",
            RepoWorkerOutputReconciliationPlan,
            "non_truth_guardrail must mention not truth",
        ),
        (
            "repo_dispatch_review_v211_reject_dispatch_executed.json",
            RepoWorkerOutputReconciliationPlan,
            "may not carry dispatch or downstream authority",
        ),
        (
            "repo_dispatch_review_v211_reject_projected_with_observed_output.json",
            RepoWorkerOutputReconciliationPlan,
            "projected output rows must not carry observed worker outputs",
        ),
        (
            "repo_dispatch_review_v211_reject_relation_without_source.json",
            RepoWorkerOutputReconciliationPlan,
            "at least 1 item",
        ),
        (
            "repo_dispatch_review_v211_reject_contract_missing_forbidden_inference.json",
            RepoDispatchReconciliationContract,
            "omit forbidden inferences",
        ),
        (
            "repo_dispatch_review_v211_reject_handoff_claims_dispatch_execution.json",
            RepoPostDispatchReviewHandoff,
            "may not carry dispatch or downstream authority",
        ),
        (
            "repo_dispatch_review_v211_reject_family_closeout_overclaims.json",
            RepoDispatchReviewFamilyCloseoutAlignment,
            "may not carry dispatch or downstream authority",
        ),
    ],
)
def test_v211_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoWorkerOutputReconciliationPlan
        | RepoDispatchReconciliationContract
        | RepoPostDispatchReviewHandoff
        | RepoDispatchReviewFamilyCloseoutAlignment
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus211", fixture_name))


def test_v211_bundle_rejects_ready_handoff_with_blocking_exception() -> None:
    handoff = _handoff_from_payload(
        _load_fixture(
            "vnext_plus211",
            "repo_dispatch_review_v211_reject_ready_handoff_with_blocking_exception.json",
        )
    )

    with pytest.raises(
        ValueError,
        match="blocking exceptions prevent ready handoff outside arbiter review",
    ):
        _validate_reference_bundle_with(handoff=handoff)


def test_v211_bundle_rejects_missing_v75a_request_ref() -> None:
    payload = _reconciliation_plan().model_dump(mode="json")
    for row in payload["reconciliation_plan_rows"]:
        if row["reconciliation_plan_ref"] == "reconciliation-plan:v75c:self-evidencing:projected":
            row["dispatch_request_refs"] = ["dispatch-request:v75a:unknown"]
    payload["worker_output_reconciliation_plan_id"] = _surface_id(
        "repo_worker_output_reconciliation_plan",
        REPO_WORKER_OUTPUT_RECONCILIATION_PLAN_SCHEMA,
        payload,
        "worker_output_reconciliation_plan_id",
    )
    reconciliation_plan = RepoWorkerOutputReconciliationPlan.model_validate(payload)
    contract = derive_v75c_repo_dispatch_reconciliation_contract(
        worker_output_reconciliation_plan=reconciliation_plan
    )
    handoff = derive_v75c_repo_post_dispatch_review_handoff(
        worker_output_reconciliation_plan=reconciliation_plan,
        dispatch_reconciliation_contract=contract,
    )

    with pytest.raises(
        ValueError,
        match="reconciliation plans must reference released V75-A requests",
    ):
        _validate_reference_bundle_with(
            reconciliation_plan=reconciliation_plan,
            contract=contract,
            handoff=handoff,
        )


def test_v211_bundle_rejects_missing_v75b_assignment_ref() -> None:
    payload = _reconciliation_plan().model_dump(mode="json")
    for row in payload["reconciliation_plan_rows"]:
        if row["reconciliation_plan_ref"] == "reconciliation-plan:v75c:self-evidencing:projected":
            row["assignment_plan_refs"] = ["assignment-plan:v75b:unknown"]
    payload["worker_output_reconciliation_plan_id"] = _surface_id(
        "repo_worker_output_reconciliation_plan",
        REPO_WORKER_OUTPUT_RECONCILIATION_PLAN_SCHEMA,
        payload,
        "worker_output_reconciliation_plan_id",
    )
    reconciliation_plan = RepoWorkerOutputReconciliationPlan.model_validate(payload)
    contract = derive_v75c_repo_dispatch_reconciliation_contract(
        worker_output_reconciliation_plan=reconciliation_plan
    )
    handoff = derive_v75c_repo_post_dispatch_review_handoff(
        worker_output_reconciliation_plan=reconciliation_plan,
        dispatch_reconciliation_contract=contract,
    )

    with pytest.raises(
        ValueError,
        match="reconciliation plans must reference released V75-B assignments",
    ):
        _validate_reference_bundle_with(
            reconciliation_plan=reconciliation_plan,
            contract=contract,
            handoff=handoff,
        )
