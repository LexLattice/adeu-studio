from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_DISPATCH_EXCEPTION_REGISTER_SCHEMA,
    REPO_MULTI_WORKER_ASSIGNMENT_PLAN_SCHEMA,
    REPO_WORKER_IO_CONTRACT_SCHEMA,
    REPO_WORKER_ROLE_CAPACITY_PROFILE_SCHEMA,
    REPO_WORKER_TOOL_APPLICABILITY_MATRIX_SCHEMA,
    RepoDispatchExceptionRegister,
    RepoDispatchNonExecutionGuardrail,
    RepoDispatchReviewRequest,
    RepoDispatchSourceIndex,
    RepoMultiWorkerAssignmentPlan,
    RepoWorkerIOContract,
    RepoWorkerRoleCapacityProfile,
    RepoWorkerToolApplicabilityMatrix,
    derive_v75b_worker_orchestration_bundle,
    validate_v75b_worker_orchestration_bundle,
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


def _assignment_from_payload(payload: dict[str, Any]) -> RepoMultiWorkerAssignmentPlan:
    payload["multi_worker_assignment_plan_id"] = _surface_id(
        "repo_multi_worker_assignment_plan",
        REPO_MULTI_WORKER_ASSIGNMENT_PLAN_SCHEMA,
        payload,
        "multi_worker_assignment_plan_id",
    )
    return RepoMultiWorkerAssignmentPlan.model_validate(payload)


def _validate_reference_bundle_with(
    *,
    role_profile: RepoWorkerRoleCapacityProfile | None = None,
    assignment_plan: RepoMultiWorkerAssignmentPlan | None = None,
    io_contract: RepoWorkerIOContract | None = None,
    tool_matrix: RepoWorkerToolApplicabilityMatrix | None = None,
    exception_register: RepoDispatchExceptionRegister | None = None,
) -> None:
    validate_v75b_worker_orchestration_bundle(
        dispatch_source_index=_v75a_source_index(),
        dispatch_review_request=_v75a_request(),
        dispatch_non_execution_guardrail=_v75a_guardrail(),
        worker_role_capacity_profile=role_profile or _role_profile(),
        multi_worker_assignment_plan=assignment_plan or _assignment_plan(),
        worker_io_contract=io_contract or _io_contract(),
        worker_tool_applicability_matrix=tool_matrix or _tool_matrix(),
        dispatch_exception_register=exception_register or _exception_register(),
    )


def test_v210_reference_bundle_validates() -> None:
    role_profile = _role_profile()
    assignment_plan = _assignment_plan()
    io_contract = _io_contract()
    tool_matrix = _tool_matrix()
    exception_register = _exception_register()

    assert role_profile.schema == REPO_WORKER_ROLE_CAPACITY_PROFILE_SCHEMA
    assert assignment_plan.schema == REPO_MULTI_WORKER_ASSIGNMENT_PLAN_SCHEMA
    assert io_contract.schema == REPO_WORKER_IO_CONTRACT_SCHEMA
    assert tool_matrix.schema == REPO_WORKER_TOOL_APPLICABILITY_MATRIX_SCHEMA
    assert exception_register.schema == REPO_DISPATCH_EXCEPTION_REGISTER_SCHEMA
    assert {row.assignment_plan_posture for row in assignment_plan.assignment_plan_rows} == {
        "blocked_by_later_authority",
        "plan_ready_for_review",
    }
    assert {row.assignment_execution_posture for row in assignment_plan.assignment_plan_rows} == {
        "no_execution_authorized"
    }

    _validate_reference_bundle_with(
        role_profile=role_profile,
        assignment_plan=assignment_plan,
        io_contract=io_contract,
        tool_matrix=tool_matrix,
        exception_register=exception_register,
    )


def test_v210_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_worker_role_capacity_profile.v1.json").validate(
        _load_fixture("vnext_plus210", "repo_worker_role_capacity_profile_v210_reference.json")
    )
    _schema_validator("repo_multi_worker_assignment_plan.v1.json").validate(
        _load_fixture("vnext_plus210", "repo_multi_worker_assignment_plan_v210_reference.json")
    )
    _schema_validator("repo_worker_io_contract.v1.json").validate(
        _load_fixture("vnext_plus210", "repo_worker_io_contract_v210_reference.json")
    )
    _schema_validator("repo_worker_tool_applicability_matrix.v1.json").validate(
        _load_fixture(
            "vnext_plus210",
            "repo_worker_tool_applicability_matrix_v210_reference.json",
        )
    )
    _schema_validator("repo_dispatch_exception_register.v1.json").validate(
        _load_fixture("vnext_plus210", "repo_dispatch_exception_register_v210_reference.json")
    )


def test_v210_derivation_helper_matches_reference_fixtures() -> None:
    role_profile, assignment_plan, io_contract, tool_matrix, exception_register = (
        derive_v75b_worker_orchestration_bundle(repo_root=_repo_root())
    )

    assert role_profile.model_dump(mode="json") == _load_fixture(
        "vnext_plus210",
        "repo_worker_role_capacity_profile_v210_reference.json",
    )
    assert assignment_plan.model_dump(mode="json") == _load_fixture(
        "vnext_plus210",
        "repo_multi_worker_assignment_plan_v210_reference.json",
    )
    assert io_contract.model_dump(mode="json") == _load_fixture(
        "vnext_plus210",
        "repo_worker_io_contract_v210_reference.json",
    )
    assert tool_matrix.model_dump(mode="json") == _load_fixture(
        "vnext_plus210",
        "repo_worker_tool_applicability_matrix_v210_reference.json",
    )
    assert exception_register.model_dump(mode="json") == _load_fixture(
        "vnext_plus210",
        "repo_dispatch_exception_register_v210_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_dispatch_review_v210_reject_role_permission.json",
            RepoWorkerRoleCapacityProfile,
            "may not carry dispatch or downstream authority",
        ),
        (
            "repo_dispatch_review_v210_reject_assignment_executes.json",
            RepoMultiWorkerAssignmentPlan,
            "assignment plans must have no execution authorized",
        ),
        (
            "repo_dispatch_review_v210_reject_io_output_truth.json",
            RepoWorkerIOContract,
            "non_truth_guardrail must mention not truth",
        ),
        (
            "repo_dispatch_review_v210_reject_tool_global_scope.json",
            RepoWorkerToolApplicabilityMatrix,
            "limitation_note must mention target-bound",
        ),
        (
            "repo_dispatch_review_v210_reject_exception_resolved.json",
            RepoDispatchExceptionRegister,
            "V75-B exception rows may not mark exceptions resolved",
        ),
    ],
)
def test_v210_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoWorkerRoleCapacityProfile
        | RepoMultiWorkerAssignmentPlan
        | RepoWorkerIOContract
        | RepoWorkerToolApplicabilityMatrix
        | RepoDispatchExceptionRegister
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus210", fixture_name))


def test_v210_bundle_rejects_unknown_dispatch_request_ref() -> None:
    assignment_payload = _assignment_plan().model_dump(mode="json")
    for row in assignment_payload["assignment_plan_rows"]:
        if row["assignment_plan_ref"] == "assignment-plan:v75b:self-evidencing:review-only":
            row["dispatch_request_refs"] = ["dispatch-request:v75a:unknown"]
    assignment_plan = _assignment_from_payload(assignment_payload)

    with pytest.raises(ValueError, match="assignment plans must reference released V75-A request"):
        _validate_reference_bundle_with(assignment_plan=assignment_plan)


def test_v210_bundle_rejects_missing_required_later_authority() -> None:
    assignment_payload = _assignment_plan().model_dump(mode="json")
    for row in assignment_payload["assignment_plan_rows"]:
        if row["assignment_plan_ref"] == "assignment-plan:v75b:self-evidencing:review-only":
            row["required_later_authority_refs"] = [
                "authority:v75a:self-evidencing:dispatch-execution"
            ]
    assignment_plan = _assignment_from_payload(assignment_payload)

    with pytest.raises(ValueError, match="assignment plans must carry required later authority"):
        _validate_reference_bundle_with(assignment_plan=assignment_plan)


def test_v210_bundle_rejects_mismatched_upstream_exception() -> None:
    assignment_payload = _assignment_plan().model_dump(mode="json")
    for row in assignment_payload["assignment_plan_rows"]:
        if row["assignment_plan_ref"] == "assignment-plan:v75b:self-evidencing:review-only":
            row["exception_refs"] = ["dispatch-exception:v75b:product-wedge:authority"]
    assignment_plan = _assignment_from_payload(assignment_payload)

    with pytest.raises(ValueError, match="assignment plans must carry upstream exception refs"):
        _validate_reference_bundle_with(assignment_plan=assignment_plan)


def test_v210_bundle_rejects_io_role_mismatch() -> None:
    assignment_payload = _assignment_plan().model_dump(mode="json")
    for row in assignment_payload["assignment_plan_rows"]:
        if row["assignment_plan_ref"] == "assignment-plan:v75b:product-wedge:blocked":
            row["io_contract_refs"] = ["io-contract:v75b:self-evidencing:evidence-review"]
    assignment_plan = _assignment_from_payload(assignment_payload)

    with pytest.raises(ValueError, match="assignment IO refs must cover assignment worker roles"):
        _validate_reference_bundle_with(assignment_plan=assignment_plan)


def test_v210_bundle_rejects_tool_role_mismatch() -> None:
    assignment_payload = _assignment_plan().model_dump(mode="json")
    for row in assignment_payload["assignment_plan_rows"]:
        if row["assignment_plan_ref"] == "assignment-plan:v75b:product-wedge:blocked":
            row["tool_applicability_refs"] = ["tool-matrix:v75b:self-evidencing:pytest-schema"]
    assignment_plan = _assignment_from_payload(assignment_payload)

    with pytest.raises(ValueError, match="assignment tool refs must cover assignment worker roles"):
        _validate_reference_bundle_with(assignment_plan=assignment_plan)


def test_v210_bundle_rejects_external_branch_plan_without_v43_or_blocker() -> None:
    assignment_payload = _assignment_plan().model_dump(mode="json")
    for row in assignment_payload["assignment_plan_rows"]:
        if row["assignment_plan_ref"] == "assignment-plan:v75b:product-wedge:blocked":
            row["assignment_plan_posture"] = "plan_ready_for_review"
    assignment_plan = _assignment_from_payload(assignment_payload)

    with pytest.raises(
        ValueError,
        match="external branch worker plans require V43 source or blocked posture",
    ):
        _validate_reference_bundle_with(assignment_plan=assignment_plan)
