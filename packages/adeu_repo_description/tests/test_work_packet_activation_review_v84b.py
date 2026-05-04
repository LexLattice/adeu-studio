from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_IMPLEMENTATION_TARGET_SURFACE_BOUNDARY_SCHEMA,
    REPO_WORK_PACKET_ACTIVATION_EXCEPTION_REGISTER_SCHEMA,
    REPO_WORK_PACKET_SCOPE_CONTRACT_SCHEMA,
    REPO_WORK_PACKET_VALIDATION_EVIDENCE_PLAN_SCHEMA,
    RepoImplementationTargetSurfaceBoundary,
    RepoWorkPacketActivationExceptionRegister,
    RepoWorkPacketScopeContract,
    RepoWorkPacketValidationEvidencePlan,
    derive_v84b_repo_implementation_target_surface_boundary,
    derive_v84b_repo_work_packet_activation_exception_register,
    derive_v84b_repo_work_packet_validation_evidence_plan,
    derive_v84b_work_packet_package_review_bundle,
    validate_v84b_work_packet_package_review_bundle,
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


def _v84b_scope(
    name: str = "repo_work_packet_scope_contract_v237_reference.json",
) -> RepoWorkPacketScopeContract:
    return RepoWorkPacketScopeContract.model_validate(_load_fixture("vnext_plus237", name))


def _v84b_target_boundary(
    name: str = "repo_implementation_target_surface_boundary_v237_reference.json",
) -> RepoImplementationTargetSurfaceBoundary:
    return RepoImplementationTargetSurfaceBoundary.model_validate(
        _load_fixture("vnext_plus237", name)
    )


def _v84b_validation_plan(
    name: str = "repo_work_packet_validation_evidence_plan_v237_reference.json",
) -> RepoWorkPacketValidationEvidencePlan:
    return RepoWorkPacketValidationEvidencePlan.model_validate(
        _load_fixture("vnext_plus237", name)
    )


def _v84b_exception_register(
    name: str = "repo_work_packet_activation_exception_register_v237_reference.json",
) -> RepoWorkPacketActivationExceptionRegister:
    return RepoWorkPacketActivationExceptionRegister.model_validate(
        _load_fixture("vnext_plus237", name)
    )


def _validate_reference_bundle_with(
    *,
    scope: RepoWorkPacketScopeContract | None = None,
    target_boundary: RepoImplementationTargetSurfaceBoundary | None = None,
    validation_plan: RepoWorkPacketValidationEvidencePlan | None = None,
    exception_register: RepoWorkPacketActivationExceptionRegister | None = None,
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
        v84a_source_index,
        v84a_request,
        v84a_guardrail,
        derived_scope,
        derived_target_boundary,
        derived_validation_plan,
        derived_exception_register,
    ) = derive_v84b_work_packet_package_review_bundle()
    actual_scope = scope or derived_scope
    actual_target_boundary = target_boundary or (
        derive_v84b_repo_implementation_target_surface_boundary(
            work_packet_scope_contract=actual_scope
        )
        if scope is not None
        else derived_target_boundary
    )
    actual_validation_plan = validation_plan or (
        derive_v84b_repo_work_packet_validation_evidence_plan(
            work_packet_scope_contract=actual_scope,
            implementation_target_surface_boundary=actual_target_boundary,
        )
        if scope is not None or target_boundary is not None
        else derived_validation_plan
    )
    actual_exception_register = exception_register or (
        derive_v84b_repo_work_packet_activation_exception_register(
            work_packet_scope_contract=actual_scope,
            implementation_target_surface_boundary=actual_target_boundary,
            work_packet_validation_evidence_plan=actual_validation_plan,
        )
        if scope is not None or target_boundary is not None or validation_plan is not None
        else derived_exception_register
    )
    validate_v84b_work_packet_package_review_bundle(
        v83_intent_source_index=v83_source_index,
        v83_semantic_intent_contract=v83_contract,
        v83_intent_non_implementation_guardrail=v83_guardrail,
        v83_intent_edge_decomposition=v83_edge_decomposition,
        v83_artifact_obligation_map=v83_obligation_map,
        v83_semantic_drift_ambiguity_register=v83_drift_register,
        v83_implementation_spec_projection_packet=v83_projection_packet,
        v83_intent_to_work_packet_handoff=v83_handoff,
        v83_semantic_implementation_spec_family_closeout_alignment=v83_closeout,
        work_packet_activation_source_index=v84a_source_index,
        work_packet_activation_review_request=v84a_request,
        work_packet_activation_non_execution_guardrail=v84a_guardrail,
        work_packet_scope_contract=actual_scope,
        implementation_target_surface_boundary=actual_target_boundary,
        work_packet_validation_evidence_plan=actual_validation_plan,
        work_packet_activation_exception_register=actual_exception_register,
    )


def test_v84b_reference_fixtures_match_derivation() -> None:
    *_, scope, target_boundary, validation_plan, exception_register = (
        derive_v84b_work_packet_package_review_bundle()
    )
    assert scope.model_dump(mode="json") == _load_fixture(
        "vnext_plus237",
        "repo_work_packet_scope_contract_v237_reference.json",
    )
    assert target_boundary.model_dump(mode="json") == _load_fixture(
        "vnext_plus237",
        "repo_implementation_target_surface_boundary_v237_reference.json",
    )
    assert validation_plan.model_dump(mode="json") == _load_fixture(
        "vnext_plus237",
        "repo_work_packet_validation_evidence_plan_v237_reference.json",
    )
    assert exception_register.model_dump(mode="json") == _load_fixture(
        "vnext_plus237",
        "repo_work_packet_activation_exception_register_v237_reference.json",
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name"),
    [
        (
            REPO_WORK_PACKET_SCOPE_CONTRACT_SCHEMA,
            "repo_work_packet_scope_contract.v1.json",
            "repo_work_packet_scope_contract_v237_reference.json",
        ),
        (
            REPO_IMPLEMENTATION_TARGET_SURFACE_BOUNDARY_SCHEMA,
            "repo_implementation_target_surface_boundary.v1.json",
            "repo_implementation_target_surface_boundary_v237_reference.json",
        ),
        (
            REPO_WORK_PACKET_VALIDATION_EVIDENCE_PLAN_SCHEMA,
            "repo_work_packet_validation_evidence_plan.v1.json",
            "repo_work_packet_validation_evidence_plan_v237_reference.json",
        ),
        (
            REPO_WORK_PACKET_ACTIVATION_EXCEPTION_REGISTER_SCHEMA,
            "repo_work_packet_activation_exception_register.v1.json",
            "repo_work_packet_activation_exception_register_v237_reference.json",
        ),
    ],
)
def test_v84b_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
) -> None:
    payload = _load_fixture("vnext_plus237", fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)


def test_v84b_reference_bundle_links_released_v84a_and_v83c_substrate() -> None:
    _validate_reference_bundle_with(
        scope=_v84b_scope(),
        target_boundary=_v84b_target_boundary(),
        validation_plan=_v84b_validation_plan(),
        exception_register=_v84b_exception_register(),
    )


def test_v84b_reference_preserves_review_only_package_boundary() -> None:
    scope_row = _v84b_scope().scope_contract_rows[0]
    assert scope_row.activation_package_ref
    assert scope_row.scope_completeness_posture == "complete_for_activation_review_only"
    assert scope_row.activation_review_posture == "package_ready_for_review_only"
    assert scope_row.work_packet_execution_posture == (
        "no_work_packet_execution_performed_by_v84"
    )
    assert scope_row.implementation_execution_posture == "no_implementation_performed_by_v84"
    assert scope_row.canonical_lock_requirement_rows[0].lock_not_created_by_v84 is True
    assert {
        row.target_access_role
        for target in _v84b_target_boundary().target_boundary_rows
        for row in target.target_access_role_rows
    } == {
        "forbidden_target",
        "generated_artifact_target",
        "prospective_write_target_for_later_lock",
    }


def test_v84b_validation_matrix_is_edge_and_obligation_complete() -> None:
    validation_row = _v84b_validation_plan().validation_plan_rows[0]
    covered_edges = {
        ref
        for matrix_row in validation_row.validation_matrix_rows
        for ref in matrix_row.semantic_edge_refs
    }
    covered_obligations = {
        ref
        for matrix_row in validation_row.validation_matrix_rows
        for ref in matrix_row.artifact_obligation_refs
    }
    assert set(validation_row.semantic_edge_refs).issubset(covered_edges)
    assert set(validation_row.artifact_obligation_refs).issubset(covered_obligations)
    assert validation_row.tool_run_posture == "no_tool_run_performed_by_v84"
    assert validation_row.tests_not_truth_guardrail == "Tests are requirements, not truth."


@pytest.mark.parametrize(
    ("fixture_name", "message"),
    [
        (
            "repo_work_packet_activation_v237_reject_target_glob_boundary.json",
            "target globs cannot become implementation target boundaries",
        ),
        (
            "repo_work_packet_activation_v237_reject_bounded_directory_missing_child_refs.json",
            "bounded directories require concrete child refs",
        ),
    ],
)
def test_v84b_target_boundaries_reject_unbounded_targets(
    fixture_name: str,
    message: str,
) -> None:
    with pytest.raises(ValidationError, match=message):
        RepoImplementationTargetSurfaceBoundary.model_validate(
            _load_fixture("vnext_plus237", fixture_name)
        )


@pytest.mark.parametrize(
    ("fixture_name", "message"),
    [
        (
            "repo_work_packet_activation_v237_reject_validation_tests_without_edges.json",
            "List should have at least 1 item",
        ),
        (
            "repo_work_packet_activation_v237_reject_validation_missing_edge_coverage.json",
            "validation plan is not complete across semantic edges",
        ),
    ],
)
def test_v84b_validation_plans_reject_uncovered_semantics(
    fixture_name: str,
    message: str,
) -> None:
    with pytest.raises(ValidationError, match=message):
        RepoWorkPacketValidationEvidencePlan.model_validate(
            _load_fixture("vnext_plus237", fixture_name)
        )


def test_v84b_scope_contract_rejects_lineage_mismatch() -> None:
    with pytest.raises(ValidationError, match="activation package lineage rows must match package"):
        RepoWorkPacketScopeContract.model_validate(
            _load_fixture(
                "vnext_plus237",
                "repo_work_packet_activation_v237_reject_package_lineage_mismatch.json",
            )
        )


def test_v84b_exception_register_rejects_hidden_exceptions() -> None:
    with pytest.raises(ValidationError, match="V84-B exceptions cannot be hidden"):
        RepoWorkPacketActivationExceptionRegister.model_validate(
            _load_fixture(
                "vnext_plus237",
                "repo_work_packet_activation_v237_reject_exception_hidden.json",
            )
        )


def test_v84b_bundle_rejects_unknown_request_refs() -> None:
    scope = _v84b_scope(
        "repo_work_packet_activation_v237_reject_scope_missing_request_ref.json"
    )
    with pytest.raises(ValueError, match="scope contracts must reference released V84-A requests"):
        _validate_reference_bundle_with(scope=scope)


def test_v84b_bundle_rejects_validation_plan_unknown_request_refs() -> None:
    validation_plan = _v84b_validation_plan()
    row = validation_plan.validation_plan_rows[0].model_copy(
        update={"activation_request_refs": ["activation-request:v84a:missing"]}
    )
    validation_plan = validation_plan.model_copy(update={"validation_plan_rows": [row]})

    with pytest.raises(ValueError, match="validation plans must reference released V84-A requests"):
        _validate_reference_bundle_with(validation_plan=validation_plan)


def test_v84b_bundle_rejects_validation_plan_request_scope_mismatch() -> None:
    validation_plan = _v84b_validation_plan()
    row = validation_plan.validation_plan_rows[0].model_copy(
        update={
            "activation_request_refs": ["activation-request:v84a:meta-orchestrator-review"]
        }
    )
    validation_plan = validation_plan.model_copy(update={"validation_plan_rows": [row]})

    with pytest.raises(ValueError, match="validation plan requests must match scope contracts"):
        _validate_reference_bundle_with(validation_plan=validation_plan)


def test_v84b_bundle_rejects_exception_register_unknown_request_refs() -> None:
    exception_register = _v84b_exception_register()
    row = exception_register.exception_register_rows[0].model_copy(
        update={"activation_request_refs": ["activation-request:v84a:missing"]}
    )
    exception_register = exception_register.model_copy(update={"exception_register_rows": [row]})

    with pytest.raises(
        ValueError,
        match="exception registers must reference released V84-A requests",
    ):
        _validate_reference_bundle_with(exception_register=exception_register)


def test_v84b_bundle_rejects_exception_register_request_scope_mismatch() -> None:
    exception_register = _v84b_exception_register()
    row = exception_register.exception_register_rows[0].model_copy(
        update={
            "activation_request_refs": ["activation-request:v84a:meta-orchestrator-review"]
        }
    )
    exception_register = exception_register.model_copy(update={"exception_register_rows": [row]})

    with pytest.raises(ValueError, match="exception register requests must match scope contracts"):
        _validate_reference_bundle_with(exception_register=exception_register)


def test_v84b_bundle_rejects_forbidden_targets_in_scope() -> None:
    scope = _v84b_scope(
        "repo_work_packet_activation_v237_reject_forbidden_target_in_scope.json"
    )
    with pytest.raises(ValueError, match="forbidden targets cannot be included in scope"):
        _validate_reference_bundle_with(scope=scope)
