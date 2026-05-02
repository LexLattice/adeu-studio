from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CONTROLLED_EXECUTION_EXCEPTION_REGISTER_SCHEMA,
    REPO_EXECUTION_EFFECT_MONITORING_CONTRACT_SCHEMA,
    REPO_EXECUTION_RUN_PLAN_SCHEMA,
    REPO_TOOL_INVOCATION_PLAN_SCHEMA,
    RepoControlledExecutionExceptionRegister,
    RepoControlledExecutionNonExecutionGuardrail,
    RepoControlledExecutionReviewRequest,
    RepoControlledExecutionSourceIndex,
    RepoExecutionEffectMonitoringContract,
    RepoExecutionRunPlan,
    RepoToolInvocationPlan,
    derive_v79b_controlled_execution_review_bundle,
    validate_v79b_controlled_execution_review_bundle,
)
from adeu_repo_description.controlled_execution_review import RepoExecutionRunPlanRow
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


def _validate_reference_bundle_with(
    *,
    run_plan: RepoExecutionRunPlan | None = None,
    tool_plan: RepoToolInvocationPlan | None = None,
    monitoring: RepoExecutionEffectMonitoringContract | None = None,
    exceptions: RepoControlledExecutionExceptionRegister | None = None,
) -> None:
    validate_v79b_controlled_execution_review_bundle(
        controlled_execution_source_index=_v79a_source_index(),
        controlled_execution_review_request=_v79a_request(),
        controlled_execution_non_execution_guardrail=_v79a_guardrail(),
        execution_run_plan=run_plan or _run_plan(),
        tool_invocation_plan=tool_plan or _tool_plan(),
        execution_effect_monitoring_contract=monitoring or _monitoring(),
        controlled_execution_exception_register=exceptions or _exceptions(),
    )


def test_v222_reference_bundle_validates() -> None:
    run_plan = _run_plan()
    tool_plan = _tool_plan()
    monitoring = _monitoring()
    exceptions = _exceptions()

    assert run_plan.schema == REPO_EXECUTION_RUN_PLAN_SCHEMA
    assert tool_plan.schema == REPO_TOOL_INVOCATION_PLAN_SCHEMA
    assert monitoring.schema == REPO_EXECUTION_EFFECT_MONITORING_CONTRACT_SCHEMA
    assert exceptions.schema == REPO_CONTROLLED_EXECUTION_EXCEPTION_REGISTER_SCHEMA
    assert {row.run_execution_status for row in run_plan.run_plan_rows} == {
        "no_run_performed_by_v79"
    }
    assert {row.tool_invocation_status for row in tool_plan.tool_invocation_plan_rows} == {
        "no_tool_invocation_performed_by_v79"
    }
    effect_postures = {
        row.effect_observation_posture for row in monitoring.effect_monitoring_contract_rows
    }
    assert effect_postures == {
        "no_effect_observed_by_v79"
    }
    assert "blocking" in {row.exception_posture for row in exceptions.exception_rows}

    _validate_reference_bundle_with(
        run_plan=run_plan,
        tool_plan=tool_plan,
        monitoring=monitoring,
        exceptions=exceptions,
    )


def test_v222_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_execution_run_plan.v1.json").validate(
        _load_fixture("vnext_plus222", "repo_execution_run_plan_v222_reference.json")
    )
    _schema_validator("repo_tool_invocation_plan.v1.json").validate(
        _load_fixture("vnext_plus222", "repo_tool_invocation_plan_v222_reference.json")
    )
    _schema_validator("repo_execution_effect_monitoring_contract.v1.json").validate(
        _load_fixture(
            "vnext_plus222",
            "repo_execution_effect_monitoring_contract_v222_reference.json",
        )
    )
    _schema_validator("repo_controlled_execution_exception_register.v1.json").validate(
        _load_fixture(
            "vnext_plus222",
            "repo_controlled_execution_exception_register_v222_reference.json",
        )
    )


def test_v222_derivation_helper_matches_reference_fixtures() -> None:
    (
        _source_index,
        _request,
        _guardrail,
        run_plan,
        tool_plan,
        monitoring,
        exceptions,
    ) = derive_v79b_controlled_execution_review_bundle(repo_root=_repo_root())

    assert run_plan.model_dump(mode="json") == _load_fixture(
        "vnext_plus222",
        "repo_execution_run_plan_v222_reference.json",
    )
    assert tool_plan.model_dump(mode="json") == _load_fixture(
        "vnext_plus222",
        "repo_tool_invocation_plan_v222_reference.json",
    )
    assert monitoring.model_dump(mode="json") == _load_fixture(
        "vnext_plus222",
        "repo_execution_effect_monitoring_contract_v222_reference.json",
    )
    assert exceptions.model_dump(mode="json") == _load_fixture(
        "vnext_plus222",
        "repo_controlled_execution_exception_register_v222_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_controlled_execution_v222_reject_run_command_execution_claim.json",
            RepoExecutionRunPlan,
            "V79-B run plans must not perform runs",
        ),
        (
            "repo_controlled_execution_v222_reject_run_glob_target.json",
            RepoExecutionRunPlan,
            "may not contain glob target boundaries",
        ),
        (
            "repo_controlled_execution_v222_reject_target_mutation_authority.json",
            RepoExecutionRunPlan,
            "may not carry controlled execution action",
        ),
        (
            "repo_controlled_execution_v222_reject_tool_invocation_claim.json",
            RepoToolInvocationPlan,
            "V79-B tool plans must not invoke tools",
        ),
        (
            "repo_controlled_execution_v222_reject_tool_global_permission.json",
            RepoToolInvocationPlan,
            "tool-invocation plans may not claim global tool permission",
        ),
        (
            "repo_controlled_execution_v222_reject_monitoring_observed_effect.json",
            RepoExecutionEffectMonitoringContract,
            "observed effects require prior authorized source evidence",
        ),
        (
            "repo_controlled_execution_v222_reject_telemetry_success.json",
            RepoExecutionEffectMonitoringContract,
            "may not carry controlled execution action",
        ),
        (
            "repo_controlled_execution_v222_reject_rollback_verification.json",
            RepoExecutionEffectMonitoringContract,
            "may not carry controlled execution action",
        ),
        (
            "repo_controlled_execution_v222_reject_operator_confirmation_authorization.json",
            RepoExecutionEffectMonitoringContract,
            "non_authorization_guardrail must mention",
        ),
        (
            "repo_controlled_execution_v222_reject_exception_resolved_by_prose.json",
            RepoControlledExecutionExceptionRegister,
            "controlled execution exceptions cannot be resolved by prose",
        ),
        (
            "repo_controlled_execution_v222_reject_product_pressure_execution_ready.json",
            RepoControlledExecutionExceptionRegister,
            "product/external exceptions must remain blocked or deferred",
        ),
        (
            "repo_controlled_execution_v222_reject_local_command_output_authority.json",
            RepoControlledExecutionExceptionRegister,
            "local command output cannot be authority evidence",
        ),
    ],
)
def test_v222_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoExecutionRunPlan
        | RepoToolInvocationPlan
        | RepoExecutionEffectMonitoringContract
        | RepoControlledExecutionExceptionRegister
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus222", fixture_name))


def test_v222_bundle_rejects_unknown_v79a_request_ref() -> None:
    run_plan = RepoExecutionRunPlan.model_validate(
        _load_fixture(
            "vnext_plus222",
            "repo_controlled_execution_v222_reject_run_unknown_request_ref.json",
        )
    )

    with pytest.raises(ValueError, match="run plan request refs must be known"):
        _validate_reference_bundle_with(run_plan=run_plan)


def test_v222_run_plan_allows_external_endpoint_targets() -> None:
    row_data = _load_fixture(
        "vnext_plus222",
        "repo_execution_run_plan_v222_reference.json",
    )["run_plan_rows"][0]
    row_data["target_resolution_kind"] = "external_endpoint_ref"
    row_data["target_boundary_refs"] = [
        "https://example.test/controlled-execution-review?dry_run=true"
    ]

    row = RepoExecutionRunPlanRow.model_validate(row_data)

    assert row.target_resolution_kind == "external_endpoint_ref"
    assert row.target_boundary_refs == [
        "https://example.test/controlled-execution-review?dry_run=true"
    ]


def test_v222_monitoring_rejects_confirmation_candidate_mismatch() -> None:
    monitoring = _load_fixture(
        "vnext_plus222",
        "repo_execution_effect_monitoring_contract_v222_reference.json",
    )
    monitoring["effect_monitoring_contract_rows"][0][
        "operator_confirmation_requirement_rows"
    ][0]["candidate_ref"] = "adeu:v79:other-candidate"

    with pytest.raises(ValidationError, match="monitoring confirmation rows must match candidate"):
        RepoExecutionEffectMonitoringContract.model_validate(monitoring)


def test_v222_bundle_rejects_run_plan_tool_candidate_mismatch() -> None:
    tool_plan = _tool_plan()
    tool_row = tool_plan.tool_invocation_plan_rows[0].model_copy(
        update={"candidate_ref": "adeu:v79:other-candidate"}
    )
    mismatched_tool_plan = tool_plan.model_copy(
        update={"tool_invocation_plan_rows": [tool_row]}
    )

    with pytest.raises(ValueError, match="run plan tool-plan refs must match candidate"):
        _validate_reference_bundle_with(tool_plan=mismatched_tool_plan)


def test_v222_bundle_rejects_exception_candidate_mismatch() -> None:
    exceptions = _exceptions()
    exception_row = exceptions.exception_rows[0].model_copy(
        update={"candidate_ref": "adeu:v79:other-candidate"}
    )
    mismatched_exceptions = exceptions.model_copy(
        update={
            "exception_rows": [
                exception_row,
                *exceptions.exception_rows[1:],
            ]
        }
    )

    with pytest.raises(ValueError, match="exception request refs must match candidate"):
        _validate_reference_bundle_with(exceptions=mismatched_exceptions)
