from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_SINGLE_CASE_EXECUTION_PREFLIGHT_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_RUN_CONTROL_CONTRACT_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_RUN_NON_AUTHORITY_GUARDRAIL_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_RUN_REQUEST_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_TARGET_SELECTION_SCHEMA,
    ProgrambenchLocalMatrixInclusionFamilyCloseoutAlignment,
    ProgrambenchLocalMatrixRevisionReadinessSummary,
    ProgrambenchLocalMatrixRevisionRegistration,
    ProgrambenchSingleCaseExecutionPreflight,
    ProgrambenchSingleCaseRunControlContract,
    ProgrambenchSingleCaseRunNonAuthorityGuardrail,
    ProgrambenchSingleCaseRunRequest,
    ProgrambenchSingleCaseTargetSelection,
    validate_pb_single_case_run_0a_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root(arc: str) -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / arc


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _load_matrix_inclusion_c_rows() -> tuple[
    ProgrambenchLocalMatrixInclusionFamilyCloseoutAlignment,
    ProgrambenchLocalMatrixRevisionRegistration,
    ProgrambenchLocalMatrixRevisionReadinessSummary,
]:
    root = _fixture_root("vnext_plus268")
    return (
        ProgrambenchLocalMatrixInclusionFamilyCloseoutAlignment.model_validate(
            _load_fixture(
                root,
                "programbench_local_matrix_inclusion_family_closeout_alignment_v268_reference.json",
            )
        ),
        ProgrambenchLocalMatrixRevisionRegistration.model_validate(
            _load_fixture(
                root,
                "programbench_local_matrix_revision_registration_v268_reference.json",
            )
        ),
        ProgrambenchLocalMatrixRevisionReadinessSummary.model_validate(
            _load_fixture(
                root,
                "programbench_local_matrix_revision_readiness_summary_v268_reference.json",
            )
        ),
    )


def _load_single_case_run_a_rows() -> tuple[
    ProgrambenchSingleCaseRunRequest,
    ProgrambenchSingleCaseTargetSelection,
    ProgrambenchSingleCaseExecutionPreflight,
    ProgrambenchSingleCaseRunControlContract,
    ProgrambenchSingleCaseRunNonAuthorityGuardrail,
]:
    root = _fixture_root("vnext_plus269")
    return (
        ProgrambenchSingleCaseRunRequest.model_validate(
            _load_fixture(
                root,
                "programbench_single_case_run_request_v269_reference.json",
            )
        ),
        ProgrambenchSingleCaseTargetSelection.model_validate(
            _load_fixture(
                root,
                "programbench_single_case_target_selection_v269_reference.json",
            )
        ),
        ProgrambenchSingleCaseExecutionPreflight.model_validate(
            _load_fixture(
                root,
                "programbench_single_case_execution_preflight_v269_reference.json",
            )
        ),
        ProgrambenchSingleCaseRunControlContract.model_validate(
            _load_fixture(
                root,
                "programbench_single_case_run_control_contract_v269_reference.json",
            )
        ),
        ProgrambenchSingleCaseRunNonAuthorityGuardrail.model_validate(
            _load_fixture(
                root,
                "programbench_single_case_run_non_authority_guardrail_v269_reference.json",
            )
        ),
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_SINGLE_CASE_RUN_REQUEST_SCHEMA,
            "programbench_single_case_run_request.v1.json",
            "programbench_single_case_run_request_v269_reference.json",
            ProgrambenchSingleCaseRunRequest,
        ),
        (
            PROGRAMBENCH_SINGLE_CASE_TARGET_SELECTION_SCHEMA,
            "programbench_single_case_target_selection.v1.json",
            "programbench_single_case_target_selection_v269_reference.json",
            ProgrambenchSingleCaseTargetSelection,
        ),
        (
            PROGRAMBENCH_SINGLE_CASE_EXECUTION_PREFLIGHT_SCHEMA,
            "programbench_single_case_execution_preflight.v1.json",
            "programbench_single_case_execution_preflight_v269_reference.json",
            ProgrambenchSingleCaseExecutionPreflight,
        ),
        (
            PROGRAMBENCH_SINGLE_CASE_RUN_CONTROL_CONTRACT_SCHEMA,
            "programbench_single_case_run_control_contract.v1.json",
            "programbench_single_case_run_control_contract_v269_reference.json",
            ProgrambenchSingleCaseRunControlContract,
        ),
        (
            PROGRAMBENCH_SINGLE_CASE_RUN_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            "programbench_single_case_run_non_authority_guardrail.v1.json",
            "programbench_single_case_run_non_authority_guardrail_v269_reference.json",
            ProgrambenchSingleCaseRunNonAuthorityGuardrail,
        ),
    ],
)
def test_pb_single_case_run_0a_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_fixture(_fixture_root("vnext_plus269"), fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_single_case_run_0a_reference_bundle_binds_matrix_member() -> None:
    matrix_closeout, matrix_registration, matrix_readiness = (
        _load_matrix_inclusion_c_rows()
    )
    request, target, preflight, control, guardrail = _load_single_case_run_a_rows()

    validate_pb_single_case_run_0a_bundle(
        matrix_inclusion_family_closeout=matrix_closeout,
        matrix_revision_registration=matrix_registration,
        matrix_revision_readiness_summary=matrix_readiness,
        run_request=request,
        target_selection=target,
        execution_preflight=preflight,
        run_control_contract=control,
        non_authority_guardrail=guardrail,
    )


def test_pb_single_case_run_0a_rejects_non_included_matrix_target() -> None:
    _, target, _, _, _ = _load_single_case_run_a_rows()

    with pytest.raises(ValidationError, match="included membership"):
        ProgrambenchSingleCaseTargetSelection.model_validate(
            target.model_dump(by_alias=True)
            | {
                "matrix_membership_status": "deferred",
                "target_selection_status": "blocked",
                "target_selection_blocker_refs": [
                    "single-case-blocker:pb-single-case-run-0a:not-included"
                ],
            }
        )


def test_pb_single_case_run_0a_rejects_direct_adapter_route_without_exception() -> None:
    request, _, _, _, _ = _load_single_case_run_a_rows()

    with pytest.raises(ValidationError, match="prior lifecycle relation"):
        ProgrambenchSingleCaseRunRequest.model_validate(
            request.model_dump(by_alias=True)
            | {"target_origin_route": "direct_adapter_case_exception"}
        )


def test_pb_single_case_run_0a_rejects_missing_required_b_witness() -> None:
    _, _, preflight, _, _ = _load_single_case_run_a_rows()

    with pytest.raises(ValidationError, match="B witness requirements"):
        ProgrambenchSingleCaseExecutionPreflight.model_validate(
            preflight.model_dump(by_alias=True)
            | {
                "required_b_witness_refs": [
                    ref
                    for ref in preflight.required_b_witness_refs
                    if ref != "sandbox_instance_ref"
                ]
            }
        )


def test_pb_single_case_run_0a_rejects_current_artifacts_as_future_forbidden() -> None:
    _, _, _, _, guardrail = _load_single_case_run_a_rows()

    with pytest.raises(ValidationError, match="current A artifact kinds"):
        ProgrambenchSingleCaseRunNonAuthorityGuardrail.model_validate(
            guardrail.model_dump(by_alias=True)
            | {
                "forbidden_future_artifact_kinds": sorted(
                    [
                        *guardrail.forbidden_future_artifact_kinds,
                        PROGRAMBENCH_SINGLE_CASE_RUN_REQUEST_SCHEMA,
                    ]
                )
            }
        )


def test_pb_single_case_run_0a_rejects_benchmark_like_result_language() -> None:
    request, _, _, _, _ = _load_single_case_run_a_rows()

    with pytest.raises(ValidationError, match="result or comparison language"):
        ProgrambenchSingleCaseRunRequest.model_validate(
            request.model_dump(by_alias=True)
            | {"limitation_note": "This would be a benchmark score."}
        )


def test_pb_single_case_run_0a_bundle_rejects_hash_drift() -> None:
    matrix_closeout, matrix_registration, matrix_readiness = (
        _load_matrix_inclusion_c_rows()
    )
    request, target, preflight, control, guardrail = _load_single_case_run_a_rows()
    bad_control = control.model_copy(
        update={
            "worker_visible_packet_hash": (
                "sha256:5454545454545454545454545454545454545454545454545454545454545454"
            )
        }
    )

    with pytest.raises(ValueError, match="worker packet hash"):
        validate_pb_single_case_run_0a_bundle(
            matrix_inclusion_family_closeout=matrix_closeout,
            matrix_revision_registration=matrix_registration,
            matrix_revision_readiness_summary=matrix_readiness,
            run_request=request,
            target_selection=target,
            execution_preflight=preflight,
            run_control_contract=bad_control,
            non_authority_guardrail=guardrail,
        )


def test_pb_single_case_run_0a_exports_current_schema() -> None:
    export_schema_main()
    root = _repo_root()

    for schema_path, spec_path in [
        (
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_single_case_run_request.v1.json",
            root / "spec" / "programbench_single_case_run_request.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_single_case_target_selection.v1.json",
            root / "spec" / "programbench_single_case_target_selection.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_single_case_execution_preflight.v1.json",
            root / "spec" / "programbench_single_case_execution_preflight.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_single_case_run_control_contract.v1.json",
            root / "spec" / "programbench_single_case_run_control_contract.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_single_case_run_non_authority_guardrail.v1.json",
            root
            / "spec"
            / "programbench_single_case_run_non_authority_guardrail.schema.json",
        ),
    ]:
        assert json.loads(schema_path.read_text(encoding="utf-8")) == json.loads(
            spec_path.read_text(encoding="utf-8")
        )
