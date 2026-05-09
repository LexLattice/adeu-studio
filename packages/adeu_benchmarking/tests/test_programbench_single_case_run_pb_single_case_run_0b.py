from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_SINGLE_CASE_CANDIDATE_ARTIFACT_CAPTURE_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_EXECUTION_TRACE_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_LIFECYCLE_PROJECTION_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_PROBE_OBSERVATION_BUNDLE_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_WORKER_DISPATCH_SPECIMEN_SCHEMA,
    ProgrambenchLocalMatrixInclusionFamilyCloseoutAlignment,
    ProgrambenchLocalMatrixRevisionReadinessSummary,
    ProgrambenchLocalMatrixRevisionRegistration,
    ProgrambenchSingleCaseCandidateArtifactCapture,
    ProgrambenchSingleCaseExecutionPreflight,
    ProgrambenchSingleCaseExecutionTrace,
    ProgrambenchSingleCaseLifecycleProjection,
    ProgrambenchSingleCaseProbeObservationBundle,
    ProgrambenchSingleCaseRunControlContract,
    ProgrambenchSingleCaseRunNonAuthorityGuardrail,
    ProgrambenchSingleCaseRunRequest,
    ProgrambenchSingleCaseTargetSelection,
    ProgrambenchSingleCaseWorkerDispatchSpecimen,
    validate_pb_single_case_run_0b_bundle,
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
            _load_fixture(root, "programbench_single_case_run_request_v269_reference.json")
        ),
        ProgrambenchSingleCaseTargetSelection.model_validate(
            _load_fixture(root, "programbench_single_case_target_selection_v269_reference.json")
        ),
        ProgrambenchSingleCaseExecutionPreflight.model_validate(
            _load_fixture(root, "programbench_single_case_execution_preflight_v269_reference.json")
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


def _load_single_case_run_b_rows() -> tuple[
    ProgrambenchSingleCaseWorkerDispatchSpecimen,
    ProgrambenchSingleCaseExecutionTrace,
    ProgrambenchSingleCaseProbeObservationBundle,
    ProgrambenchSingleCaseCandidateArtifactCapture,
    ProgrambenchSingleCaseLifecycleProjection,
]:
    root = _fixture_root("vnext_plus270")
    return (
        ProgrambenchSingleCaseWorkerDispatchSpecimen.model_validate(
            _load_fixture(
                root,
                "programbench_single_case_worker_dispatch_specimen_v270_reference.json",
            )
        ),
        ProgrambenchSingleCaseExecutionTrace.model_validate(
            _load_fixture(root, "programbench_single_case_execution_trace_v270_reference.json")
        ),
        ProgrambenchSingleCaseProbeObservationBundle.model_validate(
            _load_fixture(
                root,
                "programbench_single_case_probe_observation_bundle_v270_reference.json",
            )
        ),
        ProgrambenchSingleCaseCandidateArtifactCapture.model_validate(
            _load_fixture(
                root,
                "programbench_single_case_candidate_artifact_capture_v270_reference.json",
            )
        ),
        ProgrambenchSingleCaseLifecycleProjection.model_validate(
            _load_fixture(
                root,
                "programbench_single_case_lifecycle_projection_v270_reference.json",
            )
        ),
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_SINGLE_CASE_WORKER_DISPATCH_SPECIMEN_SCHEMA,
            "programbench_single_case_worker_dispatch_specimen.v1.json",
            "programbench_single_case_worker_dispatch_specimen_v270_reference.json",
            ProgrambenchSingleCaseWorkerDispatchSpecimen,
        ),
        (
            PROGRAMBENCH_SINGLE_CASE_EXECUTION_TRACE_SCHEMA,
            "programbench_single_case_execution_trace.v1.json",
            "programbench_single_case_execution_trace_v270_reference.json",
            ProgrambenchSingleCaseExecutionTrace,
        ),
        (
            PROGRAMBENCH_SINGLE_CASE_PROBE_OBSERVATION_BUNDLE_SCHEMA,
            "programbench_single_case_probe_observation_bundle.v1.json",
            "programbench_single_case_probe_observation_bundle_v270_reference.json",
            ProgrambenchSingleCaseProbeObservationBundle,
        ),
        (
            PROGRAMBENCH_SINGLE_CASE_CANDIDATE_ARTIFACT_CAPTURE_SCHEMA,
            "programbench_single_case_candidate_artifact_capture.v1.json",
            "programbench_single_case_candidate_artifact_capture_v270_reference.json",
            ProgrambenchSingleCaseCandidateArtifactCapture,
        ),
        (
            PROGRAMBENCH_SINGLE_CASE_LIFECYCLE_PROJECTION_SCHEMA,
            "programbench_single_case_lifecycle_projection.v1.json",
            "programbench_single_case_lifecycle_projection_v270_reference.json",
            ProgrambenchSingleCaseLifecycleProjection,
        ),
    ],
)
def test_pb_single_case_run_0b_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    export_schema_main()
    payload = _load_fixture(_fixture_root("vnext_plus270"), fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_single_case_run_0b_reference_bundle_binds_a_controls() -> None:
    matrix_closeout, matrix_registration, matrix_readiness = (
        _load_matrix_inclusion_c_rows()
    )
    request, target, preflight, control, guardrail = _load_single_case_run_a_rows()
    dispatch, trace, probes, capture, projection = _load_single_case_run_b_rows()

    validate_pb_single_case_run_0b_bundle(
        matrix_inclusion_family_closeout=matrix_closeout,
        matrix_revision_registration=matrix_registration,
        matrix_revision_readiness_summary=matrix_readiness,
        run_request=request,
        target_selection=target,
        execution_preflight=preflight,
        run_control_contract=control,
        non_authority_guardrail=guardrail,
        worker_dispatch_specimen=dispatch,
        execution_trace=trace,
        probe_observation_bundle=probes,
        candidate_artifact_capture=capture,
        lifecycle_projection=projection,
    )


def test_pb_single_case_run_0b_rejects_missing_b_dispatch_authority() -> None:
    dispatch, _, _, _, _ = _load_single_case_run_b_rows()

    with pytest.raises(ValidationError, match="lock authority"):
        ProgrambenchSingleCaseWorkerDispatchSpecimen.model_validate(
            dispatch.model_dump(by_alias=True)
            | {"b_slice_dispatch_authority_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS269.md"}
        )


def test_pb_single_case_run_0b_rejects_second_dispatch_specimen() -> None:
    dispatch, _, _, _, _ = _load_single_case_run_b_rows()

    with pytest.raises(ValidationError):
        ProgrambenchSingleCaseWorkerDispatchSpecimen.model_validate(
            dispatch.model_dump(by_alias=True) | {"dispatch_specimen_index": 2}
        )


def test_pb_single_case_run_0b_rejects_shell_shaped_command() -> None:
    _, trace, _, _, _ = _load_single_case_run_b_rows()
    payload = trace.model_dump(by_alias=True)
    payload["command_argv_rows"] = [
        payload["command_argv_rows"][0]
        | {
            "argv": ["bash", "-lc", "python -m local_case_worker"],
        }
    ]

    with pytest.raises(ValidationError, match="shell executable"):
        ProgrambenchSingleCaseExecutionTrace.model_validate(payload)


def test_pb_single_case_run_0b_rejects_shell_path_command() -> None:
    _, trace, _, _, _ = _load_single_case_run_b_rows()
    payload = trace.model_dump(by_alias=True)
    payload["command_argv_rows"] = [
        payload["command_argv_rows"][0] | {"argv": ["/bin/sh", "-c", "echo local"]}
    ]

    with pytest.raises(ValidationError, match="shell executable"):
        ProgrambenchSingleCaseExecutionTrace.model_validate(payload)


def test_pb_single_case_run_0b_rejects_shell_marker_in_argv_token() -> None:
    _, trace, _, _, _ = _load_single_case_run_b_rows()
    payload = trace.model_dump(by_alias=True)
    payload["command_argv_rows"] = [
        payload["command_argv_rows"][0]
        | {"argv": [".venv/bin/python", "-m", "local_case_worker", "out>file"]}
    ]

    with pytest.raises(ValidationError, match="raw shell markers"):
        ProgrambenchSingleCaseExecutionTrace.model_validate(payload)


def test_pb_single_case_run_0b_rejects_capture_before_screening_passes() -> None:
    _, trace, _, capture, _ = _load_single_case_run_b_rows()
    bad_trace = trace.model_copy(
        update={"forbidden_content_screen_verdict": "inconclusive_requires_review"}
    )

    with pytest.raises(ValueError, match="passed forbidden-content screening"):
        validate_pb_single_case_run_0b_bundle(
            matrix_inclusion_family_closeout=_load_matrix_inclusion_c_rows()[0],
            matrix_revision_registration=_load_matrix_inclusion_c_rows()[1],
            matrix_revision_readiness_summary=_load_matrix_inclusion_c_rows()[2],
            run_request=_load_single_case_run_a_rows()[0],
            target_selection=_load_single_case_run_a_rows()[1],
            execution_preflight=_load_single_case_run_a_rows()[2],
            run_control_contract=_load_single_case_run_a_rows()[3],
            non_authority_guardrail=_load_single_case_run_a_rows()[4],
            worker_dispatch_specimen=_load_single_case_run_b_rows()[0],
            execution_trace=bad_trace,
            probe_observation_bundle=_load_single_case_run_b_rows()[2],
            candidate_artifact_capture=capture,
            lifecycle_projection=_load_single_case_run_b_rows()[4],
        )


def test_pb_single_case_run_0b_rejects_artifact_outside_write_scope() -> None:
    capture = _load_single_case_run_b_rows()[3]

    with pytest.raises(ValidationError):
        ProgrambenchSingleCaseCandidateArtifactCapture.model_validate(
            capture.model_dump(by_alias=True)
            | {"inside_write_scope_posture": "outside_released_write_scope"}
        )


def test_pb_single_case_run_0b_rejects_artifact_hash_contradiction() -> None:
    capture = _load_single_case_run_b_rows()[3]
    payload = capture.model_dump(by_alias=True)
    payload["artifact_hash_rows"] = [
        payload["artifact_hash_rows"][0]
        | {
            "artifact_hash": (
                "sha256:6565656565656565656565656565656565656565656565656565656565656565"
            )
        }
    ]

    with pytest.raises(ValidationError, match="generated artifact hashes"):
        ProgrambenchSingleCaseCandidateArtifactCapture.model_validate(payload)


def test_pb_single_case_run_0b_rejects_materialization_hash_not_from_trace() -> None:
    matrix_closeout, matrix_registration, matrix_readiness = (
        _load_matrix_inclusion_c_rows()
    )
    request, target, preflight, control, guardrail = _load_single_case_run_a_rows()
    dispatch, trace, probes, capture, projection = _load_single_case_run_b_rows()
    bad_capture = capture.model_copy(
        update={
            "materialization_input_hash": (
                "sha256:6363636363636363636363636363636363636363636363636363636363636363"
            )
        }
    )

    with pytest.raises(ValueError, match="captured output"):
        validate_pb_single_case_run_0b_bundle(
            matrix_inclusion_family_closeout=matrix_closeout,
            matrix_revision_registration=matrix_registration,
            matrix_revision_readiness_summary=matrix_readiness,
            run_request=request,
            target_selection=target,
            execution_preflight=preflight,
            run_control_contract=control,
            non_authority_guardrail=guardrail,
            worker_dispatch_specimen=dispatch,
            execution_trace=trace,
            probe_observation_bundle=probes,
            candidate_artifact_capture=bad_capture,
            lifecycle_projection=projection,
        )


def test_pb_single_case_run_0b_rejects_dispatch_hash_drift() -> None:
    matrix_closeout, matrix_registration, matrix_readiness = (
        _load_matrix_inclusion_c_rows()
    )
    request, target, preflight, control, guardrail = _load_single_case_run_a_rows()
    dispatch, trace, probes, capture, projection = _load_single_case_run_b_rows()
    bad_dispatch = dispatch.model_copy(
        update={
            "worker_visible_packet_hash": (
                "sha256:6464646464646464646464646464646464646464646464646464646464646464"
            )
        }
    )

    with pytest.raises(ValueError, match="worker_visible_packet_hash"):
        validate_pb_single_case_run_0b_bundle(
            matrix_inclusion_family_closeout=matrix_closeout,
            matrix_revision_registration=matrix_registration,
            matrix_revision_readiness_summary=matrix_readiness,
            run_request=request,
            target_selection=target,
            execution_preflight=preflight,
            run_control_contract=control,
            non_authority_guardrail=guardrail,
            worker_dispatch_specimen=bad_dispatch,
            execution_trace=trace,
            probe_observation_bundle=probes,
            candidate_artifact_capture=capture,
            lifecycle_projection=projection,
        )


def test_pb_single_case_run_0b_rejects_projection_gap_in_reference_bundle() -> None:
    matrix_closeout, matrix_registration, matrix_readiness = (
        _load_matrix_inclusion_c_rows()
    )
    request, target, preflight, control, guardrail = _load_single_case_run_a_rows()
    dispatch, trace, probes, capture, projection = _load_single_case_run_b_rows()
    bad_projection = projection.model_copy(
        update={"projection_gap_refs": ["projection-gap:pb-single-case-run-0b:missing"]}
    )

    with pytest.raises(ValueError, match="projection gaps"):
        validate_pb_single_case_run_0b_bundle(
            matrix_inclusion_family_closeout=matrix_closeout,
            matrix_revision_registration=matrix_registration,
            matrix_revision_readiness_summary=matrix_readiness,
            run_request=request,
            target_selection=target,
            execution_preflight=preflight,
            run_control_contract=control,
            non_authority_guardrail=guardrail,
            worker_dispatch_specimen=dispatch,
            execution_trace=trace,
            probe_observation_bundle=probes,
            candidate_artifact_capture=capture,
            lifecycle_projection=bad_projection,
        )


def test_pb_single_case_run_0b_exports_current_schema() -> None:
    export_schema_main()
    root = _repo_root()

    for schema_path, spec_path in [
        (
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_single_case_worker_dispatch_specimen.v1.json",
            root
            / "spec"
            / "programbench_single_case_worker_dispatch_specimen.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_single_case_execution_trace.v1.json",
            root / "spec" / "programbench_single_case_execution_trace.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_single_case_probe_observation_bundle.v1.json",
            root
            / "spec"
            / "programbench_single_case_probe_observation_bundle.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_single_case_candidate_artifact_capture.v1.json",
            root
            / "spec"
            / "programbench_single_case_candidate_artifact_capture.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_single_case_lifecycle_projection.v1.json",
            root / "spec" / "programbench_single_case_lifecycle_projection.schema.json",
        ),
    ]:
        assert json.loads(schema_path.read_text(encoding="utf-8")) == json.loads(
            spec_path.read_text(encoding="utf-8")
        )
