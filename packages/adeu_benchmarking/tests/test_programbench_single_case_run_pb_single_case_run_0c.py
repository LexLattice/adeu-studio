from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_SINGLE_CASE_LOCAL_OUTCOME_AUDIT_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_REMAND_OR_ACCEPTANCE_DECISION_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_RUN_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_RUN_HANDOFF_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_RUN_OBSERVATION_SUMMARY_SCHEMA,
    ProgrambenchLocalMatrixInclusionFamilyCloseoutAlignment,
    ProgrambenchLocalMatrixRevisionReadinessSummary,
    ProgrambenchLocalMatrixRevisionRegistration,
    ProgrambenchSingleCaseCandidateArtifactCapture,
    ProgrambenchSingleCaseExecutionPreflight,
    ProgrambenchSingleCaseExecutionTrace,
    ProgrambenchSingleCaseLifecycleProjection,
    ProgrambenchSingleCaseLocalOutcomeAudit,
    ProgrambenchSingleCaseProbeObservationBundle,
    ProgrambenchSingleCaseRemandOrAcceptanceDecision,
    ProgrambenchSingleCaseRunControlContract,
    ProgrambenchSingleCaseRunFamilyCloseoutAlignment,
    ProgrambenchSingleCaseRunHandoff,
    ProgrambenchSingleCaseRunNonAuthorityGuardrail,
    ProgrambenchSingleCaseRunObservationSummary,
    ProgrambenchSingleCaseRunRequest,
    ProgrambenchSingleCaseTargetSelection,
    ProgrambenchSingleCaseWorkerDispatchSpecimen,
    validate_pb_single_case_run_0c_bundle,
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
        (_repo_root() / "packages" / "adeu_benchmarking" / "schema" / schema_filename).read_text(
            encoding="utf-8"
        )
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


def _load_single_case_run_c_rows() -> tuple[
    ProgrambenchSingleCaseLocalOutcomeAudit,
    ProgrambenchSingleCaseRunObservationSummary,
    ProgrambenchSingleCaseRemandOrAcceptanceDecision,
    ProgrambenchSingleCaseRunHandoff,
    ProgrambenchSingleCaseRunFamilyCloseoutAlignment,
]:
    root = _fixture_root("vnext_plus271")
    return (
        ProgrambenchSingleCaseLocalOutcomeAudit.model_validate(
            _load_fixture(
                root,
                "programbench_single_case_local_outcome_audit_v271_reference.json",
            )
        ),
        ProgrambenchSingleCaseRunObservationSummary.model_validate(
            _load_fixture(
                root,
                "programbench_single_case_run_observation_summary_v271_reference.json",
            )
        ),
        ProgrambenchSingleCaseRemandOrAcceptanceDecision.model_validate(
            _load_fixture(
                root,
                "programbench_single_case_remand_or_acceptance_decision_v271_reference.json",
            )
        ),
        ProgrambenchSingleCaseRunHandoff.model_validate(
            _load_fixture(root, "programbench_single_case_run_handoff_v271_reference.json")
        ),
        ProgrambenchSingleCaseRunFamilyCloseoutAlignment.model_validate(
            _load_fixture(
                root,
                "programbench_single_case_run_family_closeout_alignment_v271_reference.json",
            )
        ),
    )


def _validate_reference_bundle(
    *,
    local_outcome_audit: ProgrambenchSingleCaseLocalOutcomeAudit | None = None,
    observation_summary: ProgrambenchSingleCaseRunObservationSummary | None = None,
    remand_or_acceptance_decision: ProgrambenchSingleCaseRemandOrAcceptanceDecision | None = None,
    handoff: ProgrambenchSingleCaseRunHandoff | None = None,
    family_closeout: ProgrambenchSingleCaseRunFamilyCloseoutAlignment | None = None,
    probe_observation_bundle: ProgrambenchSingleCaseProbeObservationBundle | None = None,
    lifecycle_projection: ProgrambenchSingleCaseLifecycleProjection | None = None,
) -> None:
    matrix_closeout, matrix_registration, matrix_readiness = _load_matrix_inclusion_c_rows()
    request, target, preflight, control, guardrail = _load_single_case_run_a_rows()
    dispatch, trace, probes, capture, projection = _load_single_case_run_b_rows()
    audit, summary, decision, handoff_row, closeout = _load_single_case_run_c_rows()
    validate_pb_single_case_run_0c_bundle(
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
        probe_observation_bundle=probe_observation_bundle or probes,
        candidate_artifact_capture=capture,
        lifecycle_projection=lifecycle_projection or projection,
        local_outcome_audit=local_outcome_audit or audit,
        observation_summary=observation_summary or summary,
        remand_or_acceptance_decision=remand_or_acceptance_decision or decision,
        handoff=handoff or handoff_row,
        family_closeout=family_closeout or closeout,
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_SINGLE_CASE_LOCAL_OUTCOME_AUDIT_SCHEMA,
            "programbench_single_case_local_outcome_audit.v1.json",
            "programbench_single_case_local_outcome_audit_v271_reference.json",
            ProgrambenchSingleCaseLocalOutcomeAudit,
        ),
        (
            PROGRAMBENCH_SINGLE_CASE_RUN_OBSERVATION_SUMMARY_SCHEMA,
            "programbench_single_case_run_observation_summary.v1.json",
            "programbench_single_case_run_observation_summary_v271_reference.json",
            ProgrambenchSingleCaseRunObservationSummary,
        ),
        (
            PROGRAMBENCH_SINGLE_CASE_REMAND_OR_ACCEPTANCE_DECISION_SCHEMA,
            "programbench_single_case_remand_or_acceptance_decision.v1.json",
            "programbench_single_case_remand_or_acceptance_decision_v271_reference.json",
            ProgrambenchSingleCaseRemandOrAcceptanceDecision,
        ),
        (
            PROGRAMBENCH_SINGLE_CASE_RUN_HANDOFF_SCHEMA,
            "programbench_single_case_run_handoff.v1.json",
            "programbench_single_case_run_handoff_v271_reference.json",
            ProgrambenchSingleCaseRunHandoff,
        ),
        (
            PROGRAMBENCH_SINGLE_CASE_RUN_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            "programbench_single_case_run_family_closeout_alignment.v1.json",
            "programbench_single_case_run_family_closeout_alignment_v271_reference.json",
            ProgrambenchSingleCaseRunFamilyCloseoutAlignment,
        ),
    ],
)
def test_pb_single_case_run_0c_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    export_schema_main()
    payload = _load_fixture(_fixture_root("vnext_plus271"), fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_single_case_run_0c_reference_bundle_binds_a_and_b_evidence() -> None:
    _validate_reference_bundle()


def test_pb_single_case_run_0c_rejects_local_acceptance_with_failed_probe() -> None:
    audit = _load_single_case_run_c_rows()[0].model_copy(update={"positive_probe_status": "failed"})

    with pytest.raises(ValueError, match="positive_probe_status"):
        _validate_reference_bundle(local_outcome_audit=audit)


def test_pb_single_case_run_0c_rejects_failed_probe_bundle_for_acceptance() -> None:
    probes = _load_single_case_run_b_rows()[2]
    payload = probes.model_dump(by_alias=True)
    payload["probe_observation_rows"] = [
        payload["probe_observation_rows"][0] | {"probe_result_status": "failed"},
        payload["probe_observation_rows"][1],
    ]
    failed_probes = ProgrambenchSingleCaseProbeObservationBundle.model_validate(payload)

    with pytest.raises(ValueError, match="declared local probes"):
        _validate_reference_bundle(probe_observation_bundle=failed_probes)


def test_pb_single_case_run_0c_rejects_projection_gap_for_acceptance() -> None:
    projection = _load_single_case_run_b_rows()[4].model_copy(
        update={"projection_gap_refs": ["projection-gap:pb-single-case-run-0c:missing"]}
    )

    with pytest.raises(ValueError, match="projection gaps"):
        _validate_reference_bundle(lifecycle_projection=projection)


def test_pb_single_case_run_0c_rejects_blocked_posture_without_matching_blocker() -> None:
    audit = _load_single_case_run_c_rows()[0]
    payload = audit.model_dump(by_alias=True)
    payload.update(
        {
            "local_outcome_posture": "single_case_blocked_by_contamination",
            "output_capture_status": "blocked_by_output_gap",
            "output_capture_blocker_refs": ["output-blocker:pb-single-case-run-0c:001"],
        }
    )

    with pytest.raises(ValidationError, match="contamination_audit_status"):
        ProgrambenchSingleCaseLocalOutcomeAudit.model_validate(payload)


def test_pb_single_case_run_0c_rejects_artifact_gap_without_artifact_blocker() -> None:
    audit = _load_single_case_run_c_rows()[0]
    payload = audit.model_dump(by_alias=True)
    payload.update(
        {
            "candidate_artifact_capture_status": "missing",
            "candidate_artifact_inside_write_scope_posture": "not_applicable_missing_capture",
            "local_outcome_posture": "single_case_blocked_by_artifact_capture_gap",
        }
    )

    with pytest.raises(ValidationError, match="artifact_capture_blocker_refs"):
        ProgrambenchSingleCaseLocalOutcomeAudit.model_validate(payload)


@pytest.mark.parametrize(
    "limitation_note",
    [
        "This is a success rate statement.",
        "This is an official-like result statement.",
        "This claims hidden-test equivalence.",
    ],
)
def test_pb_single_case_run_0c_rejects_benchmark_language_in_summary(
    limitation_note: str,
) -> None:
    summary = _load_single_case_run_c_rows()[1]

    with pytest.raises(ValidationError, match="benchmark-like"):
        ProgrambenchSingleCaseRunObservationSummary.model_validate(
            summary.model_dump(by_alias=True) | {"limitation_note": limitation_note}
        )


def test_pb_single_case_run_0c_rejects_remand_pressure_on_local_acceptance() -> None:
    decision = _load_single_case_run_c_rows()[2]
    payload = decision.model_dump(by_alias=True)
    payload["remand_reason_rows"] = [
        {
            "limitation_note": "Local evidence gap creates pressure only.",
            "remand_reason_ref": "remand-reason:pb-single-case-run-0c:001",
            "remand_scope_posture": "pressure_only_requires_later_retry_or_trial_governance",
            "remand_source_kind": "local_evidence_inconclusive",
        }
    ]

    with pytest.raises(ValidationError, match="local acceptance cannot carry remand"):
        ProgrambenchSingleCaseRemandOrAcceptanceDecision.model_validate(payload)


def test_pb_single_case_run_0c_rejects_handoff_pressure_for_acceptance() -> None:
    handoff = _load_single_case_run_c_rows()[3].model_copy(
        update={"handoff_pressure_kind": "future_retry_governance_review"}
    )

    with pytest.raises(ValueError, match="local acceptance handoff"):
        _validate_reference_bundle(handoff=handoff)


def test_pb_single_case_run_0c_rejects_incomplete_family_closeout() -> None:
    closeout = _load_single_case_run_c_rows()[4]
    payload = closeout.model_dump(by_alias=True)
    payload["closed_slices"] = ["PB-SINGLE-CASE-RUN-0-A", "PB-SINGLE-CASE-RUN-0-C"]

    with pytest.raises(ValidationError, match="close exactly A, B, and C"):
        ProgrambenchSingleCaseRunFamilyCloseoutAlignment.model_validate(payload)


def test_pb_single_case_run_0c_exports_current_schema() -> None:
    export_schema_main()
    root = _repo_root()

    for schema_path, spec_path in [
        (
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_single_case_local_outcome_audit.v1.json",
            root / "spec" / "programbench_single_case_local_outcome_audit.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_single_case_run_observation_summary.v1.json",
            root / "spec" / "programbench_single_case_run_observation_summary.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_single_case_remand_or_acceptance_decision.v1.json",
            root / "spec" / "programbench_single_case_remand_or_acceptance_decision.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_single_case_run_handoff.v1.json",
            root / "spec" / "programbench_single_case_run_handoff.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_single_case_run_family_closeout_alignment.v1.json",
            root / "spec" / "programbench_single_case_run_family_closeout_alignment.schema.json",
        ),
    ]:
        assert json.loads(schema_path.read_text(encoding="utf-8")) == json.loads(
            spec_path.read_text(encoding="utf-8")
        )
