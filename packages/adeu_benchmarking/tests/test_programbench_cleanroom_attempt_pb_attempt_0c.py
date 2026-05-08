from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_REMAND_QUEUE_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_RESULT_REVIEW_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_WORKBENCH_EVIDENCE_EXPORT_SCHEMA,
    ProgrambenchReconstructionAttemptCandidateMaterialization,
    ProgrambenchReconstructionAttemptDispatchPreflight,
    ProgrambenchReconstructionAttemptFamilyCloseoutAlignment,
    ProgrambenchReconstructionAttemptNonAuthorityGuardrail,
    ProgrambenchReconstructionAttemptOutputCapture,
    ProgrambenchReconstructionAttemptRemandQueue,
    ProgrambenchReconstructionAttemptRequest,
    ProgrambenchReconstructionAttemptResultReview,
    ProgrambenchReconstructionAttemptSandboxApplicationTrace,
    ProgrambenchReconstructionAttemptWorkbenchEvidenceExport,
    ProgrambenchReconstructionAttemptWorkerInputPacket,
    ProgrambenchReconstructionAttemptWorkerInvocationRecord,
    ProgrambenchReconstructionCandidateArtifactManifest,
    ProgrambenchReconstructionEquivalenceAudit,
    ProgrambenchReconstructionLocalRunTrace,
    ProgrambenchReconstructionProbeResultLog,
    ProgrambenchReconstructionRemandCorrectionRecord,
    ProgrambenchReconstructionResultSummary,
    ProgrambenchReconstructionRunBudget,
    ProgrambenchReconstructionSandboxPolicy,
    ProgrambenchReconstructionWorkbenchFamilyCloseoutAlignment,
    validate_pb_attempt_0c_closeout_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root_recon_a() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus248"


def _fixture_root_recon_c() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus250"


def _fixture_root_recon_b() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus249"


def _fixture_root_attempt_a() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus251"


def _fixture_root_attempt_b() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus252"


def _fixture_root_attempt_c() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus253"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_recon_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_recon_a(), name)


def _load_recon_c_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_recon_c(), name)


def _load_recon_b_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_recon_b(), name)


def _load_attempt_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_attempt_a(), name)


def _load_attempt_b_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_attempt_b(), name)


def _load_attempt_c_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_attempt_c(), name)


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (_repo_root() / "packages" / "adeu_benchmarking" / "schema" / schema_filename).read_text(
            encoding="utf-8"
        )
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _schema_pairs() -> list[tuple[str, Path, Path]]:
    root = _repo_root()
    return [
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_WORKBENCH_EVIDENCE_EXPORT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_attempt_workbench_evidence_export.v1.json",
            root
            / "spec"
            / "programbench_reconstruction_attempt_workbench_evidence_export.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_RESULT_REVIEW_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_attempt_result_review.v1.json",
            root / "spec" / "programbench_reconstruction_attempt_result_review.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_REMAND_QUEUE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_attempt_remand_queue.v1.json",
            root / "spec" / "programbench_reconstruction_attempt_remand_queue.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_attempt_family_closeout_alignment.v1.json",
            root
            / "spec"
            / "programbench_reconstruction_attempt_family_closeout_alignment.schema.json",
        ),
    ]


def _load_attempt_a_rows() -> tuple[
    ProgrambenchReconstructionAttemptRequest,
    ProgrambenchReconstructionAttemptWorkerInputPacket,
    ProgrambenchReconstructionAttemptDispatchPreflight,
    ProgrambenchReconstructionAttemptNonAuthorityGuardrail,
]:
    return (
        ProgrambenchReconstructionAttemptRequest.model_validate(
            _load_attempt_a_fixture(
                "programbench_reconstruction_attempt_request_v251_reference.json"
            )
        ),
        ProgrambenchReconstructionAttemptWorkerInputPacket.model_validate(
            _load_attempt_a_fixture(
                "programbench_reconstruction_attempt_worker_input_packet_v251_reference.json"
            )
        ),
        ProgrambenchReconstructionAttemptDispatchPreflight.model_validate(
            _load_attempt_a_fixture(
                "programbench_reconstruction_attempt_dispatch_preflight_v251_reference.json"
            )
        ),
        ProgrambenchReconstructionAttemptNonAuthorityGuardrail.model_validate(
            _load_attempt_a_fixture(
                "programbench_reconstruction_attempt_non_authority_guardrail_v251_reference.json"
            )
        ),
    )


def _load_attempt_b_rows() -> tuple[
    ProgrambenchReconstructionAttemptWorkerInvocationRecord,
    ProgrambenchReconstructionAttemptOutputCapture,
    ProgrambenchReconstructionAttemptCandidateMaterialization,
    ProgrambenchReconstructionAttemptSandboxApplicationTrace,
]:
    return (
        ProgrambenchReconstructionAttemptWorkerInvocationRecord.model_validate(
            _load_attempt_b_fixture(
                "programbench_reconstruction_attempt_worker_invocation_record_v252_reference.json"
            )
        ),
        ProgrambenchReconstructionAttemptOutputCapture.model_validate(
            _load_attempt_b_fixture(
                "programbench_reconstruction_attempt_output_capture_v252_reference.json"
            )
        ),
        ProgrambenchReconstructionAttemptCandidateMaterialization.model_validate(
            _load_attempt_b_fixture(
                "programbench_reconstruction_attempt_candidate_materialization_v252_reference.json"
            )
        ),
        ProgrambenchReconstructionAttemptSandboxApplicationTrace.model_validate(
            _load_attempt_b_fixture(
                "programbench_reconstruction_attempt_sandbox_application_trace_v252_reference.json"
            )
        ),
    )


def _load_recon_b_rows() -> tuple[
    ProgrambenchReconstructionCandidateArtifactManifest,
    list[ProgrambenchReconstructionLocalRunTrace],
    ProgrambenchReconstructionProbeResultLog,
    list[ProgrambenchReconstructionRemandCorrectionRecord],
]:
    return (
        ProgrambenchReconstructionCandidateArtifactManifest.model_validate(
            _load_recon_b_fixture(
                "programbench_reconstruction_candidate_artifact_manifest_v249_reference.json"
            )
        ),
        [
            ProgrambenchReconstructionLocalRunTrace.model_validate(
                _load_recon_b_fixture(
                    "programbench_reconstruction_local_run_trace_v249_reference.json"
                )
            )
        ],
        ProgrambenchReconstructionProbeResultLog.model_validate(
            _load_recon_b_fixture(
                "programbench_reconstruction_probe_result_log_v249_reference.json"
            )
        ),
        [
            ProgrambenchReconstructionRemandCorrectionRecord.model_validate(
                _load_recon_b_fixture(
                    "programbench_reconstruction_remand_correction_record_v249_reference.json"
                )
            )
        ],
    )


def _load_attempt_c_rows() -> tuple[
    ProgrambenchReconstructionAttemptWorkbenchEvidenceExport,
    ProgrambenchReconstructionAttemptResultReview,
    ProgrambenchReconstructionAttemptRemandQueue,
    ProgrambenchReconstructionAttemptFamilyCloseoutAlignment,
]:
    return (
        ProgrambenchReconstructionAttemptWorkbenchEvidenceExport.model_validate(
            _load_attempt_c_fixture(
                "programbench_reconstruction_attempt_workbench_evidence_export_v253_reference.json"
            )
        ),
        ProgrambenchReconstructionAttemptResultReview.model_validate(
            _load_attempt_c_fixture(
                "programbench_reconstruction_attempt_result_review_v253_reference.json"
            )
        ),
        ProgrambenchReconstructionAttemptRemandQueue.model_validate(
            _load_attempt_c_fixture(
                "programbench_reconstruction_attempt_remand_queue_v253_reference.json"
            )
        ),
        ProgrambenchReconstructionAttemptFamilyCloseoutAlignment.model_validate(
            _load_attempt_c_fixture(
                "programbench_reconstruction_attempt_family_closeout_alignment_v253_reference.json"
            )
        ),
    )


def _load_recon_c_rows() -> tuple[
    ProgrambenchReconstructionEquivalenceAudit,
    ProgrambenchReconstructionResultSummary,
    ProgrambenchReconstructionWorkbenchFamilyCloseoutAlignment,
]:
    return (
        ProgrambenchReconstructionEquivalenceAudit.model_validate(
            _load_recon_c_fixture(
                "programbench_reconstruction_equivalence_audit_v250_reference.json"
            )
        ),
        ProgrambenchReconstructionResultSummary.model_validate(
            _load_recon_c_fixture("programbench_reconstruction_result_summary_v250_reference.json")
        ),
        ProgrambenchReconstructionWorkbenchFamilyCloseoutAlignment.model_validate(
            _load_recon_c_fixture(
                "programbench_reconstruction_workbench_family_closeout_alignment_v250_reference.json"
            )
        ),
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_WORKBENCH_EVIDENCE_EXPORT_SCHEMA,
            "programbench_reconstruction_attempt_workbench_evidence_export.v1.json",
            "programbench_reconstruction_attempt_workbench_evidence_export_v253_reference.json",
            ProgrambenchReconstructionAttemptWorkbenchEvidenceExport,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_RESULT_REVIEW_SCHEMA,
            "programbench_reconstruction_attempt_result_review.v1.json",
            "programbench_reconstruction_attempt_result_review_v253_reference.json",
            ProgrambenchReconstructionAttemptResultReview,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_REMAND_QUEUE_SCHEMA,
            "programbench_reconstruction_attempt_remand_queue.v1.json",
            "programbench_reconstruction_attempt_remand_queue_v253_reference.json",
            ProgrambenchReconstructionAttemptRemandQueue,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            "programbench_reconstruction_attempt_family_closeout_alignment.v1.json",
            "programbench_reconstruction_attempt_family_closeout_alignment_v253_reference.json",
            ProgrambenchReconstructionAttemptFamilyCloseoutAlignment,
        ),
    ],
)
def test_pb_attempt_0c_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_attempt_c_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_attempt_0c_reference_bundle_records_remand_pressure_only() -> None:
    attempt_request, worker_input_packet, dispatch_preflight, guardrail = _load_attempt_a_rows()
    sandbox_policy = ProgrambenchReconstructionSandboxPolicy.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_sandbox_policy_v248_reference.json")
    )
    run_budget = ProgrambenchReconstructionRunBudget.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_run_budget_v248_reference.json")
    )
    worker_invocation, output_capture, candidate_materialization, sandbox_trace = (
        _load_attempt_b_rows()
    )
    candidate_manifest, local_run_traces, probe_log, remand_records = _load_recon_b_rows()
    workbench_audit, workbench_summary, workbench_closeout = _load_recon_c_rows()
    workbench_export, attempt_review, remand_queue, family_closeout = _load_attempt_c_rows()

    validate_pb_attempt_0c_closeout_bundle(
        attempt_request=attempt_request,
        worker_input_packet=worker_input_packet,
        dispatch_preflight=dispatch_preflight,
        guardrail=guardrail,
        sandbox_policy=sandbox_policy,
        run_budget=run_budget,
        worker_invocation_record=worker_invocation,
        output_capture=output_capture,
        candidate_materialization=candidate_materialization,
        sandbox_application_trace=sandbox_trace,
        workbench_candidate_artifact_manifest=candidate_manifest,
        workbench_local_run_traces=local_run_traces,
        workbench_probe_result_log=probe_log,
        workbench_remand_correction_records=remand_records,
        workbench_equivalence_audit=workbench_audit,
        workbench_result_summary=workbench_summary,
        workbench_family_closeout=workbench_closeout,
        workbench_evidence_export=workbench_export,
        attempt_result_review=attempt_review,
        remand_queue=remand_queue,
        family_closeout=family_closeout,
    )

    assert workbench_export.export_validation_posture == "valid"
    assert attempt_review.local_attempt_posture == "attempt_remand_required"
    assert remand_queue.queue_authority_posture == "remand_queue_pressure_only_no_retry_authority"
    assert family_closeout.closed_family_ref == "PB-ATTEMPT-0"


def test_pb_attempt_0c_rejects_export_without_validator_results_for_every_mapped_row() -> None:
    payload = _load_attempt_c_fixture(
        "programbench_reconstruction_attempt_workbench_evidence_export_v253_reference.json"
    )
    payload["pb_recon_validation_result_refs"] = [
        "pb-recon-validation:pb-attempt-0c:result-summary"
    ]

    with pytest.raises(ValidationError, match="for every mapped workbench evidence row"):
        ProgrambenchReconstructionAttemptWorkbenchEvidenceExport.model_validate(payload)


def test_pb_attempt_0c_local_acceptance_requires_accepted_workbench_summary() -> None:
    attempt_request, worker_input_packet, dispatch_preflight, guardrail = _load_attempt_a_rows()
    sandbox_policy = ProgrambenchReconstructionSandboxPolicy.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_sandbox_policy_v248_reference.json")
    )
    run_budget = ProgrambenchReconstructionRunBudget.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_run_budget_v248_reference.json")
    )
    worker_invocation, output_capture, candidate_materialization, sandbox_trace = (
        _load_attempt_b_rows()
    )
    candidate_manifest, local_run_traces, probe_log, remand_records = _load_recon_b_rows()
    workbench_audit, workbench_summary, workbench_closeout = _load_recon_c_rows()
    workbench_export, _attempt_review, remand_queue, family_closeout = _load_attempt_c_rows()
    premature_review = ProgrambenchReconstructionAttemptResultReview.model_validate(
        _load_attempt_c_fixture(
            "programbench_reconstruction_attempt_v253_reject_local_acceptance_without_accepted_workbench_summary.json"
        )
    )

    with pytest.raises(ValueError, match="PB-RECON local_accepted"):
        validate_pb_attempt_0c_closeout_bundle(
            attempt_request=attempt_request,
            worker_input_packet=worker_input_packet,
            dispatch_preflight=dispatch_preflight,
            guardrail=guardrail,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            worker_invocation_record=worker_invocation,
            output_capture=output_capture,
            candidate_materialization=candidate_materialization,
            sandbox_application_trace=sandbox_trace,
            workbench_candidate_artifact_manifest=candidate_manifest,
            workbench_local_run_traces=local_run_traces,
            workbench_probe_result_log=probe_log,
            workbench_remand_correction_records=remand_records,
            workbench_equivalence_audit=workbench_audit,
            workbench_result_summary=workbench_summary,
            workbench_family_closeout=workbench_closeout,
            workbench_evidence_export=workbench_export,
            attempt_result_review=premature_review,
            remand_queue=remand_queue,
            family_closeout=family_closeout,
        )


def test_pb_attempt_0c_rejects_export_rows_not_released_by_workbench_summary() -> None:
    attempt_request, worker_input_packet, dispatch_preflight, guardrail = _load_attempt_a_rows()
    sandbox_policy = ProgrambenchReconstructionSandboxPolicy.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_sandbox_policy_v248_reference.json")
    )
    run_budget = ProgrambenchReconstructionRunBudget.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_run_budget_v248_reference.json")
    )
    worker_invocation, output_capture, candidate_materialization, sandbox_trace = (
        _load_attempt_b_rows()
    )
    candidate_manifest, local_run_traces, probe_log, remand_records = _load_recon_b_rows()
    workbench_audit, workbench_summary, workbench_closeout = _load_recon_c_rows()
    workbench_export, attempt_review, remand_queue, family_closeout = _load_attempt_c_rows()
    drifted_export = workbench_export.model_copy(
        update={"exported_local_run_trace_refs": ["local-run:pb-recon-0b:unreleased"]}
    )

    with pytest.raises(ValueError, match="released PB-RECON local runs"):
        validate_pb_attempt_0c_closeout_bundle(
            attempt_request=attempt_request,
            worker_input_packet=worker_input_packet,
            dispatch_preflight=dispatch_preflight,
            guardrail=guardrail,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            worker_invocation_record=worker_invocation,
            output_capture=output_capture,
            candidate_materialization=candidate_materialization,
            sandbox_application_trace=sandbox_trace,
            workbench_candidate_artifact_manifest=candidate_manifest,
            workbench_local_run_traces=local_run_traces,
            workbench_probe_result_log=probe_log,
            workbench_remand_correction_records=remand_records,
            workbench_equivalence_audit=workbench_audit,
            workbench_result_summary=workbench_summary,
            workbench_family_closeout=workbench_closeout,
            workbench_evidence_export=drifted_export,
            attempt_result_review=attempt_review,
            remand_queue=remand_queue,
            family_closeout=family_closeout,
        )


def test_pb_attempt_0c_preserves_contamination_blocked_workbench_posture() -> None:
    attempt_request, worker_input_packet, dispatch_preflight, guardrail = _load_attempt_a_rows()
    sandbox_policy = ProgrambenchReconstructionSandboxPolicy.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_sandbox_policy_v248_reference.json")
    )
    run_budget = ProgrambenchReconstructionRunBudget.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_run_budget_v248_reference.json")
    )
    worker_invocation, output_capture, candidate_materialization, sandbox_trace = (
        _load_attempt_b_rows()
    )
    candidate_manifest, local_run_traces, probe_log, remand_records = _load_recon_b_rows()
    workbench_audit, workbench_summary, workbench_closeout = _load_recon_c_rows()
    workbench_export, attempt_review, remand_queue, family_closeout = _load_attempt_c_rows()
    contaminated_summary = workbench_summary.model_copy(
        update={
            "contamination_refs": ["contamination:pb-recon-0c:hidden-source-summary"],
            "result_posture": "blocked_by_contamination",
        }
    )

    with pytest.raises(ValueError, match="contamination attempt posture"):
        validate_pb_attempt_0c_closeout_bundle(
            attempt_request=attempt_request,
            worker_input_packet=worker_input_packet,
            dispatch_preflight=dispatch_preflight,
            guardrail=guardrail,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            worker_invocation_record=worker_invocation,
            output_capture=output_capture,
            candidate_materialization=candidate_materialization,
            sandbox_application_trace=sandbox_trace,
            workbench_candidate_artifact_manifest=candidate_manifest,
            workbench_local_run_traces=local_run_traces,
            workbench_probe_result_log=probe_log,
            workbench_remand_correction_records=remand_records,
            workbench_equivalence_audit=workbench_audit,
            workbench_result_summary=contaminated_summary,
            workbench_family_closeout=workbench_closeout,
            workbench_evidence_export=workbench_export,
            attempt_result_review=attempt_review,
            remand_queue=remand_queue,
            family_closeout=family_closeout,
        )


def test_pb_attempt_0c_allows_export_gap_only_as_blocked_attempt_posture() -> None:
    attempt_request, worker_input_packet, dispatch_preflight, guardrail = _load_attempt_a_rows()
    sandbox_policy = ProgrambenchReconstructionSandboxPolicy.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_sandbox_policy_v248_reference.json")
    )
    run_budget = ProgrambenchReconstructionRunBudget.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_run_budget_v248_reference.json")
    )
    worker_invocation, output_capture, candidate_materialization, sandbox_trace = (
        _load_attempt_b_rows()
    )
    candidate_manifest, local_run_traces, probe_log, remand_records = _load_recon_b_rows()
    workbench_audit, workbench_summary, workbench_closeout = _load_recon_c_rows()
    workbench_export, attempt_review, remand_queue, family_closeout = _load_attempt_c_rows()
    blocked_export = workbench_export.model_copy(
        update={"export_validation_posture": "blocked_by_export_gap"}
    )
    blocked_review = attempt_review.model_copy(
        update={
            "carried_blocker_refs": ["workbench-evidence-export:pb-attempt-0c:reference"],
            "local_attempt_posture": "attempt_blocked_by_export_gap",
        }
    )

    validate_pb_attempt_0c_closeout_bundle(
        attempt_request=attempt_request,
        worker_input_packet=worker_input_packet,
        dispatch_preflight=dispatch_preflight,
        guardrail=guardrail,
        sandbox_policy=sandbox_policy,
        run_budget=run_budget,
        worker_invocation_record=worker_invocation,
        output_capture=output_capture,
        candidate_materialization=candidate_materialization,
        sandbox_application_trace=sandbox_trace,
        workbench_candidate_artifact_manifest=candidate_manifest,
        workbench_local_run_traces=local_run_traces,
        workbench_probe_result_log=probe_log,
        workbench_remand_correction_records=remand_records,
        workbench_equivalence_audit=workbench_audit,
        workbench_result_summary=workbench_summary,
        workbench_family_closeout=workbench_closeout,
        workbench_evidence_export=blocked_export,
        attempt_result_review=blocked_review,
        remand_queue=remand_queue,
        family_closeout=family_closeout,
    )


def test_pb_attempt_0c_remand_queue_rejects_nonlocal_source_refs() -> None:
    attempt_request, worker_input_packet, dispatch_preflight, guardrail = _load_attempt_a_rows()
    sandbox_policy = ProgrambenchReconstructionSandboxPolicy.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_sandbox_policy_v248_reference.json")
    )
    run_budget = ProgrambenchReconstructionRunBudget.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_run_budget_v248_reference.json")
    )
    worker_invocation, output_capture, candidate_materialization, sandbox_trace = (
        _load_attempt_b_rows()
    )
    candidate_manifest, local_run_traces, probe_log, remand_records = _load_recon_b_rows()
    workbench_audit, workbench_summary, workbench_closeout = _load_recon_c_rows()
    workbench_export, attempt_review, remand_queue, family_closeout = _load_attempt_c_rows()
    bad_row = remand_queue.remand_queue_rows[0].model_copy(
        update={"source_evidence_refs": ["hidden-test:forbidden"]}
    )
    bad_queue = remand_queue.model_copy(update={"remand_queue_rows": [bad_row]})

    with pytest.raises(ValueError, match="local attempt/workbench evidence refs"):
        validate_pb_attempt_0c_closeout_bundle(
            attempt_request=attempt_request,
            worker_input_packet=worker_input_packet,
            dispatch_preflight=dispatch_preflight,
            guardrail=guardrail,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            worker_invocation_record=worker_invocation,
            output_capture=output_capture,
            candidate_materialization=candidate_materialization,
            sandbox_application_trace=sandbox_trace,
            workbench_candidate_artifact_manifest=candidate_manifest,
            workbench_local_run_traces=local_run_traces,
            workbench_probe_result_log=probe_log,
            workbench_remand_correction_records=remand_records,
            workbench_equivalence_audit=workbench_audit,
            workbench_result_summary=workbench_summary,
            workbench_family_closeout=workbench_closeout,
            workbench_evidence_export=workbench_export,
            attempt_result_review=attempt_review,
            remand_queue=bad_queue,
            family_closeout=family_closeout,
        )


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_reconstruction_attempt_v253_reject_export_without_pb_recon_validator_binding.json",
            ProgrambenchReconstructionAttemptWorkbenchEvidenceExport,
        ),
        (
            "programbench_reconstruction_attempt_v253_reject_hidden_test_remand_source.json",
            ProgrambenchReconstructionAttemptRemandQueue,
        ),
        (
            "programbench_reconstruction_attempt_v253_reject_benchmark_truth_result.json",
            ProgrambenchReconstructionAttemptResultReview,
        ),
        (
            "programbench_reconstruction_attempt_v253_reject_future_family_selection.json",
            ProgrambenchReconstructionAttemptFamilyCloseoutAlignment,
        ),
    ],
)
def test_pb_attempt_0c_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_attempt_c_fixture(fixture_name))


def test_pb_attempt_0c_schema_exports_mirror_root_spec_files() -> None:
    export_schema_main()

    for expected_schema, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))

        assert authoritative["properties"]["schema"]["const"] == expected_schema
        assert authoritative == mirror

        serialized = json.dumps(authoritative, sort_keys=True)
        assert _repo_root().as_posix() not in serialized
        assert not _WINDOWS_ABSOLUTE_PATH_RE.search(serialized)
