from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_LOCAL_TRIAL_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    PROGRAMBENCH_LOCAL_TRIAL_OBSERVATION_SUMMARY_SCHEMA,
    PROGRAMBENCH_LOCAL_TRIAL_OUTCOME_AUDIT_SCHEMA,
    PROGRAMBENCH_LOCAL_TRIAL_REMAND_DECISION_SCHEMA,
    ProgrambenchLocalReconstructionTrialDocket,
    ProgrambenchLocalTrialCandidateArtifactSnapshot,
    ProgrambenchLocalTrialExecutionCapture,
    ProgrambenchLocalTrialExecutionRunbook,
    ProgrambenchLocalTrialFamilyCloseoutAlignment,
    ProgrambenchLocalTrialLifecycleProjection,
    ProgrambenchLocalTrialNonAuthorityGuardrail,
    ProgrambenchLocalTrialObservationSummary,
    ProgrambenchLocalTrialOutcomeAudit,
    ProgrambenchLocalTrialRemandDecision,
    ProgrambenchLocalTrialSandboxReadinessReview,
    ProgrambenchLocalTrialWorkerDispatchRecord,
    ProgrambenchReconstructionAttemptCandidateMaterialization,
    ProgrambenchReconstructionAttemptOutputCapture,
    ProgrambenchReconstructionAttemptSandboxApplicationTrace,
    ProgrambenchReconstructionAttemptWorkerInvocationRecord,
    validate_pb_trial_0c_closeout_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root_trial_a() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus254"


def _fixture_root_trial_b() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus255"


def _fixture_root_trial_c() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus256"


def _fixture_root_attempt_b() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus252"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_trial_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_trial_a(), name)


def _load_trial_b_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_trial_b(), name)


def _load_trial_c_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_trial_c(), name)


def _load_attempt_b_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_attempt_b(), name)


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
            PROGRAMBENCH_LOCAL_TRIAL_OUTCOME_AUDIT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_trial_outcome_audit.v1.json",
            root / "spec" / "programbench_local_trial_outcome_audit.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_TRIAL_OBSERVATION_SUMMARY_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_trial_observation_summary.v1.json",
            root / "spec" / "programbench_local_trial_observation_summary.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_TRIAL_REMAND_DECISION_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_trial_remand_decision.v1.json",
            root / "spec" / "programbench_local_trial_remand_decision.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_TRIAL_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_trial_family_closeout_alignment.v1.json",
            root / "spec" / "programbench_local_trial_family_closeout_alignment.schema.json",
        ),
    ]


def _load_trial_a_rows() -> tuple[
    ProgrambenchLocalReconstructionTrialDocket,
    ProgrambenchLocalTrialExecutionRunbook,
    ProgrambenchLocalTrialSandboxReadinessReview,
    ProgrambenchLocalTrialNonAuthorityGuardrail,
]:
    return (
        ProgrambenchLocalReconstructionTrialDocket.model_validate(
            _load_trial_a_fixture(
                "programbench_local_reconstruction_trial_docket_v254_reference.json"
            )
        ),
        ProgrambenchLocalTrialExecutionRunbook.model_validate(
            _load_trial_a_fixture("programbench_local_trial_execution_runbook_v254_reference.json")
        ),
        ProgrambenchLocalTrialSandboxReadinessReview.model_validate(
            _load_trial_a_fixture(
                "programbench_local_trial_sandbox_readiness_review_v254_reference.json"
            )
        ),
        ProgrambenchLocalTrialNonAuthorityGuardrail.model_validate(
            _load_trial_a_fixture(
                "programbench_local_trial_non_authority_guardrail_v254_reference.json"
            )
        ),
    )


def _load_trial_b_rows() -> tuple[
    ProgrambenchLocalTrialWorkerDispatchRecord,
    ProgrambenchLocalTrialExecutionCapture,
    ProgrambenchLocalTrialCandidateArtifactSnapshot,
    ProgrambenchLocalTrialLifecycleProjection,
]:
    return (
        ProgrambenchLocalTrialWorkerDispatchRecord.model_validate(
            _load_trial_b_fixture(
                "programbench_local_trial_worker_dispatch_record_v255_reference.json"
            )
        ),
        ProgrambenchLocalTrialExecutionCapture.model_validate(
            _load_trial_b_fixture("programbench_local_trial_execution_capture_v255_reference.json")
        ),
        ProgrambenchLocalTrialCandidateArtifactSnapshot.model_validate(
            _load_trial_b_fixture(
                "programbench_local_trial_candidate_artifact_snapshot_v255_reference.json"
            )
        ),
        ProgrambenchLocalTrialLifecycleProjection.model_validate(
            _load_trial_b_fixture(
                "programbench_local_trial_lifecycle_projection_v255_reference.json"
            )
        ),
    )


def _load_trial_c_rows() -> tuple[
    ProgrambenchLocalTrialOutcomeAudit,
    ProgrambenchLocalTrialObservationSummary,
    ProgrambenchLocalTrialRemandDecision,
    ProgrambenchLocalTrialFamilyCloseoutAlignment,
]:
    return (
        ProgrambenchLocalTrialOutcomeAudit.model_validate(
            _load_trial_c_fixture("programbench_local_trial_outcome_audit_v256_reference.json")
        ),
        ProgrambenchLocalTrialObservationSummary.model_validate(
            _load_trial_c_fixture(
                "programbench_local_trial_observation_summary_v256_reference.json"
            )
        ),
        ProgrambenchLocalTrialRemandDecision.model_validate(
            _load_trial_c_fixture("programbench_local_trial_remand_decision_v256_reference.json")
        ),
        ProgrambenchLocalTrialFamilyCloseoutAlignment.model_validate(
            _load_trial_c_fixture(
                "programbench_local_trial_family_closeout_alignment_v256_reference.json"
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


def _validate_pb_trial_0c_closeout_bundle(
    *,
    trial_docket: ProgrambenchLocalReconstructionTrialDocket,
    execution_runbook: ProgrambenchLocalTrialExecutionRunbook,
    sandbox_readiness_review: ProgrambenchLocalTrialSandboxReadinessReview,
    trial_guardrail: ProgrambenchLocalTrialNonAuthorityGuardrail,
    worker_dispatch_record: ProgrambenchLocalTrialWorkerDispatchRecord,
    execution_capture: ProgrambenchLocalTrialExecutionCapture,
    candidate_artifact_snapshot: ProgrambenchLocalTrialCandidateArtifactSnapshot,
    lifecycle_projection: ProgrambenchLocalTrialLifecycleProjection,
    outcome_audit: ProgrambenchLocalTrialOutcomeAudit,
    observation_summary: ProgrambenchLocalTrialObservationSummary,
    remand_decision: ProgrambenchLocalTrialRemandDecision,
    family_closeout: ProgrambenchLocalTrialFamilyCloseoutAlignment,
) -> None:
    (
        released_attempt_worker_invocation,
        released_attempt_output_capture,
        released_attempt_candidate_materialization,
        released_attempt_sandbox_trace,
    ) = _load_attempt_b_rows()

    validate_pb_trial_0c_closeout_bundle(
        trial_docket=trial_docket,
        execution_runbook=execution_runbook,
        sandbox_readiness_review=sandbox_readiness_review,
        trial_guardrail=trial_guardrail,
        released_attempt_worker_invocation=released_attempt_worker_invocation,
        released_attempt_output_capture=released_attempt_output_capture,
        released_attempt_candidate_materialization=released_attempt_candidate_materialization,
        released_attempt_sandbox_trace=released_attempt_sandbox_trace,
        worker_dispatch_record=worker_dispatch_record,
        execution_capture=execution_capture,
        candidate_artifact_snapshot=candidate_artifact_snapshot,
        lifecycle_projection=lifecycle_projection,
        outcome_audit=outcome_audit,
        observation_summary=observation_summary,
        remand_decision=remand_decision,
        family_closeout=family_closeout,
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_LOCAL_TRIAL_OUTCOME_AUDIT_SCHEMA,
            "programbench_local_trial_outcome_audit.v1.json",
            "programbench_local_trial_outcome_audit_v256_reference.json",
            ProgrambenchLocalTrialOutcomeAudit,
        ),
        (
            PROGRAMBENCH_LOCAL_TRIAL_OBSERVATION_SUMMARY_SCHEMA,
            "programbench_local_trial_observation_summary.v1.json",
            "programbench_local_trial_observation_summary_v256_reference.json",
            ProgrambenchLocalTrialObservationSummary,
        ),
        (
            PROGRAMBENCH_LOCAL_TRIAL_REMAND_DECISION_SCHEMA,
            "programbench_local_trial_remand_decision.v1.json",
            "programbench_local_trial_remand_decision_v256_reference.json",
            ProgrambenchLocalTrialRemandDecision,
        ),
        (
            PROGRAMBENCH_LOCAL_TRIAL_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            "programbench_local_trial_family_closeout_alignment.v1.json",
            "programbench_local_trial_family_closeout_alignment_v256_reference.json",
            ProgrambenchLocalTrialFamilyCloseoutAlignment,
        ),
    ],
)
def test_pb_trial_0c_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_trial_c_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_trial_0c_reference_bundle_closes_single_local_trial() -> None:
    (
        trial_docket,
        execution_runbook,
        sandbox_readiness_review,
        trial_guardrail,
    ) = _load_trial_a_rows()
    (
        worker_dispatch_record,
        execution_capture,
        candidate_artifact_snapshot,
        lifecycle_projection,
    ) = _load_trial_b_rows()
    (
        outcome_audit,
        observation_summary,
        remand_decision,
        family_closeout,
    ) = _load_trial_c_rows()

    _validate_pb_trial_0c_closeout_bundle(
        trial_docket=trial_docket,
        execution_runbook=execution_runbook,
        sandbox_readiness_review=sandbox_readiness_review,
        trial_guardrail=trial_guardrail,
        worker_dispatch_record=worker_dispatch_record,
        execution_capture=execution_capture,
        candidate_artifact_snapshot=candidate_artifact_snapshot,
        lifecycle_projection=lifecycle_projection,
        outcome_audit=outcome_audit,
        observation_summary=observation_summary,
        remand_decision=remand_decision,
        family_closeout=family_closeout,
    )

    assert outcome_audit.local_outcome_posture == "trial_locally_accepted"
    assert observation_summary.single_trial_scope_posture == (
        "single_local_trial_only_no_comparison"
    )
    assert remand_decision.retry_authority_posture == "no_retry_authority_granted_by_pb_trial_0c"
    assert family_closeout.closed_slice_refs == [
        "PB-TRIAL-0-A",
        "PB-TRIAL-0-B",
        "PB-TRIAL-0-C",
    ]


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_local_trial_v256_reject_local_acceptance_with_blockers.json",
            ProgrambenchLocalTrialOutcomeAudit,
        ),
        (
            (
                "programbench_local_trial_v256_reject_local_acceptance_without_"
                "lifecycle_projection_validation.json"
            ),
            ProgrambenchLocalTrialOutcomeAudit,
        ),
        (
            "programbench_local_trial_v256_reject_comparative_observation_summary.json",
            ProgrambenchLocalTrialObservationSummary,
        ),
        (
            "programbench_local_trial_v256_reject_model_ranking_summary.json",
            ProgrambenchLocalTrialObservationSummary,
        ),
        (
            "programbench_local_trial_v256_reject_hidden_test_remand_source.json",
            ProgrambenchLocalTrialRemandDecision,
        ),
        (
            "programbench_local_trial_v256_reject_retry_authority.json",
            ProgrambenchLocalTrialRemandDecision,
        ),
        (
            "programbench_local_trial_v256_reject_future_family_selection.json",
            ProgrambenchLocalTrialFamilyCloseoutAlignment,
        ),
    ],
)
def test_pb_trial_0c_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_trial_c_fixture(fixture_name))


def test_pb_trial_0c_rejects_outcome_without_lifecycle_projection() -> None:
    (
        trial_docket,
        execution_runbook,
        sandbox_readiness_review,
        trial_guardrail,
    ) = _load_trial_a_rows()
    (
        worker_dispatch_record,
        execution_capture,
        candidate_artifact_snapshot,
        lifecycle_projection,
    ) = _load_trial_b_rows()
    (
        outcome_audit,
        observation_summary,
        remand_decision,
        family_closeout,
    ) = _load_trial_c_rows()
    drifted_audit = outcome_audit.model_copy(
        update={"trial_lifecycle_projection_ref": "trial-lifecycle-projection:pb-trial-0b:stale"}
    )

    with pytest.raises(ValueError, match="lifecycle projection"):
        _validate_pb_trial_0c_closeout_bundle(
            trial_docket=trial_docket,
            execution_runbook=execution_runbook,
            sandbox_readiness_review=sandbox_readiness_review,
            trial_guardrail=trial_guardrail,
            worker_dispatch_record=worker_dispatch_record,
            execution_capture=execution_capture,
            candidate_artifact_snapshot=candidate_artifact_snapshot,
            lifecycle_projection=lifecycle_projection,
            outcome_audit=drifted_audit,
            observation_summary=observation_summary,
            remand_decision=remand_decision,
            family_closeout=family_closeout,
        )


def test_pb_trial_0c_revalidates_pb_trial_0b_lineage() -> None:
    (
        trial_docket,
        execution_runbook,
        sandbox_readiness_review,
        trial_guardrail,
    ) = _load_trial_a_rows()
    (
        worker_dispatch_record,
        execution_capture,
        candidate_artifact_snapshot,
        lifecycle_projection,
    ) = _load_trial_b_rows()
    (
        outcome_audit,
        observation_summary,
        remand_decision,
        family_closeout,
    ) = _load_trial_c_rows()
    drifted_dispatch = worker_dispatch_record.model_copy(
        update={"trial_runbook_ref": "trial-runbook:pb-trial-0a:stale"}
    )

    with pytest.raises(ValueError, match="worker dispatch must reference trial runbook"):
        _validate_pb_trial_0c_closeout_bundle(
            trial_docket=trial_docket,
            execution_runbook=execution_runbook,
            sandbox_readiness_review=sandbox_readiness_review,
            trial_guardrail=trial_guardrail,
            worker_dispatch_record=drifted_dispatch,
            execution_capture=execution_capture,
            candidate_artifact_snapshot=candidate_artifact_snapshot,
            lifecycle_projection=lifecycle_projection,
            outcome_audit=outcome_audit,
            observation_summary=observation_summary,
            remand_decision=remand_decision,
            family_closeout=family_closeout,
        )


def test_pb_trial_0c_rejects_local_acceptance_without_snapshot_inside_scope() -> None:
    (
        trial_docket,
        execution_runbook,
        sandbox_readiness_review,
        trial_guardrail,
    ) = _load_trial_a_rows()
    (
        worker_dispatch_record,
        execution_capture,
        candidate_artifact_snapshot,
        lifecycle_projection,
    ) = _load_trial_b_rows()
    (
        outcome_audit,
        observation_summary,
        remand_decision,
        family_closeout,
    ) = _load_trial_c_rows()
    drifted_snapshot = candidate_artifact_snapshot.model_copy(
        update={"snapshot_inside_write_scope": False}
    )

    with pytest.raises(ValueError, match="inside released write scope"):
        _validate_pb_trial_0c_closeout_bundle(
            trial_docket=trial_docket,
            execution_runbook=execution_runbook,
            sandbox_readiness_review=sandbox_readiness_review,
            trial_guardrail=trial_guardrail,
            worker_dispatch_record=worker_dispatch_record,
            execution_capture=execution_capture,
            candidate_artifact_snapshot=drifted_snapshot,
            lifecycle_projection=lifecycle_projection,
            outcome_audit=outcome_audit,
            observation_summary=observation_summary,
            remand_decision=remand_decision,
            family_closeout=family_closeout,
        )


def test_pb_trial_0c_rejects_observation_hash_drift() -> None:
    (
        trial_docket,
        execution_runbook,
        sandbox_readiness_review,
        trial_guardrail,
    ) = _load_trial_a_rows()
    (
        worker_dispatch_record,
        execution_capture,
        candidate_artifact_snapshot,
        lifecycle_projection,
    ) = _load_trial_b_rows()
    (
        outcome_audit,
        observation_summary,
        remand_decision,
        family_closeout,
    ) = _load_trial_c_rows()
    drifted_summary = observation_summary.model_copy(
        update={
            "observed_candidate_snapshot_hash": (
                "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
            )
        }
    )

    with pytest.raises(ValueError, match="candidate snapshot hash"):
        _validate_pb_trial_0c_closeout_bundle(
            trial_docket=trial_docket,
            execution_runbook=execution_runbook,
            sandbox_readiness_review=sandbox_readiness_review,
            trial_guardrail=trial_guardrail,
            worker_dispatch_record=worker_dispatch_record,
            execution_capture=execution_capture,
            candidate_artifact_snapshot=candidate_artifact_snapshot,
            lifecycle_projection=lifecycle_projection,
            outcome_audit=outcome_audit,
            observation_summary=drifted_summary,
            remand_decision=remand_decision,
            family_closeout=family_closeout,
        )


def test_pb_trial_0c_schema_exports_mirror_root_spec_files() -> None:
    export_schema_main()

    for expected_schema, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))

        assert authoritative["properties"]["schema"]["const"] == expected_schema
        assert authoritative == mirror

        serialized = json.dumps(authoritative, sort_keys=True)
        assert _repo_root().as_posix() not in serialized
        assert not _WINDOWS_ABSOLUTE_PATH_RE.search(serialized)
