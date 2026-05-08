from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_LOCAL_TRIAL_CANDIDATE_ARTIFACT_SNAPSHOT_SCHEMA,
    PROGRAMBENCH_LOCAL_TRIAL_EXECUTION_CAPTURE_SCHEMA,
    PROGRAMBENCH_LOCAL_TRIAL_LIFECYCLE_PROJECTION_SCHEMA,
    PROGRAMBENCH_LOCAL_TRIAL_WORKER_DISPATCH_RECORD_SCHEMA,
    ProgrambenchLocalReconstructionTrialDocket,
    ProgrambenchLocalTrialCandidateArtifactSnapshot,
    ProgrambenchLocalTrialExecutionCapture,
    ProgrambenchLocalTrialExecutionRunbook,
    ProgrambenchLocalTrialLifecycleProjection,
    ProgrambenchLocalTrialNonAuthorityGuardrail,
    ProgrambenchLocalTrialSandboxReadinessReview,
    ProgrambenchLocalTrialWorkerDispatchRecord,
    ProgrambenchReconstructionAttemptCandidateMaterialization,
    ProgrambenchReconstructionAttemptOutputCapture,
    ProgrambenchReconstructionAttemptSandboxApplicationTrace,
    ProgrambenchReconstructionAttemptWorkerInvocationRecord,
    validate_pb_trial_0b_execution_bundle,
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
            PROGRAMBENCH_LOCAL_TRIAL_WORKER_DISPATCH_RECORD_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_trial_worker_dispatch_record.v1.json",
            root / "spec" / "programbench_local_trial_worker_dispatch_record.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_TRIAL_EXECUTION_CAPTURE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_trial_execution_capture.v1.json",
            root / "spec" / "programbench_local_trial_execution_capture.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_TRIAL_CANDIDATE_ARTIFACT_SNAPSHOT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_trial_candidate_artifact_snapshot.v1.json",
            root
            / "spec"
            / "programbench_local_trial_candidate_artifact_snapshot.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_TRIAL_LIFECYCLE_PROJECTION_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_trial_lifecycle_projection.v1.json",
            root / "spec" / "programbench_local_trial_lifecycle_projection.schema.json",
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


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_LOCAL_TRIAL_WORKER_DISPATCH_RECORD_SCHEMA,
            "programbench_local_trial_worker_dispatch_record.v1.json",
            "programbench_local_trial_worker_dispatch_record_v255_reference.json",
            ProgrambenchLocalTrialWorkerDispatchRecord,
        ),
        (
            PROGRAMBENCH_LOCAL_TRIAL_EXECUTION_CAPTURE_SCHEMA,
            "programbench_local_trial_execution_capture.v1.json",
            "programbench_local_trial_execution_capture_v255_reference.json",
            ProgrambenchLocalTrialExecutionCapture,
        ),
        (
            PROGRAMBENCH_LOCAL_TRIAL_CANDIDATE_ARTIFACT_SNAPSHOT_SCHEMA,
            "programbench_local_trial_candidate_artifact_snapshot.v1.json",
            "programbench_local_trial_candidate_artifact_snapshot_v255_reference.json",
            ProgrambenchLocalTrialCandidateArtifactSnapshot,
        ),
        (
            PROGRAMBENCH_LOCAL_TRIAL_LIFECYCLE_PROJECTION_SCHEMA,
            "programbench_local_trial_lifecycle_projection.v1.json",
            "programbench_local_trial_lifecycle_projection_v255_reference.json",
            ProgrambenchLocalTrialLifecycleProjection,
        ),
    ],
)
def test_pb_trial_0b_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_trial_b_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_trial_0b_reference_bundle_records_one_local_specimen() -> None:
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
        released_attempt_worker_invocation,
        released_attempt_output_capture,
        released_attempt_candidate_materialization,
        released_attempt_sandbox_trace,
    ) = _load_attempt_b_rows()

    validate_pb_trial_0b_execution_bundle(
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
    )

    assert worker_dispatch_record.dispatch_index == 1
    assert worker_dispatch_record.dispatch_authority_ref == (
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS255.md"
    )
    assert execution_capture.forbidden_content_screen_verdict == "passed"
    assert candidate_artifact_snapshot.snapshot_inside_write_scope is True
    assert lifecycle_projection.new_evidence_law_posture == (
        "no_new_evidence_law_defined_by_pb_trial_0b"
    )


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_local_trial_v255_reject_dispatch_missing_b_lock_authority.json",
            ProgrambenchLocalTrialWorkerDispatchRecord,
        ),
        (
            "programbench_local_trial_v255_reject_hidden_test_access.json",
            ProgrambenchLocalTrialWorkerDispatchRecord,
        ),
        (
            "programbench_local_trial_v255_reject_snapshot_official_submission.json",
            ProgrambenchLocalTrialCandidateArtifactSnapshot,
        ),
        (
            "programbench_local_trial_v255_reject_projection_new_evidence_law.json",
            ProgrambenchLocalTrialLifecycleProjection,
        ),
    ],
)
def test_pb_trial_0b_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_trial_b_fixture(fixture_name))


def test_pb_trial_0b_rejects_dispatch_without_ready_a_readiness() -> None:
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
        released_attempt_worker_invocation,
        released_attempt_output_capture,
        released_attempt_candidate_materialization,
        released_attempt_sandbox_trace,
    ) = _load_attempt_b_rows()
    blocked_readiness = sandbox_readiness_review.model_copy(
        update={"readiness_posture": "blocked_by_sandbox_gap"}
    )

    with pytest.raises(ValueError, match="ready A sandbox readiness"):
        validate_pb_trial_0b_execution_bundle(
            trial_docket=trial_docket,
            execution_runbook=execution_runbook,
            sandbox_readiness_review=blocked_readiness,
            trial_guardrail=trial_guardrail,
            released_attempt_worker_invocation=released_attempt_worker_invocation,
            released_attempt_output_capture=released_attempt_output_capture,
            released_attempt_candidate_materialization=released_attempt_candidate_materialization,
            released_attempt_sandbox_trace=released_attempt_sandbox_trace,
            worker_dispatch_record=worker_dispatch_record,
            execution_capture=execution_capture,
            candidate_artifact_snapshot=candidate_artifact_snapshot,
            lifecycle_projection=lifecycle_projection,
        )


def test_pb_trial_0b_rejects_snapshot_when_forbidden_screening_blocks() -> None:
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
        released_attempt_worker_invocation,
        released_attempt_output_capture,
        released_attempt_candidate_materialization,
        released_attempt_sandbox_trace,
    ) = _load_attempt_b_rows()
    blocked_capture = execution_capture.model_copy(
        update={"forbidden_content_screen_verdict": "inconclusive_requires_review"}
    )

    with pytest.raises(ValueError, match="passed forbidden-content screening"):
        validate_pb_trial_0b_execution_bundle(
            trial_docket=trial_docket,
            execution_runbook=execution_runbook,
            sandbox_readiness_review=sandbox_readiness_review,
            trial_guardrail=trial_guardrail,
            released_attempt_worker_invocation=released_attempt_worker_invocation,
            released_attempt_output_capture=released_attempt_output_capture,
            released_attempt_candidate_materialization=released_attempt_candidate_materialization,
            released_attempt_sandbox_trace=released_attempt_sandbox_trace,
            worker_dispatch_record=worker_dispatch_record,
            execution_capture=blocked_capture,
            candidate_artifact_snapshot=candidate_artifact_snapshot,
            lifecycle_projection=lifecycle_projection,
        )


def test_pb_trial_0b_rejects_snapshot_outside_released_write_scope() -> None:
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
        released_attempt_worker_invocation,
        released_attempt_output_capture,
        released_attempt_candidate_materialization,
        released_attempt_sandbox_trace,
    ) = _load_attempt_b_rows()
    drifted_snapshot = candidate_artifact_snapshot.model_copy(
        update={"write_scope_ref": "write-scope:pb-trial-0b:outside"}
    )

    with pytest.raises(ValueError, match="write scope"):
        validate_pb_trial_0b_execution_bundle(
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
            candidate_artifact_snapshot=drifted_snapshot,
            lifecycle_projection=lifecycle_projection,
        )


def test_pb_trial_0b_rejects_lifecycle_projection_to_unreleased_attempt_refs() -> None:
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
        released_attempt_worker_invocation,
        released_attempt_output_capture,
        released_attempt_candidate_materialization,
        released_attempt_sandbox_trace,
    ) = _load_attempt_b_rows()
    drifted_projection = lifecycle_projection.model_copy(
        update={"mapped_attempt_invocation_refs": ["worker-invocation:pb-attempt-0b:stale"]}
    )

    with pytest.raises(ValueError, match="released PB-ATTEMPT invocation"):
        validate_pb_trial_0b_execution_bundle(
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
            lifecycle_projection=drifted_projection,
        )


def test_pb_trial_0b_schema_exports_mirror_root_spec_files() -> None:
    export_schema_main()

    for expected_schema, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))

        assert authoritative["properties"]["schema"]["const"] == expected_schema
        assert authoritative == mirror

        serialized = json.dumps(authoritative, sort_keys=True)
        assert _repo_root().as_posix() not in serialized
        assert not _WINDOWS_ABSOLUTE_PATH_RE.search(serialized)
