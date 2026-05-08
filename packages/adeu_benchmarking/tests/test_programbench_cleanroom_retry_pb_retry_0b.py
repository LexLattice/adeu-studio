from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_LOCAL_RETRY_CANDIDATE_DELTA_SNAPSHOT_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_DISPATCH_RECORD_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_EXECUTION_CAPTURE_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_LIFECYCLE_PROJECTION_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_SANDBOX_APPLICATION_TRACE_SCHEMA,
    ProgrambenchLocalRetryCandidateDeltaSnapshot,
    ProgrambenchLocalRetryDispatchRecord,
    ProgrambenchLocalRetryEligibilityReview,
    ProgrambenchLocalRetryExecutionCapture,
    ProgrambenchLocalRetryLifecycleProjection,
    ProgrambenchLocalRetryLineageRegistry,
    ProgrambenchLocalRetryNonAuthorityGuardrail,
    ProgrambenchLocalRetryRequest,
    ProgrambenchLocalRetrySandboxApplicationTrace,
    ProgrambenchLocalRetryScopeContract,
    ProgrambenchLocalTrialCandidateArtifactSnapshot,
    ProgrambenchLocalTrialLifecycleProjection,
    ProgrambenchLocalTrialWorkerDispatchRecord,
    ProgrambenchTrialRemandSourceIndex,
    validate_pb_retry_0b_dispatch_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root_retry_a() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus257"


def _fixture_root_retry_b() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus258"


def _fixture_root_trial_b() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus255"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_retry_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_retry_a(), name)


def _load_retry_b_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_retry_b(), name)


def _load_trial_b_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_trial_b(), name)


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
            PROGRAMBENCH_LOCAL_RETRY_DISPATCH_RECORD_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_retry_dispatch_record.v1.json",
            root / "spec" / "programbench_local_retry_dispatch_record.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_EXECUTION_CAPTURE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_retry_execution_capture.v1.json",
            root / "spec" / "programbench_local_retry_execution_capture.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_CANDIDATE_DELTA_SNAPSHOT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_retry_candidate_delta_snapshot.v1.json",
            root
            / "spec"
            / "programbench_local_retry_candidate_delta_snapshot.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_LIFECYCLE_PROJECTION_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_retry_lifecycle_projection.v1.json",
            root / "spec" / "programbench_local_retry_lifecycle_projection.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_SANDBOX_APPLICATION_TRACE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_retry_sandbox_application_trace.v1.json",
            root / "spec" / "programbench_local_retry_sandbox_application_trace.schema.json",
        ),
    ]


def _load_retry_a_rows() -> tuple[
    ProgrambenchLocalRetryRequest,
    ProgrambenchLocalRetryLineageRegistry,
    ProgrambenchTrialRemandSourceIndex,
    ProgrambenchLocalRetryEligibilityReview,
    ProgrambenchLocalRetryScopeContract,
    ProgrambenchLocalRetryNonAuthorityGuardrail,
]:
    return (
        ProgrambenchLocalRetryRequest.model_validate(
            _load_retry_a_fixture("programbench_local_retry_request_v257_reference.json")
        ),
        ProgrambenchLocalRetryLineageRegistry.model_validate(
            _load_retry_a_fixture("programbench_local_retry_lineage_registry_v257_reference.json")
        ),
        ProgrambenchTrialRemandSourceIndex.model_validate(
            _load_retry_a_fixture("programbench_trial_remand_source_index_v257_reference.json")
        ),
        ProgrambenchLocalRetryEligibilityReview.model_validate(
            _load_retry_a_fixture("programbench_local_retry_eligibility_review_v257_reference.json")
        ),
        ProgrambenchLocalRetryScopeContract.model_validate(
            _load_retry_a_fixture("programbench_local_retry_scope_contract_v257_reference.json")
        ),
        ProgrambenchLocalRetryNonAuthorityGuardrail.model_validate(
            _load_retry_a_fixture(
                "programbench_local_retry_non_authority_guardrail_v257_reference.json"
            )
        ),
    )


def _load_retry_b_rows() -> tuple[
    ProgrambenchLocalRetryDispatchRecord,
    ProgrambenchLocalRetryExecutionCapture,
    ProgrambenchLocalRetryCandidateDeltaSnapshot,
    ProgrambenchLocalRetryLifecycleProjection,
    ProgrambenchLocalRetrySandboxApplicationTrace,
]:
    return (
        ProgrambenchLocalRetryDispatchRecord.model_validate(
            _load_retry_b_fixture("programbench_local_retry_dispatch_record_v258_reference.json")
        ),
        ProgrambenchLocalRetryExecutionCapture.model_validate(
            _load_retry_b_fixture("programbench_local_retry_execution_capture_v258_reference.json")
        ),
        ProgrambenchLocalRetryCandidateDeltaSnapshot.model_validate(
            _load_retry_b_fixture(
                "programbench_local_retry_candidate_delta_snapshot_v258_reference.json"
            )
        ),
        ProgrambenchLocalRetryLifecycleProjection.model_validate(
            _load_retry_b_fixture(
                "programbench_local_retry_lifecycle_projection_v258_reference.json"
            )
        ),
        ProgrambenchLocalRetrySandboxApplicationTrace.model_validate(
            _load_retry_b_fixture(
                "programbench_local_retry_sandbox_application_trace_v258_reference.json"
            )
        ),
    )


def _load_trial_b_rows() -> tuple[
    ProgrambenchLocalTrialWorkerDispatchRecord,
    ProgrambenchLocalTrialCandidateArtifactSnapshot,
    ProgrambenchLocalTrialLifecycleProjection,
]:
    return (
        ProgrambenchLocalTrialWorkerDispatchRecord.model_validate(
            _load_trial_b_fixture(
                "programbench_local_trial_worker_dispatch_record_v255_reference.json"
            )
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


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_LOCAL_RETRY_DISPATCH_RECORD_SCHEMA,
            "programbench_local_retry_dispatch_record.v1.json",
            "programbench_local_retry_dispatch_record_v258_reference.json",
            ProgrambenchLocalRetryDispatchRecord,
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_EXECUTION_CAPTURE_SCHEMA,
            "programbench_local_retry_execution_capture.v1.json",
            "programbench_local_retry_execution_capture_v258_reference.json",
            ProgrambenchLocalRetryExecutionCapture,
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_CANDIDATE_DELTA_SNAPSHOT_SCHEMA,
            "programbench_local_retry_candidate_delta_snapshot.v1.json",
            "programbench_local_retry_candidate_delta_snapshot_v258_reference.json",
            ProgrambenchLocalRetryCandidateDeltaSnapshot,
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_LIFECYCLE_PROJECTION_SCHEMA,
            "programbench_local_retry_lifecycle_projection.v1.json",
            "programbench_local_retry_lifecycle_projection_v258_reference.json",
            ProgrambenchLocalRetryLifecycleProjection,
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_SANDBOX_APPLICATION_TRACE_SCHEMA,
            "programbench_local_retry_sandbox_application_trace.v1.json",
            "programbench_local_retry_sandbox_application_trace_v258_reference.json",
            ProgrambenchLocalRetrySandboxApplicationTrace,
        ),
    ],
)
def test_pb_retry_0b_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_retry_b_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_retry_0b_reference_bundle_records_one_local_retry_specimen() -> None:
    (
        retry_request,
        retry_lineage_registry,
        remand_source_index,
        retry_eligibility_review,
        retry_scope_contract,
        retry_guardrail,
    ) = _load_retry_a_rows()
    (
        source_trial_dispatch,
        source_trial_candidate_snapshot,
        source_trial_lifecycle_projection,
    ) = _load_trial_b_rows()
    (
        retry_dispatch_record,
        retry_execution_capture,
        retry_candidate_delta_snapshot,
        retry_lifecycle_projection,
        retry_sandbox_trace,
    ) = _load_retry_b_rows()

    validate_pb_retry_0b_dispatch_bundle(
        retry_request=retry_request,
        retry_lineage_registry=retry_lineage_registry,
        remand_source_index=remand_source_index,
        retry_eligibility_review=retry_eligibility_review,
        retry_scope_contract=retry_scope_contract,
        retry_guardrail=retry_guardrail,
        source_trial_dispatch=source_trial_dispatch,
        source_trial_candidate_snapshot=source_trial_candidate_snapshot,
        source_trial_lifecycle_projection=source_trial_lifecycle_projection,
        retry_dispatch_record=retry_dispatch_record,
        retry_execution_capture=retry_execution_capture,
        retry_candidate_delta_snapshot=retry_candidate_delta_snapshot,
        retry_lifecycle_projection=retry_lifecycle_projection,
        retry_sandbox_trace=retry_sandbox_trace,
    )

    assert retry_dispatch_record.retry_dispatch_authority_ref == (
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS258.md"
    )
    assert retry_dispatch_record.retry_depth == 1
    assert retry_execution_capture.forbidden_content_screen_verdict == "passed"
    assert retry_candidate_delta_snapshot.inside_released_write_scope is True
    assert retry_lifecycle_projection.new_evidence_law_posture == (
        "no_new_evidence_law_defined_by_pb_retry_0b"
    )


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_local_retry_v258_reject_dispatch_missing_b_lock_authority.json",
            ProgrambenchLocalRetryDispatchRecord,
        ),
        (
            "programbench_local_retry_v258_reject_second_dispatch_depth.json",
            ProgrambenchLocalRetryDispatchRecord,
        ),
        (
            "programbench_local_retry_v258_reject_snapshot_before_screening.json",
            ProgrambenchLocalRetryCandidateDeltaSnapshot,
        ),
        (
            "programbench_local_retry_v258_reject_projection_new_evidence_law.json",
            ProgrambenchLocalRetryLifecycleProjection,
        ),
    ],
)
def test_pb_retry_0b_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_retry_b_fixture(fixture_name))


def test_pb_retry_0b_rejects_dispatch_without_ready_a_eligibility() -> None:
    (
        retry_request,
        retry_lineage_registry,
        remand_source_index,
        retry_eligibility_review,
        retry_scope_contract,
        retry_guardrail,
    ) = _load_retry_a_rows()
    (
        source_trial_dispatch,
        source_trial_candidate_snapshot,
        source_trial_lifecycle_projection,
    ) = _load_trial_b_rows()
    (
        retry_dispatch_record,
        retry_execution_capture,
        retry_candidate_delta_snapshot,
        retry_lifecycle_projection,
        retry_sandbox_trace,
    ) = _load_retry_b_rows()
    blocked_eligibility = retry_eligibility_review.model_copy(
        update={
            "carried_blocker_refs": ["blocker:pb-retry-0a:scope-widening"],
            "eligibility_posture": "blocked_by_scope_widening",
            "ready_basis_posture": "blocked",
        }
    )

    with pytest.raises(ValueError, match="eligible A retry review"):
        validate_pb_retry_0b_dispatch_bundle(
            retry_request=retry_request,
            retry_lineage_registry=retry_lineage_registry,
            remand_source_index=remand_source_index,
            retry_eligibility_review=blocked_eligibility,
            retry_scope_contract=retry_scope_contract,
            retry_guardrail=retry_guardrail,
            source_trial_dispatch=source_trial_dispatch,
            source_trial_candidate_snapshot=source_trial_candidate_snapshot,
            source_trial_lifecycle_projection=source_trial_lifecycle_projection,
            retry_dispatch_record=retry_dispatch_record,
            retry_execution_capture=retry_execution_capture,
            retry_candidate_delta_snapshot=retry_candidate_delta_snapshot,
            retry_lifecycle_projection=retry_lifecycle_projection,
            retry_sandbox_trace=retry_sandbox_trace,
        )


def test_pb_retry_0b_rejects_existing_retry_request() -> None:
    (
        retry_request,
        retry_lineage_registry,
        remand_source_index,
        retry_eligibility_review,
        retry_scope_contract,
        retry_guardrail,
    ) = _load_retry_a_rows()
    (
        source_trial_dispatch,
        source_trial_candidate_snapshot,
        source_trial_lifecycle_projection,
    ) = _load_trial_b_rows()
    (
        retry_dispatch_record,
        retry_execution_capture,
        retry_candidate_delta_snapshot,
        retry_lifecycle_projection,
        retry_sandbox_trace,
    ) = _load_retry_b_rows()
    drifted_registry = retry_lineage_registry.model_copy(
        update={"existing_retry_request_refs": ["retry-request:pb-retry-0a:reference"]}
    )

    with pytest.raises(ValueError, match="existing retry request"):
        validate_pb_retry_0b_dispatch_bundle(
            retry_request=retry_request,
            retry_lineage_registry=drifted_registry,
            remand_source_index=remand_source_index,
            retry_eligibility_review=retry_eligibility_review,
            retry_scope_contract=retry_scope_contract,
            retry_guardrail=retry_guardrail,
            source_trial_dispatch=source_trial_dispatch,
            source_trial_candidate_snapshot=source_trial_candidate_snapshot,
            source_trial_lifecycle_projection=source_trial_lifecycle_projection,
            retry_dispatch_record=retry_dispatch_record,
            retry_execution_capture=retry_execution_capture,
            retry_candidate_delta_snapshot=retry_candidate_delta_snapshot,
            retry_lifecycle_projection=retry_lifecycle_projection,
            retry_sandbox_trace=retry_sandbox_trace,
        )


def test_pb_retry_0b_rejects_snapshot_when_execution_screening_blocks() -> None:
    (
        retry_request,
        retry_lineage_registry,
        remand_source_index,
        retry_eligibility_review,
        retry_scope_contract,
        retry_guardrail,
    ) = _load_retry_a_rows()
    (
        source_trial_dispatch,
        source_trial_candidate_snapshot,
        source_trial_lifecycle_projection,
    ) = _load_trial_b_rows()
    (
        retry_dispatch_record,
        retry_execution_capture,
        retry_candidate_delta_snapshot,
        retry_lifecycle_projection,
        retry_sandbox_trace,
    ) = _load_retry_b_rows()
    blocked_capture = retry_execution_capture.model_copy(
        update={"forbidden_content_screen_verdict": "inconclusive_requires_review"}
    )

    with pytest.raises(ValueError, match="passed forbidden-content screening"):
        validate_pb_retry_0b_dispatch_bundle(
            retry_request=retry_request,
            retry_lineage_registry=retry_lineage_registry,
            remand_source_index=remand_source_index,
            retry_eligibility_review=retry_eligibility_review,
            retry_scope_contract=retry_scope_contract,
            retry_guardrail=retry_guardrail,
            source_trial_dispatch=source_trial_dispatch,
            source_trial_candidate_snapshot=source_trial_candidate_snapshot,
            source_trial_lifecycle_projection=source_trial_lifecycle_projection,
            retry_dispatch_record=retry_dispatch_record,
            retry_execution_capture=blocked_capture,
            retry_candidate_delta_snapshot=retry_candidate_delta_snapshot,
            retry_lifecycle_projection=retry_lifecycle_projection,
            retry_sandbox_trace=retry_sandbox_trace,
        )


def test_pb_retry_0b_rejects_candidate_delta_outside_source_write_scope() -> None:
    (
        retry_request,
        retry_lineage_registry,
        remand_source_index,
        retry_eligibility_review,
        retry_scope_contract,
        retry_guardrail,
    ) = _load_retry_a_rows()
    (
        source_trial_dispatch,
        source_trial_candidate_snapshot,
        source_trial_lifecycle_projection,
    ) = _load_trial_b_rows()
    (
        retry_dispatch_record,
        retry_execution_capture,
        retry_candidate_delta_snapshot,
        retry_lifecycle_projection,
        retry_sandbox_trace,
    ) = _load_retry_b_rows()
    drifted_snapshot = retry_candidate_delta_snapshot.model_copy(
        update={"write_scope_ref": "write-scope:pb-retry-0b:outside"}
    )

    with pytest.raises(ValueError, match="write scope"):
        validate_pb_retry_0b_dispatch_bundle(
            retry_request=retry_request,
            retry_lineage_registry=retry_lineage_registry,
            remand_source_index=remand_source_index,
            retry_eligibility_review=retry_eligibility_review,
            retry_scope_contract=retry_scope_contract,
            retry_guardrail=retry_guardrail,
            source_trial_dispatch=source_trial_dispatch,
            source_trial_candidate_snapshot=source_trial_candidate_snapshot,
            source_trial_lifecycle_projection=source_trial_lifecycle_projection,
            retry_dispatch_record=retry_dispatch_record,
            retry_execution_capture=retry_execution_capture,
            retry_candidate_delta_snapshot=drifted_snapshot,
            retry_lifecycle_projection=retry_lifecycle_projection,
            retry_sandbox_trace=retry_sandbox_trace,
        )


def test_pb_retry_0b_rejects_sandbox_trace_violations() -> None:
    (
        retry_request,
        retry_lineage_registry,
        remand_source_index,
        retry_eligibility_review,
        retry_scope_contract,
        retry_guardrail,
    ) = _load_retry_a_rows()
    (
        source_trial_dispatch,
        source_trial_candidate_snapshot,
        source_trial_lifecycle_projection,
    ) = _load_trial_b_rows()
    (
        retry_dispatch_record,
        retry_execution_capture,
        retry_candidate_delta_snapshot,
        retry_lifecycle_projection,
        retry_sandbox_trace,
    ) = _load_retry_b_rows()
    violated_trace = retry_sandbox_trace.model_copy(
        update={"sandbox_violation_refs": ["sandbox-violation:pb-retry-0b:network-enabled"]}
    )

    with pytest.raises(ValueError, match="sandbox violations"):
        validate_pb_retry_0b_dispatch_bundle(
            retry_request=retry_request,
            retry_lineage_registry=retry_lineage_registry,
            remand_source_index=remand_source_index,
            retry_eligibility_review=retry_eligibility_review,
            retry_scope_contract=retry_scope_contract,
            retry_guardrail=retry_guardrail,
            source_trial_dispatch=source_trial_dispatch,
            source_trial_candidate_snapshot=source_trial_candidate_snapshot,
            source_trial_lifecycle_projection=source_trial_lifecycle_projection,
            retry_dispatch_record=retry_dispatch_record,
            retry_execution_capture=retry_execution_capture,
            retry_candidate_delta_snapshot=retry_candidate_delta_snapshot,
            retry_lifecycle_projection=retry_lifecycle_projection,
            retry_sandbox_trace=violated_trace,
        )


def test_pb_retry_0b_schema_exports_mirror_root_spec_files() -> None:
    export_schema_main()

    for expected_schema, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))

        assert authoritative["properties"]["schema"]["const"] == expected_schema
        assert authoritative == mirror

        serialized = json.dumps(authoritative, sort_keys=True)
        assert _repo_root().as_posix() not in serialized
        assert not _WINDOWS_ABSOLUTE_PATH_RE.search(serialized)
