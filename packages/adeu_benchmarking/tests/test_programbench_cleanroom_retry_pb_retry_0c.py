from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_LOCAL_RETRY_DELTA_OBSERVATION_SUMMARY_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_OUTCOME_AUDIT_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_REMAND_SETTLEMENT_SCHEMA,
    ProgrambenchLocalRetryCandidateDeltaSnapshot,
    ProgrambenchLocalRetryDeltaObservationSummary,
    ProgrambenchLocalRetryDispatchRecord,
    ProgrambenchLocalRetryEligibilityReview,
    ProgrambenchLocalRetryExecutionCapture,
    ProgrambenchLocalRetryFamilyCloseoutAlignment,
    ProgrambenchLocalRetryLifecycleProjection,
    ProgrambenchLocalRetryLineageRegistry,
    ProgrambenchLocalRetryNonAuthorityGuardrail,
    ProgrambenchLocalRetryOutcomeAudit,
    ProgrambenchLocalRetryRemandSettlement,
    ProgrambenchLocalRetryRequest,
    ProgrambenchLocalRetrySandboxApplicationTrace,
    ProgrambenchLocalRetryScopeContract,
    ProgrambenchLocalTrialCandidateArtifactSnapshot,
    ProgrambenchLocalTrialFamilyCloseoutAlignment,
    ProgrambenchLocalTrialLifecycleProjection,
    ProgrambenchLocalTrialObservationSummary,
    ProgrambenchLocalTrialRemandDecision,
    ProgrambenchLocalTrialWorkerDispatchRecord,
    ProgrambenchTrialRemandSourceIndex,
    validate_pb_retry_0c_closeout_bundle,
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


def _fixture_root_retry_c() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus259"


def _fixture_root_trial_b() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus255"


def _fixture_root_trial_c() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus256"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_retry_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_retry_a(), name)


def _load_retry_b_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_retry_b(), name)


def _load_retry_c_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_retry_c(), name)


def _load_trial_b_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_trial_b(), name)


def _load_trial_c_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_trial_c(), name)


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
            PROGRAMBENCH_LOCAL_RETRY_OUTCOME_AUDIT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_retry_outcome_audit.v1.json",
            root / "spec" / "programbench_local_retry_outcome_audit.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_DELTA_OBSERVATION_SUMMARY_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_retry_delta_observation_summary.v1.json",
            root
            / "spec"
            / "programbench_local_retry_delta_observation_summary.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_REMAND_SETTLEMENT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_retry_remand_settlement.v1.json",
            root / "spec" / "programbench_local_retry_remand_settlement.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_retry_family_closeout_alignment.v1.json",
            root
            / "spec"
            / "programbench_local_retry_family_closeout_alignment.schema.json",
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


def _load_retry_c_rows() -> tuple[
    ProgrambenchLocalRetryOutcomeAudit,
    ProgrambenchLocalRetryDeltaObservationSummary,
    ProgrambenchLocalRetryRemandSettlement,
    ProgrambenchLocalRetryFamilyCloseoutAlignment,
]:
    return (
        ProgrambenchLocalRetryOutcomeAudit.model_validate(
            _load_retry_c_fixture("programbench_local_retry_outcome_audit_v259_reference.json")
        ),
        ProgrambenchLocalRetryDeltaObservationSummary.model_validate(
            _load_retry_c_fixture(
                "programbench_local_retry_delta_observation_summary_v259_reference.json"
            )
        ),
        ProgrambenchLocalRetryRemandSettlement.model_validate(
            _load_retry_c_fixture("programbench_local_retry_remand_settlement_v259_reference.json")
        ),
        ProgrambenchLocalRetryFamilyCloseoutAlignment.model_validate(
            _load_retry_c_fixture(
                "programbench_local_retry_family_closeout_alignment_v259_reference.json"
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


def _load_trial_c_rows() -> tuple[
    ProgrambenchLocalTrialObservationSummary,
    ProgrambenchLocalTrialRemandDecision,
    ProgrambenchLocalTrialFamilyCloseoutAlignment,
]:
    return (
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


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_LOCAL_RETRY_OUTCOME_AUDIT_SCHEMA,
            "programbench_local_retry_outcome_audit.v1.json",
            "programbench_local_retry_outcome_audit_v259_reference.json",
            ProgrambenchLocalRetryOutcomeAudit,
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_DELTA_OBSERVATION_SUMMARY_SCHEMA,
            "programbench_local_retry_delta_observation_summary.v1.json",
            "programbench_local_retry_delta_observation_summary_v259_reference.json",
            ProgrambenchLocalRetryDeltaObservationSummary,
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_REMAND_SETTLEMENT_SCHEMA,
            "programbench_local_retry_remand_settlement.v1.json",
            "programbench_local_retry_remand_settlement_v259_reference.json",
            ProgrambenchLocalRetryRemandSettlement,
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            "programbench_local_retry_family_closeout_alignment.v1.json",
            "programbench_local_retry_family_closeout_alignment_v259_reference.json",
            ProgrambenchLocalRetryFamilyCloseoutAlignment,
        ),
    ],
)
def test_pb_retry_0c_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_retry_c_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_retry_0c_reference_bundle_closes_local_retry_family() -> None:
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
        source_trial_observation_summary,
        source_trial_remand_decision,
        source_trial_family_closeout,
    ) = _load_trial_c_rows()
    (
        retry_dispatch_record,
        retry_execution_capture,
        retry_candidate_delta_snapshot,
        retry_lifecycle_projection,
        retry_sandbox_trace,
    ) = _load_retry_b_rows()
    (
        retry_outcome_audit,
        retry_delta_observation_summary,
        retry_remand_settlement,
        retry_family_closeout,
    ) = _load_retry_c_rows()

    validate_pb_retry_0c_closeout_bundle(
        retry_request=retry_request,
        retry_lineage_registry=retry_lineage_registry,
        remand_source_index=remand_source_index,
        retry_eligibility_review=retry_eligibility_review,
        retry_scope_contract=retry_scope_contract,
        retry_guardrail=retry_guardrail,
        source_trial_observation_summary=source_trial_observation_summary,
        source_trial_remand_decision=source_trial_remand_decision,
        source_trial_family_closeout=source_trial_family_closeout,
        source_trial_dispatch=source_trial_dispatch,
        source_trial_candidate_snapshot=source_trial_candidate_snapshot,
        source_trial_lifecycle_projection=source_trial_lifecycle_projection,
        retry_dispatch_record=retry_dispatch_record,
        retry_execution_capture=retry_execution_capture,
        retry_candidate_delta_snapshot=retry_candidate_delta_snapshot,
        retry_lifecycle_projection=retry_lifecycle_projection,
        retry_sandbox_trace=retry_sandbox_trace,
        retry_outcome_audit=retry_outcome_audit,
        retry_delta_observation_summary=retry_delta_observation_summary,
        retry_remand_settlement=retry_remand_settlement,
        retry_family_closeout=retry_family_closeout,
    )

    assert retry_outcome_audit.local_retry_result_posture == "local_retry_resolved"
    assert retry_remand_settlement.second_retry_authority_posture == (
        "no_second_retry_dispatch_authority_granted_by_pb_retry_0c"
    )
    assert retry_family_closeout.closed_slice_refs == [
        "PB-RETRY-0-A",
        "PB-RETRY-0-B",
        "PB-RETRY-0-C",
    ]


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_local_retry_v259_reject_comparative_delta_summary.json",
            ProgrambenchLocalRetryDeltaObservationSummary,
        ),
        (
            "programbench_local_retry_v259_reject_family_closeout_missing_slice.json",
            ProgrambenchLocalRetryFamilyCloseoutAlignment,
        ),
        (
            "programbench_local_retry_v259_reject_hidden_remand_ref.json",
            ProgrambenchLocalRetryOutcomeAudit,
        ),
        (
            "programbench_local_retry_v259_reject_second_retry_authority.json",
            ProgrambenchLocalRetryRemandSettlement,
        ),
    ],
)
def test_pb_retry_0c_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_retry_c_fixture(fixture_name))


def test_pb_retry_0c_rejects_mismatched_retry_lineage() -> None:
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
        source_trial_observation_summary,
        source_trial_remand_decision,
        source_trial_family_closeout,
    ) = _load_trial_c_rows()
    (
        retry_dispatch_record,
        retry_execution_capture,
        retry_candidate_delta_snapshot,
        retry_lifecycle_projection,
        retry_sandbox_trace,
    ) = _load_retry_b_rows()
    (
        retry_outcome_audit,
        retry_delta_observation_summary,
        retry_remand_settlement,
        retry_family_closeout,
    ) = _load_retry_c_rows()
    drifted_outcome = retry_outcome_audit.model_copy(
        update={"retry_lineage_ref": "retry-lineage:pb-retry-0:other"}
    )

    with pytest.raises(ValueError, match="preserve retry lineage"):
        validate_pb_retry_0c_closeout_bundle(
            retry_request=retry_request,
            retry_lineage_registry=retry_lineage_registry,
            remand_source_index=remand_source_index,
            retry_eligibility_review=retry_eligibility_review,
            retry_scope_contract=retry_scope_contract,
            retry_guardrail=retry_guardrail,
            source_trial_observation_summary=source_trial_observation_summary,
            source_trial_remand_decision=source_trial_remand_decision,
            source_trial_family_closeout=source_trial_family_closeout,
            source_trial_dispatch=source_trial_dispatch,
            source_trial_candidate_snapshot=source_trial_candidate_snapshot,
            source_trial_lifecycle_projection=source_trial_lifecycle_projection,
            retry_dispatch_record=retry_dispatch_record,
            retry_execution_capture=retry_execution_capture,
            retry_candidate_delta_snapshot=retry_candidate_delta_snapshot,
            retry_lifecycle_projection=retry_lifecycle_projection,
            retry_sandbox_trace=retry_sandbox_trace,
            retry_outcome_audit=drifted_outcome,
            retry_delta_observation_summary=retry_delta_observation_summary,
            retry_remand_settlement=retry_remand_settlement,
            retry_family_closeout=retry_family_closeout,
        )


def test_pb_retry_0c_rejects_invalid_b_execution_bundle() -> None:
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
        source_trial_observation_summary,
        source_trial_remand_decision,
        source_trial_family_closeout,
    ) = _load_trial_c_rows()
    (
        retry_dispatch_record,
        retry_execution_capture,
        retry_candidate_delta_snapshot,
        retry_lifecycle_projection,
        retry_sandbox_trace,
    ) = _load_retry_b_rows()
    (
        retry_outcome_audit,
        retry_delta_observation_summary,
        retry_remand_settlement,
        retry_family_closeout,
    ) = _load_retry_c_rows()
    violated_trace = retry_sandbox_trace.model_copy(
        update={"sandbox_violation_refs": ["sandbox-violation:pb-retry-0b:network-enabled"]}
    )

    with pytest.raises(ValueError, match="sandbox violations"):
        validate_pb_retry_0c_closeout_bundle(
            retry_request=retry_request,
            retry_lineage_registry=retry_lineage_registry,
            remand_source_index=remand_source_index,
            retry_eligibility_review=retry_eligibility_review,
            retry_scope_contract=retry_scope_contract,
            retry_guardrail=retry_guardrail,
            source_trial_observation_summary=source_trial_observation_summary,
            source_trial_remand_decision=source_trial_remand_decision,
            source_trial_family_closeout=source_trial_family_closeout,
            source_trial_dispatch=source_trial_dispatch,
            source_trial_candidate_snapshot=source_trial_candidate_snapshot,
            source_trial_lifecycle_projection=source_trial_lifecycle_projection,
            retry_dispatch_record=retry_dispatch_record,
            retry_execution_capture=retry_execution_capture,
            retry_candidate_delta_snapshot=retry_candidate_delta_snapshot,
            retry_lifecycle_projection=retry_lifecycle_projection,
            retry_sandbox_trace=violated_trace,
            retry_outcome_audit=retry_outcome_audit,
            retry_delta_observation_summary=retry_delta_observation_summary,
            retry_remand_settlement=retry_remand_settlement,
            retry_family_closeout=retry_family_closeout,
        )


def test_pb_retry_0c_rejects_unresolved_remand_marked_settled() -> None:
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
        source_trial_observation_summary,
        source_trial_remand_decision,
        source_trial_family_closeout,
    ) = _load_trial_c_rows()
    (
        retry_dispatch_record,
        retry_execution_capture,
        retry_candidate_delta_snapshot,
        retry_lifecycle_projection,
        retry_sandbox_trace,
    ) = _load_retry_b_rows()
    (
        retry_outcome_audit,
        retry_delta_observation_summary,
        retry_remand_settlement,
        retry_family_closeout,
    ) = _load_retry_c_rows()
    unresolved_outcome = retry_outcome_audit.model_copy(
        update={
            "carried_blocker_refs": ["blocker:pb-retry-0c:remand-unresolved"],
            "local_retry_result_posture": "local_retry_remand_unresolved",
        }
    )

    with pytest.raises(ValueError, match="settled retry remand requires resolved retry outcome"):
        validate_pb_retry_0c_closeout_bundle(
            retry_request=retry_request,
            retry_lineage_registry=retry_lineage_registry,
            remand_source_index=remand_source_index,
            retry_eligibility_review=retry_eligibility_review,
            retry_scope_contract=retry_scope_contract,
            retry_guardrail=retry_guardrail,
            source_trial_observation_summary=source_trial_observation_summary,
            source_trial_remand_decision=source_trial_remand_decision,
            source_trial_family_closeout=source_trial_family_closeout,
            source_trial_dispatch=source_trial_dispatch,
            source_trial_candidate_snapshot=source_trial_candidate_snapshot,
            source_trial_lifecycle_projection=source_trial_lifecycle_projection,
            retry_dispatch_record=retry_dispatch_record,
            retry_execution_capture=retry_execution_capture,
            retry_candidate_delta_snapshot=retry_candidate_delta_snapshot,
            retry_lifecycle_projection=retry_lifecycle_projection,
            retry_sandbox_trace=retry_sandbox_trace,
            retry_outcome_audit=unresolved_outcome,
            retry_delta_observation_summary=retry_delta_observation_summary,
            retry_remand_settlement=retry_remand_settlement,
            retry_family_closeout=retry_family_closeout,
        )


def test_pb_retry_0c_schema_exports_mirror_root_spec_files() -> None:
    export_schema_main()

    for expected_schema, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))

        assert authoritative["properties"]["schema"]["const"] == expected_schema
        assert authoritative == mirror

        serialized = json.dumps(authoritative, sort_keys=True)
        assert _repo_root().as_posix() not in serialized
        assert not _WINDOWS_ABSOLUTE_PATH_RE.search(serialized)
