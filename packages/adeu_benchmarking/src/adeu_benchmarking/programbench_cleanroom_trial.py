from __future__ import annotations

import re
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

from .programbench_cleanroom_attempt import (
    ProgrambenchReconstructionAttemptCandidateMaterialization,
    ProgrambenchReconstructionAttemptDispatchPreflight,
    ProgrambenchReconstructionAttemptFamilyCloseoutAlignment,
    ProgrambenchReconstructionAttemptNonAuthorityGuardrail,
    ProgrambenchReconstructionAttemptOutputCapture,
    ProgrambenchReconstructionAttemptRequest,
    ProgrambenchReconstructionAttemptResultReview,
    ProgrambenchReconstructionAttemptSandboxApplicationTrace,
    ProgrambenchReconstructionAttemptWorkerInputPacket,
    ProgrambenchReconstructionAttemptWorkerInvocationRecord,
)

MODEL_CONFIG = ConfigDict(
    extra="forbid",
    frozen=True,
    populate_by_name=True,
    protected_namespaces=(),
)

PROGRAMBENCH_LOCAL_RECONSTRUCTION_TRIAL_DOCKET_SCHEMA = (
    "programbench_local_reconstruction_trial_docket@1"
)
PROGRAMBENCH_LOCAL_TRIAL_EXECUTION_RUNBOOK_SCHEMA = "programbench_local_trial_execution_runbook@1"
PROGRAMBENCH_LOCAL_TRIAL_SANDBOX_READINESS_REVIEW_SCHEMA = (
    "programbench_local_trial_sandbox_readiness_review@1"
)
PROGRAMBENCH_LOCAL_TRIAL_NON_AUTHORITY_GUARDRAIL_SCHEMA = (
    "programbench_local_trial_non_authority_guardrail@1"
)

PROGRAMBENCH_LOCAL_TRIAL_WORKER_DISPATCH_RECORD_SCHEMA = (
    "programbench_local_trial_worker_dispatch_record@1"
)
PROGRAMBENCH_LOCAL_TRIAL_EXECUTION_CAPTURE_SCHEMA = "programbench_local_trial_execution_capture@1"
PROGRAMBENCH_LOCAL_TRIAL_CANDIDATE_ARTIFACT_SNAPSHOT_SCHEMA = (
    "programbench_local_trial_candidate_artifact_snapshot@1"
)
PROGRAMBENCH_LOCAL_TRIAL_LIFECYCLE_PROJECTION_SCHEMA = (
    "programbench_local_trial_lifecycle_projection@1"
)
PROGRAMBENCH_LOCAL_TRIAL_OUTCOME_AUDIT_SCHEMA = "programbench_local_trial_outcome_audit@1"
PROGRAMBENCH_LOCAL_TRIAL_OBSERVATION_SUMMARY_SCHEMA = (
    "programbench_local_trial_observation_summary@1"
)
PROGRAMBENCH_LOCAL_TRIAL_REMAND_DECISION_SCHEMA = "programbench_local_trial_remand_decision@1"
PROGRAMBENCH_LOCAL_TRIAL_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA = (
    "programbench_local_trial_family_closeout_alignment@1"
)

PB_TRIAL_0A_ARTIFACT_KINDS = {
    PROGRAMBENCH_LOCAL_RECONSTRUCTION_TRIAL_DOCKET_SCHEMA,
    PROGRAMBENCH_LOCAL_TRIAL_EXECUTION_RUNBOOK_SCHEMA,
    PROGRAMBENCH_LOCAL_TRIAL_SANDBOX_READINESS_REVIEW_SCHEMA,
    PROGRAMBENCH_LOCAL_TRIAL_NON_AUTHORITY_GUARDRAIL_SCHEMA,
}
PB_TRIAL_0B_ARTIFACT_KINDS = {
    PROGRAMBENCH_LOCAL_TRIAL_WORKER_DISPATCH_RECORD_SCHEMA,
    PROGRAMBENCH_LOCAL_TRIAL_EXECUTION_CAPTURE_SCHEMA,
    PROGRAMBENCH_LOCAL_TRIAL_CANDIDATE_ARTIFACT_SNAPSHOT_SCHEMA,
    PROGRAMBENCH_LOCAL_TRIAL_LIFECYCLE_PROJECTION_SCHEMA,
}
PB_TRIAL_0C_ARTIFACT_KINDS = {
    PROGRAMBENCH_LOCAL_TRIAL_OUTCOME_AUDIT_SCHEMA,
    PROGRAMBENCH_LOCAL_TRIAL_OBSERVATION_SUMMARY_SCHEMA,
    PROGRAMBENCH_LOCAL_TRIAL_REMAND_DECISION_SCHEMA,
    PROGRAMBENCH_LOCAL_TRIAL_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
}
PB_TRIAL_0A_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS = (
    PB_TRIAL_0B_ARTIFACT_KINDS | PB_TRIAL_0C_ARTIFACT_KINDS
)

_SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
_FORBIDDEN_REF_MARKERS = (
    "benchmark-score",
    "decompilation",
    "docker-socket",
    "external-repo",
    "hidden-test",
    "host-secret",
    "internet-lookup",
    "model-ranking",
    "official-evaluator",
    "original-source",
)
_REQUIRED_READINESS_CHECK_KINDS = {
    "bounded_write_scope",
    "closed_tool_manifest",
    "decompilation_disabled",
    "docker_socket_absent",
    "host_secrets_absent",
    "network_disabled",
    "run_budget_bound",
    "source_lookup_disabled",
}
_PB_TRIAL_0B_DISPATCH_AUTHORITY_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS255.md"
_PB_TRIAL_CLOSED_SLICES = ["PB-TRIAL-0-A", "PB-TRIAL-0-B", "PB-TRIAL-0-C"]
_COMPARATIVE_LANGUAGE_MARKERS = (
    "better than",
    "benchmark score",
    "leaderboard",
    "model ranking",
    "outperformed",
    "ranked",
    "retry comparison",
)


def _ensure_non_empty_trimmed(values: list[str], *, field_name: str) -> None:
    for value in values:
        if not isinstance(value, str) or not value or value != value.strip():
            raise ValueError(f"{field_name} entries must be non-empty trimmed strings")


def _ensure_non_empty_unique(values: list[str], *, field_name: str) -> None:
    if not values:
        raise ValueError(f"{field_name} must contain at least one entry")
    _ensure_non_empty_trimmed(values, field_name=field_name)
    if len(values) != len(set(values)):
        raise ValueError(f"{field_name} must not contain duplicates")


def _ensure_sorted_unique(values: list[str], *, field_name: str) -> None:
    _ensure_non_empty_unique(values, field_name=field_name)
    if values != sorted(values):
        raise ValueError(f"{field_name} must be lexicographically sorted")


def _ensure_sorted_unique_allow_empty(values: list[str], *, field_name: str) -> None:
    if values:
        _ensure_non_empty_trimmed(values, field_name=field_name)
    if len(values) != len(set(values)):
        raise ValueError(f"{field_name} must not contain duplicates")
    if values != sorted(values):
        raise ValueError(f"{field_name} must be lexicographically sorted")


def _ensure_hash(value: str, *, field_name: str) -> None:
    if not _SHA256_RE.match(value):
        raise ValueError(f"{field_name} must be a sha256:<64 lowercase hex> hash")


def _ensure_no_forbidden_refs(values: list[str], *, field_name: str) -> None:
    leaked = sorted(
        ref for ref in values if any(marker in ref for marker in _FORBIDDEN_REF_MARKERS)
    )
    if leaked:
        raise ValueError(f"{field_name} contains forbidden trial evidence refs: {leaked}")


class _TrialBase(BaseModel):
    model_config = MODEL_CONFIG


class ProgrambenchLocalTrialAllowedStepRow(_TrialBase):
    step_ref: str
    step_kind: Literal[
        "candidate_snapshot_later",
        "execution_capture_later",
        "lifecycle_projection_later",
        "local_worker_dispatch_later",
        "worker_input_materialization_later",
    ]
    step_scope_posture: Literal["planned_for_later_pb_trial_0b_only"]
    command_shape_posture: Literal["argv_shaped_if_command_like", "not_command_shaped"]
    evidence_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_allowed_step(self) -> "ProgrambenchLocalTrialAllowedStepRow":
        _ensure_sorted_unique(self.evidence_refs, field_name="allowed step evidence_refs")
        return self


class ProgrambenchLocalTrialForbiddenStepRow(_TrialBase):
    forbidden_step_ref: str
    forbidden_step_kind: Literal[
        "benchmark_scoring",
        "decompilation",
        "external_repo_lookup",
        "hidden_test_access",
        "internet_lookup",
        "model_ranking",
        "official_programbench_runner_contact",
        "official_submission",
        "original_source_lookup",
        "retry_dispatch",
    ]
    forbiddance_posture: Literal["forbidden_by_pb_trial_0a"]
    limitation_note: str


class ProgrambenchLocalTrialCaptureObligationRow(_TrialBase):
    capture_obligation_ref: str
    capture_kind: Literal[
        "candidate_snapshot_manifest_hash",
        "full_transcript_hash",
        "sandbox_witness_bundle",
        "stderr_hash_and_bounded_excerpt",
        "stdout_hash_and_bounded_excerpt",
        "tool_manifest_hashes",
    ]
    capture_scope_posture: Literal["required_for_later_pb_trial_0b"]
    witness_requirement_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_capture_obligation(self) -> "ProgrambenchLocalTrialCaptureObligationRow":
        _ensure_sorted_unique(
            self.witness_requirement_refs,
            field_name="capture obligation witness_requirement_refs",
        )
        return self


class ProgrambenchLocalTrialReadinessCheckRow(_TrialBase):
    readiness_check_ref: str
    check_kind: Literal[
        "bounded_write_scope",
        "closed_tool_manifest",
        "decompilation_disabled",
        "docker_socket_absent",
        "host_secrets_absent",
        "network_disabled",
        "run_budget_bound",
        "source_lookup_disabled",
    ]
    check_posture: Literal["blocked", "passed"]
    witness_requirement_ref: str
    evidence_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_readiness_check(self) -> "ProgrambenchLocalTrialReadinessCheckRow":
        _ensure_sorted_unique(self.evidence_refs, field_name="readiness check evidence_refs")
        return self


class ProgrambenchLocalTrialForbiddenAuthorityRow(_TrialBase):
    forbidden_authority_ref: str
    authority_kind: Literal[
        "benchmark_truth",
        "candidate_artifact_snapshot",
        "command_execution",
        "future_family_selection",
        "hidden_test_inference",
        "lifecycle_projection",
        "model_ranking",
        "official_programbench_participation",
        "official_submission",
        "outcome_audit",
        "retry_authority",
        "source_lookup",
        "worker_dispatch",
    ]
    forbiddance_posture: Literal["forbidden_by_pb_trial_0a"]
    limitation_note: str


class ProgrambenchLocalTrialDeclaredUncertaintyRow(_TrialBase):
    uncertainty_ref: str
    uncertainty_kind: Literal[
        "candidate_behavior_gap_declared",
        "execution_observation_gap_declared",
        "sandbox_witness_gap_declared",
    ]
    uncertainty_posture: Literal["worker_declared_uncertainty_not_outcome_or_remand_authority"]
    evidence_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_uncertainty_row(self) -> "ProgrambenchLocalTrialDeclaredUncertaintyRow":
        _ensure_sorted_unique(self.evidence_refs, field_name="uncertainty evidence_refs")
        return self


class ProgrambenchLocalTrialForbiddenContentScreeningRow(_TrialBase):
    screening_ref: str
    screening_kind: Literal[
        "excluded_derived_content",
        "forbidden_source_content",
        "hidden_evidence_content",
        "postmortem_only_content",
    ]
    screening_posture: Literal["blocked", "passed"]
    evidence_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_screening_row(self) -> "ProgrambenchLocalTrialForbiddenContentScreeningRow":
        _ensure_sorted_unique(self.evidence_refs, field_name="screening evidence_refs")
        return self


class ProgrambenchLocalTrialMaterializedFileRow(_TrialBase):
    materialized_file_ref: str
    path_ref: str
    file_role: Literal[
        "candidate_config_file",
        "candidate_source_file",
        "candidate_support_file",
        "generated_output_artifact",
    ]
    write_scope_ref: str
    materialization_posture: Literal["local_trial_sandbox_materialized_file"]
    limitation_note: str


class ProgrambenchLocalTrialGeneratedFileHashRow(_TrialBase):
    generated_file_hash_ref: str
    materialized_file_ref: str
    content_hash: str
    hash_role: Literal["local_trial_candidate_content_hash"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_generated_hash_row(self) -> "ProgrambenchLocalTrialGeneratedFileHashRow":
        _ensure_hash(self.content_hash, field_name="content_hash")
        return self


class ProgrambenchLocalTrialProjectionValidationRow(_TrialBase):
    projection_validation_ref: str
    validation_kind: Literal[
        "candidate_snapshot_mapped",
        "execution_capture_mapped",
        "mapped_attempt_lifecycle_refs_present",
        "new_evidence_law_absent",
        "worker_dispatch_mapped",
    ]
    validation_posture: Literal["passed"]
    evidence_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_projection_row(self) -> "ProgrambenchLocalTrialProjectionValidationRow":
        _ensure_sorted_unique(self.evidence_refs, field_name="projection evidence_refs")
        return self


class ProgrambenchLocalTrialLocalEvidenceRow(_TrialBase):
    local_evidence_ref: str
    evidence_kind: Literal[
        "candidate_snapshot_inside_write_scope",
        "execution_capture_available",
        "lifecycle_projection_validated",
        "runbook_satisfaction_reviewed",
        "sandbox_satisfaction_reviewed",
    ]
    evidence_posture: Literal["local_trial_evidence_only"]
    source_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_local_evidence(self) -> "ProgrambenchLocalTrialLocalEvidenceRow":
        _ensure_sorted_unique(self.source_refs, field_name="local evidence source_refs")
        _ensure_no_forbidden_refs(self.source_refs, field_name="local evidence source_refs")
        return self


class ProgrambenchLocalTrialRunbookSatisfactionRow(_TrialBase):
    runbook_satisfaction_ref: str
    satisfaction_kind: Literal[
        "allowed_steps_satisfied",
        "capture_obligations_satisfied",
        "forbidden_steps_respected",
        "input_hash_preserved",
    ]
    satisfaction_posture: Literal["blocked", "passed", "warning"]
    evidence_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_runbook_satisfaction(
        self,
    ) -> "ProgrambenchLocalTrialRunbookSatisfactionRow":
        _ensure_sorted_unique(self.evidence_refs, field_name="runbook satisfaction evidence_refs")
        _ensure_no_forbidden_refs(
            self.evidence_refs,
            field_name="runbook satisfaction evidence_refs",
        )
        return self


class ProgrambenchLocalTrialSandboxSatisfactionRow(_TrialBase):
    sandbox_satisfaction_ref: str
    satisfaction_kind: Literal[
        "forbidden_access_absent",
        "sandbox_witnesses_satisfied",
        "write_scope_satisfied",
    ]
    satisfaction_posture: Literal["blocked", "passed", "warning"]
    evidence_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_sandbox_satisfaction(
        self,
    ) -> "ProgrambenchLocalTrialSandboxSatisfactionRow":
        _ensure_sorted_unique(self.evidence_refs, field_name="sandbox satisfaction evidence_refs")
        _ensure_no_forbidden_refs(
            self.evidence_refs,
            field_name="sandbox satisfaction evidence_refs",
        )
        return self


class ProgrambenchLocalTrialObservationRow(_TrialBase):
    observation_ref: str
    observation_kind: Literal[
        "candidate_snapshot_observed",
        "local_outcome_observed",
        "single_trial_scope_observed",
    ]
    observation_text: str = Field(max_length=320)
    observation_scope_posture: Literal["single_local_trial_only"]
    evidence_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_observation(self) -> "ProgrambenchLocalTrialObservationRow":
        _ensure_sorted_unique(self.evidence_refs, field_name="observation evidence_refs")
        _ensure_no_forbidden_refs(self.evidence_refs, field_name="observation evidence_refs")
        text = self.observation_text.lower()
        leaked_markers = [marker for marker in _COMPARATIVE_LANGUAGE_MARKERS if marker in text]
        if leaked_markers:
            raise ValueError(
                "trial observation rows cannot contain comparative or benchmark language: "
                f"{leaked_markers}"
            )
        return self


class ProgrambenchLocalTrialLimitationRow(_TrialBase):
    limitation_ref: str
    limitation_kind: Literal[
        "hidden_tests_not_consulted",
        "local_trial_only",
        "no_model_comparison",
        "not_benchmark_truth",
    ]
    limitation_posture: Literal["declared"]
    limitation_note: str


class ProgrambenchLocalTrialRemandDecisionRow(_TrialBase):
    remand_decision_row_ref: str
    remand_source_kind: Literal[
        "local_candidate_snapshot_gap",
        "local_evidence_inconclusive",
        "local_execution_capture_gap",
        "local_lifecycle_projection_gap",
        "runbook_satisfaction_gap",
        "sandbox_readiness_or_application_gap",
        "worker_declared_uncertainty",
    ]
    remand_posture: Literal["local_pressure_only_no_retry_authority"]
    evidence_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_remand_row(self) -> "ProgrambenchLocalTrialRemandDecisionRow":
        _ensure_sorted_unique(self.evidence_refs, field_name="remand evidence_refs")
        _ensure_no_forbidden_refs(self.evidence_refs, field_name="remand evidence_refs")
        return self


class ProgrambenchLocalReconstructionTrialDocket(_TrialBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_RECONSTRUCTION_TRIAL_DOCKET_SCHEMA] = Field(
        alias="schema"
    )
    trial_docket_ref: str
    attempt_request_ref: str
    worker_input_packet_ref: str
    dispatch_preflight_ref: str
    attempt_guardrail_ref: str
    prior_attempt_result_review_context_ref: str
    attempt_family_closeout_ref: str
    workbench_lineage_refs: list[str] = Field(min_length=1)
    case_packet_refs: list[str] = Field(min_length=1)
    worker_profile_ref: str
    trial_purpose: Literal["single_local_cleanroom_reconstruction_trial"]
    trial_cardinality_posture: Literal["single_trial_only"]
    official_programbench_posture: Literal["no_official_programbench_participation_by_pb_trial_0a"]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    model_ranking_posture: Literal["no_model_ranking_claimed_by_pb_trial_0a"]
    retry_authority_posture: Literal["no_retry_authority_granted_by_pb_trial_0a"]
    future_family_selection_posture: Literal["no_future_family_selected_by_pb_trial_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_trial_docket(self) -> "ProgrambenchLocalReconstructionTrialDocket":
        _ensure_sorted_unique(self.workbench_lineage_refs, field_name="workbench_lineage_refs")
        _ensure_sorted_unique(self.case_packet_refs, field_name="case_packet_refs")
        _ensure_no_forbidden_refs(self.workbench_lineage_refs, field_name="workbench_lineage_refs")
        _ensure_no_forbidden_refs(self.case_packet_refs, field_name="case_packet_refs")
        return self


class ProgrambenchLocalTrialExecutionRunbook(_TrialBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_TRIAL_EXECUTION_RUNBOOK_SCHEMA] = Field(alias="schema")
    trial_runbook_ref: str
    trial_docket_ref: str
    worker_input_packet_hash: str
    worker_visible_context_hash: str
    runbook_hash: str
    trial_input_materialization_policy_ref: str
    sandbox_policy_ref: str
    run_budget_ref: str
    allowed_step_rows: list[ProgrambenchLocalTrialAllowedStepRow] = Field(min_length=1)
    forbidden_step_rows: list[ProgrambenchLocalTrialForbiddenStepRow] = Field(min_length=1)
    capture_obligation_rows: list[ProgrambenchLocalTrialCaptureObligationRow] = Field(min_length=1)
    write_scope_refs: list[str] = Field(min_length=1)
    tool_manifest_refs: list[str] = Field(min_length=1)
    timeout_policy_ref: str
    environment_policy_ref: str
    sandbox_witness_requirement_refs: list[str] = Field(min_length=1)
    runbook_scope_posture: Literal["execution_plan_only_no_dispatch_by_pb_trial_0a"]
    dispatch_authority_posture: Literal["no_worker_dispatch_authority_granted_by_pb_trial_0a"]
    execution_authority_posture: Literal["no_command_execution_authority_granted_by_pb_trial_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_execution_runbook(self) -> "ProgrambenchLocalTrialExecutionRunbook":
        for field_name in (
            "worker_input_packet_hash",
            "worker_visible_context_hash",
            "runbook_hash",
        ):
            _ensure_hash(getattr(self, field_name), field_name=field_name)
        for field_name in (
            "write_scope_refs",
            "tool_manifest_refs",
            "sandbox_witness_requirement_refs",
        ):
            _ensure_sorted_unique(getattr(self, field_name), field_name=field_name)
        allowed_refs = [row.step_ref for row in self.allowed_step_rows]
        _ensure_sorted_unique(allowed_refs, field_name="allowed_step_refs")
        forbidden_refs = [row.forbidden_step_ref for row in self.forbidden_step_rows]
        _ensure_sorted_unique(forbidden_refs, field_name="forbidden_step_refs")
        capture_refs = [row.capture_obligation_ref for row in self.capture_obligation_rows]
        _ensure_sorted_unique(capture_refs, field_name="capture_obligation_refs")
        required_forbidden_steps = {
            "benchmark_scoring",
            "decompilation",
            "external_repo_lookup",
            "hidden_test_access",
            "internet_lookup",
            "model_ranking",
            "official_programbench_runner_contact",
            "official_submission",
            "original_source_lookup",
            "retry_dispatch",
        }
        observed_forbidden_steps = {row.forbidden_step_kind for row in self.forbidden_step_rows}
        missing = sorted(required_forbidden_steps - observed_forbidden_steps)
        if missing:
            raise ValueError(f"runbook missing forbidden step kinds: {missing}")
        witness_refs = set(self.sandbox_witness_requirement_refs)
        for row in self.capture_obligation_rows:
            missing_capture_witnesses = sorted(set(row.witness_requirement_refs) - witness_refs)
            if missing_capture_witnesses:
                raise ValueError(
                    "capture obligation witness refs must be declared by runbook: "
                    f"{missing_capture_witnesses}"
                )
        return self


class ProgrambenchLocalTrialSandboxReadinessReview(_TrialBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_TRIAL_SANDBOX_READINESS_REVIEW_SCHEMA] = Field(
        alias="schema"
    )
    sandbox_readiness_review_ref: str
    trial_docket_ref: str
    trial_runbook_ref: str
    sandbox_policy_ref: str
    run_budget_ref: str
    readiness_check_rows: list[ProgrambenchLocalTrialReadinessCheckRow] = Field(min_length=1)
    sandbox_witness_requirement_refs: list[str] = Field(min_length=1)
    network_readiness_posture: Literal["network_disabled"]
    source_lookup_readiness_posture: Literal["source_lookup_disabled"]
    decompilation_readiness_posture: Literal["decompilation_disabled"]
    docker_socket_readiness_posture: Literal["docker_socket_absent"]
    host_secret_readiness_posture: Literal["host_secrets_absent"]
    write_scope_readiness_posture: Literal["bounded_write_scope"]
    tool_manifest_readiness_posture: Literal["closed_tool_manifest", "tool_manifest_gap"]
    budget_readiness_posture: Literal["run_budget_bound"]
    readiness_posture: Literal[
        "blocked_by_budget_gap",
        "blocked_by_guardrail_gap",
        "blocked_by_missing_released_attempt_ref",
        "blocked_by_sandbox_gap",
        "blocked_by_tool_manifest_gap",
        "blocked_by_worker_input_hash_gap",
        "future_family_only",
        "ready_for_later_local_trial_execution_review",
    ]
    execution_authority_posture: Literal["no_command_execution_authority_granted_by_pb_trial_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_sandbox_readiness(
        self,
    ) -> "ProgrambenchLocalTrialSandboxReadinessReview":
        _ensure_sorted_unique(
            self.sandbox_witness_requirement_refs,
            field_name="sandbox_witness_requirement_refs",
        )
        check_refs = [row.readiness_check_ref for row in self.readiness_check_rows]
        _ensure_sorted_unique(check_refs, field_name="readiness_check_refs")
        check_kinds = {row.check_kind for row in self.readiness_check_rows}
        missing = sorted(_REQUIRED_READINESS_CHECK_KINDS - check_kinds)
        if missing:
            raise ValueError(f"sandbox readiness missing check kinds: {missing}")
        witness_refs = set(self.sandbox_witness_requirement_refs)
        missing_witnesses = sorted(
            {
                row.witness_requirement_ref
                for row in self.readiness_check_rows
                if row.witness_requirement_ref not in witness_refs
            }
        )
        if missing_witnesses:
            raise ValueError(
                f"readiness checks must map to declared witness refs: {missing_witnesses}"
            )
        if self.readiness_posture == "future_family_only":
            raise ValueError("sandbox readiness must review PB-TRIAL-0-A readiness only")
        if self.readiness_posture == "ready_for_later_local_trial_execution_review":
            blocked = [
                row.readiness_check_ref
                for row in self.readiness_check_rows
                if row.check_posture != "passed"
            ]
            if blocked:
                raise ValueError(f"ready sandbox reviews cannot carry blocked checks: {blocked}")
            if self.tool_manifest_readiness_posture != "closed_tool_manifest":
                raise ValueError("ready sandbox reviews require closed tool manifest posture")
        return self


class ProgrambenchLocalTrialNonAuthorityGuardrail(_TrialBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_TRIAL_NON_AUTHORITY_GUARDRAIL_SCHEMA] = Field(
        alias="schema"
    )
    trial_guardrail_ref: str
    trial_docket_ref: str
    forbidden_authority_rows: list[ProgrambenchLocalTrialForbiddenAuthorityRow] = Field(
        min_length=1
    )
    forbidden_future_artifact_kinds: list[str] = Field(min_length=1)
    official_programbench_non_authority_posture: Literal[
        "no_official_programbench_authority_by_pb_trial_0a"
    ]
    hidden_test_non_inference_posture: Literal["hidden_tests_not_visible_not_inference_evidence"]
    source_lookup_non_authority_posture: Literal["source_lookup_forbidden_by_pb_trial_0a"]
    submission_non_authority_posture: Literal["no_submission_authority_by_pb_trial_0a"]
    benchmark_truth_non_authority_posture: Literal["not_benchmark_truth"]
    model_ranking_non_authority_posture: Literal["no_model_ranking_claimed_by_pb_trial_0a"]
    retry_authority_posture: Literal["no_retry_authority_granted_by_pb_trial_0a"]
    future_family_selection_posture: Literal["no_future_family_selected_by_pb_trial_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_trial_guardrail(self) -> "ProgrambenchLocalTrialNonAuthorityGuardrail":
        row_refs = [row.forbidden_authority_ref for row in self.forbidden_authority_rows]
        _ensure_sorted_unique(row_refs, field_name="forbidden_authority_refs")
        required_authorities = {
            "benchmark_truth",
            "candidate_artifact_snapshot",
            "command_execution",
            "future_family_selection",
            "hidden_test_inference",
            "lifecycle_projection",
            "model_ranking",
            "official_programbench_participation",
            "official_submission",
            "outcome_audit",
            "retry_authority",
            "source_lookup",
            "worker_dispatch",
        }
        observed = {row.authority_kind for row in self.forbidden_authority_rows}
        missing = sorted(required_authorities - observed)
        if missing:
            raise ValueError(f"trial guardrail missing forbidden authority kinds: {missing}")
        _ensure_sorted_unique(
            self.forbidden_future_artifact_kinds,
            field_name="forbidden_future_artifact_kinds",
        )
        forbidden_future = set(self.forbidden_future_artifact_kinds)
        missing_future = sorted(
            PB_TRIAL_0A_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS - forbidden_future
        )
        if missing_future:
            raise ValueError(f"trial guardrail missing future artifact kinds: {missing_future}")
        current = sorted(PB_TRIAL_0A_ARTIFACT_KINDS & forbidden_future)
        if current:
            raise ValueError(f"trial guardrail cannot forbid current A artifact kinds: {current}")
        return self


class ProgrambenchLocalTrialWorkerDispatchRecord(_TrialBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_TRIAL_WORKER_DISPATCH_RECORD_SCHEMA] = Field(
        alias="schema"
    )
    trial_worker_dispatch_ref: str
    trial_docket_ref: str
    trial_runbook_ref: str
    sandbox_readiness_review_ref: str
    worker_profile_ref: str
    dispatch_index: int = Field(ge=1)
    dispatch_authority_ref: str
    sandbox_instance_ref: str
    sandbox_attestation_bundle_ref: str
    input_packet_materialization_hash: str
    worker_input_packet_hash: str
    worker_visible_context_hash: str
    tool_manifest_ref: str
    allowed_tool_manifest_hash: str
    forbidden_tool_manifest_hash: str
    dispatch_start_posture: Literal["started_under_released_pb_trial_0b_lock"]
    dispatch_completion_posture: Literal[
        "completed_with_execution_capture",
        "failed_with_execution_capture",
    ]
    tool_access_posture: Literal["released_tool_manifest_only"]
    network_access_posture: Literal["network_disabled"]
    source_lookup_posture: Literal["source_lookup_forbidden"]
    internet_lookup_posture: Literal["internet_lookup_forbidden"]
    decompilation_posture: Literal["decompilation_forbidden"]
    external_repo_access_posture: Literal["external_repo_access_forbidden"]
    docker_socket_access_posture: Literal["docker_socket_absent"]
    host_secret_access_posture: Literal["host_secrets_absent"]
    hidden_test_access_posture: Literal["hidden_tests_not_visible_not_accessed"]
    official_programbench_posture: Literal[
        "no_official_programbench_participation_by_pb_trial_0b"
    ]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    model_ranking_posture: Literal["no_model_ranking_claimed_by_pb_trial_0b"]
    official_submission_posture: Literal["no_official_submission_authority_by_pb_trial_0b"]
    retry_authority_posture: Literal["no_retry_authority_granted_by_pb_trial_0b"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_worker_dispatch(self) -> "ProgrambenchLocalTrialWorkerDispatchRecord":
        if self.dispatch_index != 1:
            raise ValueError(
                "PB-TRIAL-0-B allows exactly one dispatch specimen per docket, "
                f"found: {self.dispatch_index}"
            )
        if self.dispatch_authority_ref != _PB_TRIAL_0B_DISPATCH_AUTHORITY_REF:
            raise ValueError("dispatch authority must be the released PB-TRIAL-0-B lock")
        for field_name in (
            "input_packet_materialization_hash",
            "worker_input_packet_hash",
            "worker_visible_context_hash",
            "allowed_tool_manifest_hash",
            "forbidden_tool_manifest_hash",
        ):
            _ensure_hash(getattr(self, field_name), field_name=field_name)
        return self


class ProgrambenchLocalTrialExecutionCapture(_TrialBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_TRIAL_EXECUTION_CAPTURE_SCHEMA] = Field(alias="schema")
    trial_execution_capture_ref: str
    trial_worker_dispatch_ref: str
    trial_docket_ref: str
    captured_transcript_hash: str
    bounded_transcript_excerpt: str = Field(max_length=512)
    stdout_hash: str
    stdout_excerpt_bounded: str = Field(max_length=512)
    stderr_hash: str
    stderr_excerpt_bounded: str = Field(max_length=512)
    exit_code: int
    duration_ms: int = Field(ge=0)
    timeout_status: Literal["not_timed_out", "timed_out_with_capture"]
    full_output_capture_policy_ref: str
    worker_tool_call_manifest_ref: str
    declared_uncertainty_rows: list[ProgrambenchLocalTrialDeclaredUncertaintyRow] = Field(
        default_factory=list
    )
    forbidden_content_screening_rows: list[
        ProgrambenchLocalTrialForbiddenContentScreeningRow
    ] = Field(min_length=1)
    forbidden_content_screen_verdict: Literal[
        "blocked_excluded_derived",
        "blocked_forbidden_source",
        "blocked_hidden_evidence",
        "blocked_postmortem_only",
        "inconclusive_requires_review",
        "passed",
    ]
    forbidden_content_screening_posture: Literal[
        "screened_local_trial_output_for_forbidden_content"
    ]
    sandbox_witness_refs: list[str] = Field(min_length=1)
    execution_capture_posture: Literal["captured_local_trial_execution_only"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_execution_capture(self) -> "ProgrambenchLocalTrialExecutionCapture":
        for field_name in ("captured_transcript_hash", "stdout_hash", "stderr_hash"):
            _ensure_hash(getattr(self, field_name), field_name=field_name)
        _ensure_sorted_unique(self.sandbox_witness_refs, field_name="sandbox_witness_refs")
        screening_refs = [row.screening_ref for row in self.forbidden_content_screening_rows]
        _ensure_sorted_unique(screening_refs, field_name="forbidden_content_screening_rows")
        uncertainty_refs = [row.uncertainty_ref for row in self.declared_uncertainty_rows]
        _ensure_sorted_unique_allow_empty(
            uncertainty_refs,
            field_name="declared_uncertainty_rows",
        )
        blocked_rows = [
            row
            for row in self.forbidden_content_screening_rows
            if row.screening_posture == "blocked"
        ]
        if self.forbidden_content_screen_verdict == "passed":
            if blocked_rows:
                blocked_refs = [row.screening_ref for row in blocked_rows]
                raise ValueError(
                    f"passed forbidden-content screening cannot carry blocked rows: {blocked_refs}"
                )
            return self
        blocked_posture_kind = {
            "blocked_excluded_derived": "excluded_derived_content",
            "blocked_forbidden_source": "forbidden_source_content",
            "blocked_hidden_evidence": "hidden_evidence_content",
            "blocked_postmortem_only": "postmortem_only_content",
        }
        expected_kind = blocked_posture_kind.get(self.forbidden_content_screen_verdict)
        if expected_kind is None:
            if blocked_rows:
                raise ValueError("inconclusive screening posture cannot carry blocked rows")
            return self
        if not any(row.screening_kind == expected_kind for row in blocked_rows):
            raise ValueError(
                f"{self.forbidden_content_screen_verdict} requires a matching blocked row"
            )
        return self


class ProgrambenchLocalTrialCandidateArtifactSnapshot(_TrialBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_TRIAL_CANDIDATE_ARTIFACT_SNAPSHOT_SCHEMA] = Field(
        alias="schema"
    )
    candidate_artifact_snapshot_ref: str
    trial_execution_capture_ref: str
    trial_docket_ref: str
    write_scope_ref: str
    pre_state_manifest_ref: str
    post_state_manifest_ref: str
    fs_diff_ref: str
    snapshot_manifest_hash: str
    materialized_file_rows: list[ProgrambenchLocalTrialMaterializedFileRow] = Field(min_length=1)
    generated_file_hash_rows: list[ProgrambenchLocalTrialGeneratedFileHashRow] = Field(
        min_length=1
    )
    official_submission_posture: Literal["no_official_submission_authority_by_pb_trial_0b"]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    snapshot_inside_write_scope: Literal[True]
    snapshot_posture: Literal["local_candidate_snapshot_inside_released_write_scope"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_candidate_snapshot(self) -> "ProgrambenchLocalTrialCandidateArtifactSnapshot":
        _ensure_hash(self.snapshot_manifest_hash, field_name="snapshot_manifest_hash")
        file_refs = [row.materialized_file_ref for row in self.materialized_file_rows]
        _ensure_sorted_unique(file_refs, field_name="materialized_file_rows")
        path_refs = [row.path_ref for row in self.materialized_file_rows]
        _ensure_sorted_unique(path_refs, field_name="materialized_file_paths")
        hash_refs = [row.generated_file_hash_ref for row in self.generated_file_hash_rows]
        _ensure_sorted_unique(hash_refs, field_name="generated_file_hash_rows")
        hashed_file_refs = {row.materialized_file_ref for row in self.generated_file_hash_rows}
        if hashed_file_refs != set(file_refs):
            raise ValueError("generated file hash rows must cover exactly materialized files")
        row_write_scope_refs = {row.write_scope_ref for row in self.materialized_file_rows}
        if row_write_scope_refs != {self.write_scope_ref}:
            raise ValueError("materialized file rows must use the declared write scope")
        return self


class ProgrambenchLocalTrialLifecycleProjection(_TrialBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_TRIAL_LIFECYCLE_PROJECTION_SCHEMA] = Field(
        alias="schema"
    )
    trial_lifecycle_projection_ref: str
    trial_docket_ref: str
    trial_worker_dispatch_ref: str
    trial_execution_capture_ref: str
    candidate_artifact_snapshot_ref: str
    mapped_attempt_invocation_refs: list[str] = Field(min_length=1)
    mapped_attempt_output_capture_refs: list[str] = Field(min_length=1)
    mapped_attempt_materialization_refs: list[str] = Field(min_length=1)
    mapped_attempt_sandbox_trace_refs: list[str] = Field(min_length=1)
    projection_validation_rows: list[ProgrambenchLocalTrialProjectionValidationRow] = Field(
        min_length=1
    )
    projection_posture: Literal["projected_to_released_pb_attempt_lifecycle_refs"]
    new_evidence_law_posture: Literal["no_new_evidence_law_defined_by_pb_trial_0b"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_lifecycle_projection(self) -> "ProgrambenchLocalTrialLifecycleProjection":
        for field_name in (
            "mapped_attempt_invocation_refs",
            "mapped_attempt_output_capture_refs",
            "mapped_attempt_materialization_refs",
            "mapped_attempt_sandbox_trace_refs",
        ):
            _ensure_sorted_unique(getattr(self, field_name), field_name=field_name)
        row_refs = [row.projection_validation_ref for row in self.projection_validation_rows]
        _ensure_sorted_unique(row_refs, field_name="projection_validation_rows")
        required_validation_kinds = {
            "candidate_snapshot_mapped",
            "execution_capture_mapped",
            "mapped_attempt_lifecycle_refs_present",
            "new_evidence_law_absent",
            "worker_dispatch_mapped",
        }
        observed = {row.validation_kind for row in self.projection_validation_rows}
        missing = sorted(required_validation_kinds - observed)
        if missing:
            raise ValueError(f"lifecycle projection missing validation kinds: {missing}")
        return self


class ProgrambenchLocalTrialOutcomeAudit(_TrialBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_TRIAL_OUTCOME_AUDIT_SCHEMA] = Field(alias="schema")
    trial_outcome_audit_ref: str
    trial_docket_ref: str
    trial_runbook_ref: str
    sandbox_readiness_review_ref: str
    trial_worker_dispatch_ref: str
    trial_execution_capture_ref: str
    candidate_artifact_snapshot_ref: str
    trial_lifecycle_projection_ref: str
    local_evidence_rows: list[ProgrambenchLocalTrialLocalEvidenceRow] = Field(min_length=1)
    runbook_satisfaction_rows: list[ProgrambenchLocalTrialRunbookSatisfactionRow] = Field(
        min_length=1
    )
    sandbox_satisfaction_rows: list[ProgrambenchLocalTrialSandboxSatisfactionRow] = Field(
        min_length=1
    )
    carried_blocker_refs: list[str] = Field(default_factory=list)
    carried_warning_refs: list[str] = Field(default_factory=list)
    local_outcome_posture: Literal[
        "trial_blocked_by_lifecycle_projection_gap",
        "trial_blocked_by_output_capture_gap",
        "trial_blocked_by_sandbox_violation",
        "trial_inconclusive_local_only",
        "trial_locally_accepted",
        "trial_remand_recommended",
    ]
    hidden_test_equivalence_posture: Literal["no_hidden_test_equivalence_claimed_by_pb_trial_0c"]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    model_ranking_posture: Literal["no_model_ranking_claimed_by_pb_trial_0c"]
    official_submission_posture: Literal["no_official_submission_authority_by_pb_trial_0c"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_outcome_audit(self) -> "ProgrambenchLocalTrialOutcomeAudit":
        evidence_refs = [row.local_evidence_ref for row in self.local_evidence_rows]
        _ensure_sorted_unique(evidence_refs, field_name="local_evidence_rows")
        runbook_refs = [
            row.runbook_satisfaction_ref for row in self.runbook_satisfaction_rows
        ]
        _ensure_sorted_unique(runbook_refs, field_name="runbook_satisfaction_rows")
        sandbox_refs = [
            row.sandbox_satisfaction_ref for row in self.sandbox_satisfaction_rows
        ]
        _ensure_sorted_unique(sandbox_refs, field_name="sandbox_satisfaction_rows")
        _ensure_sorted_unique_allow_empty(
            self.carried_blocker_refs,
            field_name="carried_blocker_refs",
        )
        _ensure_sorted_unique_allow_empty(
            self.carried_warning_refs,
            field_name="carried_warning_refs",
        )
        if self.local_outcome_posture == "trial_locally_accepted":
            if self.carried_blocker_refs:
                raise ValueError("local acceptance cannot carry blockers")
            blocked_runbook = [
                row.runbook_satisfaction_ref
                for row in self.runbook_satisfaction_rows
                if row.satisfaction_posture != "passed"
            ]
            blocked_sandbox = [
                row.sandbox_satisfaction_ref
                for row in self.sandbox_satisfaction_rows
                if row.satisfaction_posture != "passed"
            ]
            if blocked_runbook or blocked_sandbox:
                raise ValueError(
                    "local acceptance requires passed runbook and sandbox satisfaction rows"
                )
            required_evidence = {
                "candidate_snapshot_inside_write_scope",
                "execution_capture_available",
                "lifecycle_projection_validated",
                "runbook_satisfaction_reviewed",
                "sandbox_satisfaction_reviewed",
            }
            observed = {row.evidence_kind for row in self.local_evidence_rows}
            missing = sorted(required_evidence - observed)
            if missing:
                raise ValueError(f"local acceptance missing evidence kinds: {missing}")
        elif not (self.carried_blocker_refs or self.carried_warning_refs):
            raise ValueError("non-accepted outcomes require blockers or warnings")
        return self


class ProgrambenchLocalTrialObservationSummary(_TrialBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_TRIAL_OBSERVATION_SUMMARY_SCHEMA] = Field(
        alias="schema"
    )
    trial_observation_summary_ref: str
    trial_outcome_audit_ref: str
    trial_docket_ref: str
    observed_input_packet_hash: str
    observed_candidate_snapshot_hash: str
    observed_result_posture: Literal[
        "trial_blocked_by_lifecycle_projection_gap",
        "trial_blocked_by_output_capture_gap",
        "trial_blocked_by_sandbox_violation",
        "trial_inconclusive_local_only",
        "trial_locally_accepted",
        "trial_remand_recommended",
    ]
    observation_rows: list[ProgrambenchLocalTrialObservationRow] = Field(min_length=1)
    limitation_rows: list[ProgrambenchLocalTrialLimitationRow] = Field(min_length=1)
    single_trial_scope_posture: Literal["single_local_trial_only_no_comparison"]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    model_ranking_posture: Literal["no_model_ranking_claimed_by_pb_trial_0c"]
    comparison_authority_posture: Literal["no_comparison_authority_granted_by_pb_trial_0c"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_observation_summary(self) -> "ProgrambenchLocalTrialObservationSummary":
        _ensure_hash(self.observed_input_packet_hash, field_name="observed_input_packet_hash")
        _ensure_hash(
            self.observed_candidate_snapshot_hash,
            field_name="observed_candidate_snapshot_hash",
        )
        observation_refs = [row.observation_ref for row in self.observation_rows]
        _ensure_sorted_unique(observation_refs, field_name="observation_rows")
        limitation_refs = [row.limitation_ref for row in self.limitation_rows]
        _ensure_sorted_unique(limitation_refs, field_name="limitation_rows")
        text = self.limitation_note.lower()
        leaked_markers = [marker for marker in _COMPARATIVE_LANGUAGE_MARKERS if marker in text]
        if leaked_markers:
            raise ValueError(
                "trial observation summary cannot contain comparative or benchmark language: "
                f"{leaked_markers}"
            )
        return self


class ProgrambenchLocalTrialRemandDecision(_TrialBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_TRIAL_REMAND_DECISION_SCHEMA] = Field(alias="schema")
    trial_remand_decision_ref: str
    trial_outcome_audit_ref: str
    trial_observation_summary_ref: str
    remand_decision_rows: list[ProgrambenchLocalTrialRemandDecisionRow] = Field(
        default_factory=list
    )
    remand_source_kinds: list[
        Literal[
            "local_candidate_snapshot_gap",
            "local_evidence_inconclusive",
            "local_execution_capture_gap",
            "local_lifecycle_projection_gap",
            "runbook_satisfaction_gap",
            "sandbox_readiness_or_application_gap",
            "worker_declared_uncertainty",
        ]
    ] = Field(default_factory=list)
    retry_authority_posture: Literal["no_retry_authority_granted_by_pb_trial_0c"]
    hidden_test_diagnostic_posture: Literal["hidden_tests_not_used_as_diagnostics"]
    source_lookup_posture: Literal["source_lookup_forbidden_by_pb_trial_0c"]
    future_family_selection_posture: Literal["no_future_family_selected_by_pb_trial_0c"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_remand_decision(self) -> "ProgrambenchLocalTrialRemandDecision":
        row_refs = [row.remand_decision_row_ref for row in self.remand_decision_rows]
        _ensure_sorted_unique_allow_empty(row_refs, field_name="remand_decision_rows")
        _ensure_sorted_unique_allow_empty(
            self.remand_source_kinds,
            field_name="remand_source_kinds",
        )
        row_kinds = sorted({row.remand_source_kind for row in self.remand_decision_rows})
        if row_kinds != self.remand_source_kinds:
            raise ValueError("remand source kinds must match remand decision rows")
        return self


class ProgrambenchLocalTrialFamilyCloseoutAlignment(_TrialBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_TRIAL_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA] = Field(
        alias="schema"
    )
    family_closeout_ref: str
    closed_family_ref: Literal["PB-TRIAL-0"]
    closed_slice_refs: list[str] = Field(min_length=1)
    trial_docket_refs: list[str] = Field(min_length=1)
    trial_execution_capture_refs: list[str] = Field(min_length=1)
    candidate_artifact_snapshot_refs: list[str] = Field(min_length=1)
    trial_outcome_audit_refs: list[str] = Field(min_length=1)
    trial_observation_summary_refs: list[str] = Field(min_length=1)
    trial_remand_decision_refs: list[str] = Field(min_length=1)
    family_alignment_posture: Literal["pb_trial_0_closed_local_trial_only"]
    official_programbench_non_authority_posture: Literal[
        "no_official_programbench_authority_by_pb_trial_0c"
    ]
    hidden_test_non_inference_posture: Literal["hidden_tests_not_inference_evidence"]
    benchmark_truth_non_authority_posture: Literal["not_benchmark_truth"]
    model_ranking_non_authority_posture: Literal["no_model_ranking_claimed_by_pb_trial_0c"]
    retry_authority_posture: Literal["no_retry_authority_granted_by_pb_trial_0c"]
    future_family_selection_posture: Literal["no_future_family_selected_by_pb_trial_0c"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_family_closeout(
        self,
    ) -> "ProgrambenchLocalTrialFamilyCloseoutAlignment":
        if self.closed_slice_refs != _PB_TRIAL_CLOSED_SLICES:
            raise ValueError("PB-TRIAL-0 closeout must close exactly A, B, and C")
        for field_name in (
            "trial_docket_refs",
            "trial_execution_capture_refs",
            "candidate_artifact_snapshot_refs",
            "trial_outcome_audit_refs",
            "trial_observation_summary_refs",
            "trial_remand_decision_refs",
        ):
            _ensure_sorted_unique(getattr(self, field_name), field_name=field_name)
        return self


def validate_pb_trial_0a_trial_bundle(
    *,
    attempt_request: ProgrambenchReconstructionAttemptRequest,
    worker_input_packet: ProgrambenchReconstructionAttemptWorkerInputPacket,
    dispatch_preflight: ProgrambenchReconstructionAttemptDispatchPreflight,
    attempt_guardrail: ProgrambenchReconstructionAttemptNonAuthorityGuardrail,
    prior_attempt_result_review: ProgrambenchReconstructionAttemptResultReview,
    attempt_family_closeout: ProgrambenchReconstructionAttemptFamilyCloseoutAlignment,
    trial_docket: ProgrambenchLocalReconstructionTrialDocket,
    execution_runbook: ProgrambenchLocalTrialExecutionRunbook,
    sandbox_readiness_review: ProgrambenchLocalTrialSandboxReadinessReview,
    trial_guardrail: ProgrambenchLocalTrialNonAuthorityGuardrail,
) -> None:
    if attempt_family_closeout.closed_family_ref != "PB-ATTEMPT-0":
        raise ValueError("trial docket requires released PB-ATTEMPT-0 closeout")
    if attempt_request.attempt_request_ref not in attempt_family_closeout.attempt_request_refs:
        raise ValueError("attempt closeout must release attempt request")
    if (
        prior_attempt_result_review.attempt_result_review_ref
        not in attempt_family_closeout.attempt_result_review_refs
    ):
        raise ValueError("attempt closeout must release result-review context ref")
    if prior_attempt_result_review.attempt_request_ref != attempt_request.attempt_request_ref:
        raise ValueError("prior attempt result review must reference attempt request")
    allowed_result_postures = {
        "attempt_inconclusive_local_only",
        "attempt_remand_required",
    }
    if prior_attempt_result_review.local_attempt_posture not in allowed_result_postures:
        raise ValueError(
            "trial docket requires remand or inconclusive PB-ATTEMPT result-review context"
        )

    if worker_input_packet.attempt_request_ref != attempt_request.attempt_request_ref:
        raise ValueError("worker input packet must reference attempt request")
    if dispatch_preflight.attempt_request_ref != attempt_request.attempt_request_ref:
        raise ValueError("dispatch preflight must reference attempt request")
    if dispatch_preflight.worker_input_packet_ref != worker_input_packet.worker_input_packet_ref:
        raise ValueError("dispatch preflight must reference worker input packet")
    if attempt_guardrail.attempt_request_ref != attempt_request.attempt_request_ref:
        raise ValueError("attempt guardrail must reference attempt request")
    if dispatch_preflight.preflight_posture != "preflight_passed_for_later_local_attempt_review":
        raise ValueError("trial docket requires passed PB-ATTEMPT-0 dispatch preflight")

    if trial_docket.attempt_request_ref != attempt_request.attempt_request_ref:
        raise ValueError("trial docket must reference attempt request")
    if trial_docket.worker_input_packet_ref != worker_input_packet.worker_input_packet_ref:
        raise ValueError("trial docket must reference worker input packet")
    if trial_docket.dispatch_preflight_ref != dispatch_preflight.dispatch_preflight_ref:
        raise ValueError("trial docket must reference dispatch preflight")
    if trial_docket.attempt_guardrail_ref != attempt_guardrail.guardrail_ref:
        raise ValueError("trial docket must reference attempt guardrail")
    if trial_docket.prior_attempt_result_review_context_ref != (
        prior_attempt_result_review.attempt_result_review_ref
    ):
        raise ValueError("trial docket must reference prior attempt result-review context")
    if trial_docket.attempt_family_closeout_ref != attempt_family_closeout.family_closeout_ref:
        raise ValueError("trial docket must reference attempt family closeout")
    if trial_docket.worker_profile_ref != attempt_request.worker_profile_ref:
        raise ValueError("trial docket must preserve worker profile")

    if execution_runbook.trial_docket_ref != trial_docket.trial_docket_ref:
        raise ValueError("execution runbook must reference trial docket")
    if execution_runbook.worker_input_packet_hash != (
        worker_input_packet.worker_input_manifest_hash
    ):
        raise ValueError("runbook worker input hash must match worker input packet")
    if execution_runbook.sandbox_policy_ref != attempt_request.sandbox_policy_ref:
        raise ValueError("runbook must preserve attempt sandbox policy")
    if execution_runbook.run_budget_ref != attempt_request.run_budget_ref:
        raise ValueError("runbook must preserve attempt run budget")
    if execution_runbook.runbook_scope_posture != (
        "execution_plan_only_no_dispatch_by_pb_trial_0a"
    ):
        raise ValueError("runbook must remain execution-plan-only")

    if sandbox_readiness_review.trial_docket_ref != trial_docket.trial_docket_ref:
        raise ValueError("sandbox readiness review must reference trial docket")
    if sandbox_readiness_review.trial_runbook_ref != execution_runbook.trial_runbook_ref:
        raise ValueError("sandbox readiness review must reference runbook")
    if sandbox_readiness_review.sandbox_policy_ref != execution_runbook.sandbox_policy_ref:
        raise ValueError("sandbox readiness review must preserve sandbox policy")
    if sandbox_readiness_review.run_budget_ref != execution_runbook.run_budget_ref:
        raise ValueError("sandbox readiness review must preserve run budget")
    if sandbox_readiness_review.sandbox_witness_requirement_refs != (
        execution_runbook.sandbox_witness_requirement_refs
    ):
        raise ValueError("sandbox readiness witnesses must match runbook witness requirements")

    if trial_guardrail.trial_docket_ref != trial_docket.trial_docket_ref:
        raise ValueError("trial guardrail must reference trial docket")


def validate_pb_trial_0b_execution_bundle(
    *,
    trial_docket: ProgrambenchLocalReconstructionTrialDocket,
    execution_runbook: ProgrambenchLocalTrialExecutionRunbook,
    sandbox_readiness_review: ProgrambenchLocalTrialSandboxReadinessReview,
    trial_guardrail: ProgrambenchLocalTrialNonAuthorityGuardrail,
    released_attempt_worker_invocation: ProgrambenchReconstructionAttemptWorkerInvocationRecord,
    released_attempt_output_capture: ProgrambenchReconstructionAttemptOutputCapture,
    released_attempt_candidate_materialization: (
        ProgrambenchReconstructionAttemptCandidateMaterialization
    ),
    released_attempt_sandbox_trace: ProgrambenchReconstructionAttemptSandboxApplicationTrace,
    worker_dispatch_record: ProgrambenchLocalTrialWorkerDispatchRecord,
    execution_capture: ProgrambenchLocalTrialExecutionCapture,
    candidate_artifact_snapshot: ProgrambenchLocalTrialCandidateArtifactSnapshot,
    lifecycle_projection: ProgrambenchLocalTrialLifecycleProjection,
) -> None:
    if execution_runbook.trial_docket_ref != trial_docket.trial_docket_ref:
        raise ValueError("execution runbook must reference trial docket")
    if sandbox_readiness_review.trial_docket_ref != trial_docket.trial_docket_ref:
        raise ValueError("sandbox readiness review must reference trial docket")
    if sandbox_readiness_review.trial_runbook_ref != execution_runbook.trial_runbook_ref:
        raise ValueError("sandbox readiness review must reference runbook")
    if trial_guardrail.trial_docket_ref != trial_docket.trial_docket_ref:
        raise ValueError("trial guardrail must reference trial docket")
    if sandbox_readiness_review.readiness_posture != (
        "ready_for_later_local_trial_execution_review"
    ):
        raise ValueError("PB-TRIAL-0-B dispatch requires ready A sandbox readiness")

    if worker_dispatch_record.trial_docket_ref != trial_docket.trial_docket_ref:
        raise ValueError("worker dispatch must reference trial docket")
    if worker_dispatch_record.trial_runbook_ref != execution_runbook.trial_runbook_ref:
        raise ValueError("worker dispatch must reference trial runbook")
    if worker_dispatch_record.sandbox_readiness_review_ref != (
        sandbox_readiness_review.sandbox_readiness_review_ref
    ):
        raise ValueError("worker dispatch must reference sandbox readiness review")
    if worker_dispatch_record.worker_profile_ref != trial_docket.worker_profile_ref:
        raise ValueError("worker dispatch must preserve trial worker profile")
    if worker_dispatch_record.worker_input_packet_hash != (
        execution_runbook.worker_input_packet_hash
    ):
        raise ValueError("worker dispatch input hash must match execution runbook")
    if worker_dispatch_record.worker_visible_context_hash != (
        execution_runbook.worker_visible_context_hash
    ):
        raise ValueError("worker dispatch context hash must match execution runbook")
    if worker_dispatch_record.tool_manifest_ref not in execution_runbook.tool_manifest_refs:
        raise ValueError("worker dispatch tool manifest must be released by runbook")

    if execution_capture.trial_worker_dispatch_ref != (
        worker_dispatch_record.trial_worker_dispatch_ref
    ):
        raise ValueError("execution capture must reference worker dispatch")
    if execution_capture.trial_docket_ref != trial_docket.trial_docket_ref:
        raise ValueError("execution capture must reference trial docket")
    if set(execution_capture.sandbox_witness_refs) != set(
        sandbox_readiness_review.sandbox_witness_requirement_refs
    ):
        raise ValueError("execution capture sandbox witnesses must match A readiness witnesses")
    if execution_capture.forbidden_content_screen_verdict != "passed":
        raise ValueError("candidate snapshots require passed forbidden-content screening")

    if candidate_artifact_snapshot.trial_execution_capture_ref != (
        execution_capture.trial_execution_capture_ref
    ):
        raise ValueError("candidate snapshot must reference execution capture")
    if candidate_artifact_snapshot.trial_docket_ref != trial_docket.trial_docket_ref:
        raise ValueError("candidate snapshot must reference trial docket")
    if candidate_artifact_snapshot.write_scope_ref not in execution_runbook.write_scope_refs:
        raise ValueError("candidate snapshot write scope must be released by runbook")
    if not candidate_artifact_snapshot.snapshot_inside_write_scope:
        raise ValueError("candidate snapshot must stay inside released write scope")

    if lifecycle_projection.trial_docket_ref != trial_docket.trial_docket_ref:
        raise ValueError("lifecycle projection must reference trial docket")
    if lifecycle_projection.trial_worker_dispatch_ref != (
        worker_dispatch_record.trial_worker_dispatch_ref
    ):
        raise ValueError("lifecycle projection must reference worker dispatch")
    if lifecycle_projection.trial_execution_capture_ref != (
        execution_capture.trial_execution_capture_ref
    ):
        raise ValueError("lifecycle projection must reference execution capture")
    if lifecycle_projection.candidate_artifact_snapshot_ref != (
        candidate_artifact_snapshot.candidate_artifact_snapshot_ref
    ):
        raise ValueError("lifecycle projection must reference candidate snapshot")
    if lifecycle_projection.new_evidence_law_posture != (
        "no_new_evidence_law_defined_by_pb_trial_0b"
    ):
        raise ValueError("lifecycle projection cannot define new evidence law")
    if lifecycle_projection.mapped_attempt_invocation_refs != [
        released_attempt_worker_invocation.worker_invocation_ref
    ]:
        raise ValueError("lifecycle projection must map released PB-ATTEMPT invocation ref")
    if lifecycle_projection.mapped_attempt_output_capture_refs != [
        released_attempt_output_capture.output_capture_ref
    ]:
        raise ValueError("lifecycle projection must map released PB-ATTEMPT output capture ref")
    if lifecycle_projection.mapped_attempt_materialization_refs != [
        released_attempt_candidate_materialization.candidate_materialization_ref
    ]:
        raise ValueError("lifecycle projection must map released PB-ATTEMPT materialization ref")
    if lifecycle_projection.mapped_attempt_sandbox_trace_refs != [
        released_attempt_sandbox_trace.sandbox_application_trace_ref
    ]:
        raise ValueError("lifecycle projection must map released PB-ATTEMPT sandbox trace ref")


def validate_pb_trial_0c_closeout_bundle(
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
    if execution_runbook.trial_docket_ref != trial_docket.trial_docket_ref:
        raise ValueError("execution runbook must reference trial docket")
    if sandbox_readiness_review.trial_docket_ref != trial_docket.trial_docket_ref:
        raise ValueError("sandbox readiness review must reference trial docket")
    if trial_guardrail.trial_docket_ref != trial_docket.trial_docket_ref:
        raise ValueError("trial guardrail must reference trial docket")
    if worker_dispatch_record.trial_docket_ref != trial_docket.trial_docket_ref:
        raise ValueError("worker dispatch must reference trial docket")
    if execution_capture.trial_docket_ref != trial_docket.trial_docket_ref:
        raise ValueError("execution capture must reference trial docket")
    if candidate_artifact_snapshot.trial_docket_ref != trial_docket.trial_docket_ref:
        raise ValueError("candidate snapshot must reference trial docket")
    if lifecycle_projection.trial_docket_ref != trial_docket.trial_docket_ref:
        raise ValueError("lifecycle projection must reference trial docket")

    if outcome_audit.trial_docket_ref != trial_docket.trial_docket_ref:
        raise ValueError("outcome audit must reference trial docket")
    if outcome_audit.trial_runbook_ref != execution_runbook.trial_runbook_ref:
        raise ValueError("outcome audit must reference trial runbook")
    if outcome_audit.sandbox_readiness_review_ref != (
        sandbox_readiness_review.sandbox_readiness_review_ref
    ):
        raise ValueError("outcome audit must reference sandbox readiness review")
    if outcome_audit.trial_worker_dispatch_ref != (
        worker_dispatch_record.trial_worker_dispatch_ref
    ):
        raise ValueError("outcome audit must reference worker dispatch")
    if outcome_audit.trial_execution_capture_ref != execution_capture.trial_execution_capture_ref:
        raise ValueError("outcome audit must reference execution capture")
    if outcome_audit.candidate_artifact_snapshot_ref != (
        candidate_artifact_snapshot.candidate_artifact_snapshot_ref
    ):
        raise ValueError("outcome audit must reference candidate snapshot")
    if outcome_audit.trial_lifecycle_projection_ref != (
        lifecycle_projection.trial_lifecycle_projection_ref
    ):
        raise ValueError("outcome audit must reference lifecycle projection")

    if outcome_audit.local_outcome_posture == "trial_locally_accepted":
        if not candidate_artifact_snapshot.snapshot_inside_write_scope:
            raise ValueError("local acceptance requires snapshot inside released write scope")
        if candidate_artifact_snapshot.write_scope_ref not in execution_runbook.write_scope_refs:
            raise ValueError("local acceptance requires released write scope")
        if lifecycle_projection.projection_posture != (
            "projected_to_released_pb_attempt_lifecycle_refs"
        ):
            raise ValueError("local acceptance requires lifecycle projection")
        if lifecycle_projection.new_evidence_law_posture != (
            "no_new_evidence_law_defined_by_pb_trial_0b"
        ):
            raise ValueError("local acceptance requires no new evidence law")
        validation_kinds = {
            row.validation_kind for row in lifecycle_projection.projection_validation_rows
        }
        required_validation = {
            "candidate_snapshot_mapped",
            "execution_capture_mapped",
            "mapped_attempt_lifecycle_refs_present",
            "new_evidence_law_absent",
            "worker_dispatch_mapped",
        }
        missing_validation = sorted(required_validation - validation_kinds)
        if missing_validation:
            raise ValueError(
                "local acceptance requires lifecycle projection validation: "
                f"{missing_validation}"
            )
        if execution_capture.forbidden_content_screen_verdict != "passed":
            raise ValueError("local acceptance requires passed output screening")

    if observation_summary.trial_outcome_audit_ref != outcome_audit.trial_outcome_audit_ref:
        raise ValueError("observation summary must reference outcome audit")
    if observation_summary.trial_docket_ref != trial_docket.trial_docket_ref:
        raise ValueError("observation summary must reference trial docket")
    if observation_summary.observed_result_posture != outcome_audit.local_outcome_posture:
        raise ValueError("observation summary result posture must match outcome audit")
    if observation_summary.observed_input_packet_hash != execution_runbook.worker_input_packet_hash:
        raise ValueError("observation summary must preserve observed input packet hash")
    if observation_summary.observed_candidate_snapshot_hash != (
        candidate_artifact_snapshot.snapshot_manifest_hash
    ):
        raise ValueError("observation summary must preserve candidate snapshot hash")

    if remand_decision.trial_outcome_audit_ref != outcome_audit.trial_outcome_audit_ref:
        raise ValueError("remand decision must reference outcome audit")
    if remand_decision.trial_observation_summary_ref != (
        observation_summary.trial_observation_summary_ref
    ):
        raise ValueError("remand decision must reference observation summary")
    if outcome_audit.local_outcome_posture == "trial_locally_accepted" and (
        remand_decision.remand_decision_rows or remand_decision.remand_source_kinds
    ):
        raise ValueError("local acceptance cannot carry remand pressure")
    if outcome_audit.local_outcome_posture != "trial_locally_accepted" and not (
        remand_decision.remand_decision_rows
    ):
        raise ValueError("non-accepted outcomes require local remand rows")

    if family_closeout.trial_docket_refs != [trial_docket.trial_docket_ref]:
        raise ValueError("family closeout must close exactly this trial docket")
    if family_closeout.trial_execution_capture_refs != [
        execution_capture.trial_execution_capture_ref
    ]:
        raise ValueError("family closeout must reference execution capture")
    if family_closeout.candidate_artifact_snapshot_refs != [
        candidate_artifact_snapshot.candidate_artifact_snapshot_ref
    ]:
        raise ValueError("family closeout must reference candidate snapshot")
    if family_closeout.trial_outcome_audit_refs != [outcome_audit.trial_outcome_audit_ref]:
        raise ValueError("family closeout must reference outcome audit")
    if family_closeout.trial_observation_summary_refs != [
        observation_summary.trial_observation_summary_ref
    ]:
        raise ValueError("family closeout must reference observation summary")
    if family_closeout.trial_remand_decision_refs != [
        remand_decision.trial_remand_decision_ref
    ]:
        raise ValueError("family closeout must reference remand decision")
