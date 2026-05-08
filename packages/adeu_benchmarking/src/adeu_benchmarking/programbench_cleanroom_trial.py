from __future__ import annotations

import re
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

from .programbench_cleanroom_attempt import (
    ProgrambenchReconstructionAttemptDispatchPreflight,
    ProgrambenchReconstructionAttemptFamilyCloseoutAlignment,
    ProgrambenchReconstructionAttemptNonAuthorityGuardrail,
    ProgrambenchReconstructionAttemptRequest,
    ProgrambenchReconstructionAttemptResultReview,
    ProgrambenchReconstructionAttemptWorkerInputPacket,
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
        _ensure_non_empty_unique(allowed_refs, field_name="allowed_step_refs")
        forbidden_refs = [row.forbidden_step_ref for row in self.forbidden_step_rows]
        _ensure_non_empty_unique(forbidden_refs, field_name="forbidden_step_refs")
        capture_refs = [row.capture_obligation_ref for row in self.capture_obligation_rows]
        _ensure_non_empty_unique(capture_refs, field_name="capture_obligation_refs")
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
        _ensure_non_empty_unique(check_refs, field_name="readiness_check_refs")
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
    if set(sandbox_readiness_review.sandbox_witness_requirement_refs) != set(
        execution_runbook.sandbox_witness_requirement_refs
    ):
        raise ValueError("sandbox readiness witnesses must match runbook witness requirements")

    if trial_guardrail.trial_docket_ref != trial_docket.trial_docket_ref:
        raise ValueError("trial guardrail must reference trial docket")
