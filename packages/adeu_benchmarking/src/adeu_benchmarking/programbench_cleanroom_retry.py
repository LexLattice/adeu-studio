from __future__ import annotations

import re
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

from .programbench_cleanroom_trial import (
    ProgrambenchLocalTrialCandidateArtifactSnapshot,
    ProgrambenchLocalTrialFamilyCloseoutAlignment,
    ProgrambenchLocalTrialLifecycleProjection,
    ProgrambenchLocalTrialObservationSummary,
    ProgrambenchLocalTrialOutcomeAudit,
    ProgrambenchLocalTrialRemandDecision,
    ProgrambenchLocalTrialWorkerDispatchRecord,
)

MODEL_CONFIG = ConfigDict(
    extra="forbid",
    frozen=True,
    populate_by_name=True,
    protected_namespaces=(),
)

PROGRAMBENCH_LOCAL_RETRY_REQUEST_SCHEMA = "programbench_local_retry_request@1"
PROGRAMBENCH_LOCAL_RETRY_LINEAGE_REGISTRY_SCHEMA = (
    "programbench_local_retry_lineage_registry@1"
)
PROGRAMBENCH_TRIAL_REMAND_SOURCE_INDEX_SCHEMA = "programbench_trial_remand_source_index@1"
PROGRAMBENCH_LOCAL_RETRY_ELIGIBILITY_REVIEW_SCHEMA = (
    "programbench_local_retry_eligibility_review@1"
)
PROGRAMBENCH_LOCAL_RETRY_SCOPE_CONTRACT_SCHEMA = "programbench_local_retry_scope_contract@1"
PROGRAMBENCH_LOCAL_RETRY_NON_AUTHORITY_GUARDRAIL_SCHEMA = (
    "programbench_local_retry_non_authority_guardrail@1"
)

PROGRAMBENCH_LOCAL_RETRY_DISPATCH_RECORD_SCHEMA = "programbench_local_retry_dispatch_record@1"
PROGRAMBENCH_LOCAL_RETRY_EXECUTION_CAPTURE_SCHEMA = "programbench_local_retry_execution_capture@1"
PROGRAMBENCH_LOCAL_RETRY_CANDIDATE_DELTA_SNAPSHOT_SCHEMA = (
    "programbench_local_retry_candidate_delta_snapshot@1"
)
PROGRAMBENCH_LOCAL_RETRY_LIFECYCLE_PROJECTION_SCHEMA = (
    "programbench_local_retry_lifecycle_projection@1"
)
PROGRAMBENCH_LOCAL_RETRY_SANDBOX_APPLICATION_TRACE_SCHEMA = (
    "programbench_local_retry_sandbox_application_trace@1"
)
PROGRAMBENCH_LOCAL_RETRY_OUTCOME_AUDIT_SCHEMA = "programbench_local_retry_outcome_audit@1"
PROGRAMBENCH_LOCAL_RETRY_DELTA_OBSERVATION_SUMMARY_SCHEMA = (
    "programbench_local_retry_delta_observation_summary@1"
)
PROGRAMBENCH_LOCAL_RETRY_REMAND_SETTLEMENT_SCHEMA = (
    "programbench_local_retry_remand_settlement@1"
)
PROGRAMBENCH_LOCAL_RETRY_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA = (
    "programbench_local_retry_family_closeout_alignment@1"
)

PB_RETRY_0A_ARTIFACT_KINDS = {
    PROGRAMBENCH_LOCAL_RETRY_REQUEST_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_LINEAGE_REGISTRY_SCHEMA,
    PROGRAMBENCH_TRIAL_REMAND_SOURCE_INDEX_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_ELIGIBILITY_REVIEW_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_SCOPE_CONTRACT_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_NON_AUTHORITY_GUARDRAIL_SCHEMA,
}
PB_RETRY_0B_ARTIFACT_KINDS = {
    PROGRAMBENCH_LOCAL_RETRY_DISPATCH_RECORD_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_EXECUTION_CAPTURE_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_CANDIDATE_DELTA_SNAPSHOT_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_LIFECYCLE_PROJECTION_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_SANDBOX_APPLICATION_TRACE_SCHEMA,
}
PB_RETRY_0C_ARTIFACT_KINDS = {
    PROGRAMBENCH_LOCAL_RETRY_OUTCOME_AUDIT_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_DELTA_OBSERVATION_SUMMARY_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_REMAND_SETTLEMENT_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
}
PB_RETRY_0A_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS = (
    PB_RETRY_0B_ARTIFACT_KINDS | PB_RETRY_0C_ARTIFACT_KINDS
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
    "source-lookup",
)
_FORBIDDEN_CONTENT_MARKERS = (
    "benchmark score",
    "decompilation",
    "docker socket",
    "external repo",
    "hidden test",
    "host secret",
    "internet lookup",
    "model ranking",
    "official evaluator",
    "original source",
    "source lookup",
)
_ALLOWED_RETRY_RATIONALE_KINDS = {
    "lifecycle_projection_gap",
    "local_candidate_snapshot_gap",
    "local_evidence_inconclusive",
    "local_output_capture_gap",
    "local_probe_failure",
    "runbook_satisfaction_gap",
    "worker_declared_uncertainty",
}
_PB_RETRY_0B_DISPATCH_AUTHORITY_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS258.md"
_PASSED_FORBIDDEN_CONTENT_SCREEN_VERDICT = "passed"


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
        raise ValueError(f"{field_name} contains forbidden retry evidence refs: {leaked}")


def _ensure_no_forbidden_content(value: str, *, field_name: str) -> None:
    lowered = value.lower()
    leaked = [marker for marker in _FORBIDDEN_CONTENT_MARKERS if marker in lowered]
    if leaked:
        raise ValueError(f"{field_name} contains forbidden retry content markers: {leaked}")


class _RetryBase(BaseModel):
    model_config = MODEL_CONFIG


class ProgrambenchLocalRetrySequenceRow(_RetryBase):
    retry_sequence_ref: str
    retry_request_ref: str
    retry_sequence_index: int = Field(ge=1)
    sequence_posture: Literal["single_pb_retry_0_candidate"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_sequence(self) -> "ProgrambenchLocalRetrySequenceRow":
        if self.retry_sequence_index != 1:
            raise ValueError("PB-RETRY-0-A allows only retry_sequence_index = 1")
        return self


class ProgrambenchTrialRemandSourceRow(_RetryBase):
    remand_source_ref: str
    remand_source_kind: Literal[
        "lifecycle_projection_gap",
        "local_candidate_snapshot_gap",
        "local_evidence_inconclusive",
        "local_output_capture_gap",
        "local_probe_failure",
        "runbook_satisfaction_gap",
        "worker_declared_uncertainty",
    ]
    retryability_posture: Literal[
        "blocked",
        "forbidden",
        "local_non_retryable",
        "local_retryable",
        "support_only",
    ]
    source_refs: list[str] = Field(min_length=1)
    source_content_shape_posture: Literal["category_only_no_source_identifying_content"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_remand_source_row(self) -> "ProgrambenchTrialRemandSourceRow":
        _ensure_sorted_unique(self.source_refs, field_name="remand source_refs")
        _ensure_no_forbidden_refs(self.source_refs, field_name="remand source_refs")
        _ensure_no_forbidden_content(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalRetryRationaleRow(_RetryBase):
    retry_rationale_ref: str
    retry_rationale_kind: Literal[
        "lifecycle_projection_gap",
        "local_candidate_snapshot_gap",
        "local_evidence_inconclusive",
        "local_output_capture_gap",
        "local_probe_failure",
        "runbook_satisfaction_gap",
        "worker_declared_uncertainty",
    ]
    rationale_posture: Literal["local_retry_rationale_only_no_dispatch_authority"]
    source_refs: list[str] = Field(min_length=1)
    content_shape_posture: Literal["category_only_no_source_identifying_content"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_retry_rationale_row(self) -> "ProgrambenchLocalRetryRationaleRow":
        _ensure_sorted_unique(self.source_refs, field_name="retry rationale source_refs")
        _ensure_no_forbidden_refs(self.source_refs, field_name="retry rationale source_refs")
        _ensure_no_forbidden_content(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalRetryAllowedActionRow(_RetryBase):
    allowed_action_ref: str
    action_kind: Literal[
        "local_retry_instruction",
        "remand_focused_obligation",
        "worker_uncertainty_clarification",
    ]
    action_scope_posture: Literal["allowed_for_later_pb_retry_0b_only"]
    source_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_allowed_action(self) -> "ProgrambenchLocalRetryAllowedActionRow":
        _ensure_sorted_unique(self.source_refs, field_name="allowed action source_refs")
        _ensure_no_forbidden_refs(self.source_refs, field_name="allowed action source_refs")
        return self


class ProgrambenchLocalRetryForbiddenActionRow(_RetryBase):
    forbidden_action_ref: str
    action_kind: Literal[
        "add_evidence_source",
        "add_tool",
        "benchmark_scoring",
        "decompilation",
        "docker_socket_access",
        "external_repo_lookup",
        "hidden_test_access",
        "host_secret_access",
        "internet_lookup",
        "model_ranking",
        "network_access",
        "official_submission",
        "source_lookup",
        "widen_write_scope",
    ]
    forbiddance_posture: Literal["forbidden_by_pb_retry_0a"]
    limitation_note: str


class ProgrambenchLocalRetryForbiddenAuthorityRow(_RetryBase):
    forbidden_authority_ref: str
    authority_kind: Literal[
        "benchmark_truth",
        "command_execution",
        "future_family_selection",
        "hidden_test_inference",
        "model_ranking",
        "multi_attempt_comparison",
        "official_programbench_participation",
        "official_submission",
        "remand_settlement",
        "retry_candidate_delta_snapshot",
        "retry_dispatch",
        "retry_execution_capture",
        "retry_lifecycle_projection",
        "retry_outcome_audit",
        "second_retry",
        "source_lookup",
    ]
    forbiddance_posture: Literal["forbidden_by_pb_retry_0a"]
    limitation_note: str


class ProgrambenchLocalRetryRequest(_RetryBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_RETRY_REQUEST_SCHEMA] = Field(alias="schema")
    retry_request_ref: str
    retry_lineage_ref: str
    trial_lineage_ref: str
    source_trial_ref: str
    source_remand_decision_ref: str
    retry_lineage_registry_ref: str
    prior_retry_request_refs: list[str] = Field(default_factory=list)
    retry_sequence_index: int = Field(ge=1)
    trial_outcome_audit_ref: str
    trial_observation_summary_ref: str
    trial_remand_decision_ref: str
    trial_family_closeout_ref: str
    requested_retry_horizon: Literal["later_local_retry_dispatch_review"]
    retry_depth_limit: int = Field(ge=1)
    retry_uniqueness_posture: Literal["one_eligible_retry_for_trial_remand"]
    retry_dispatch_authority_posture: Literal[
        "no_retry_dispatch_authority_granted_by_pb_retry_0a"
    ]
    official_benchmark_authority_posture: Literal[
        "no_official_programbench_authority_granted_by_pb_retry_0a"
    ]
    model_ranking_posture: Literal["no_model_ranking_claimed_by_pb_retry_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_retry_request(self) -> "ProgrambenchLocalRetryRequest":
        _ensure_sorted_unique_allow_empty(
            self.prior_retry_request_refs,
            field_name="prior_retry_request_refs",
        )
        if self.retry_sequence_index != 1:
            raise ValueError("PB-RETRY-0-A allows only retry_sequence_index = 1")
        if self.retry_depth_limit != 1:
            raise ValueError("PB-RETRY-0-A allows only retry_depth_limit = 1")
        if self.source_remand_decision_ref != self.trial_remand_decision_ref:
            raise ValueError("source_remand_decision_ref must match trial_remand_decision_ref")
        return self


class ProgrambenchLocalRetryLineageRegistry(_RetryBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_RETRY_LINEAGE_REGISTRY_SCHEMA] = Field(alias="schema")
    retry_lineage_registry_ref: str
    trial_lineage_ref: str
    trial_remand_decision_ref: str
    existing_retry_request_refs: list[str] = Field(default_factory=list)
    eligible_retry_request_refs: list[str] = Field(min_length=1)
    retry_sequence_rows: list[ProgrambenchLocalRetrySequenceRow] = Field(min_length=1)
    retry_uniqueness_posture: Literal["one_eligible_retry_for_trial_remand"]
    retry_chain_authority_posture: Literal["no_retry_chain_authority_granted_by_pb_retry_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_lineage_registry(self) -> "ProgrambenchLocalRetryLineageRegistry":
        _ensure_sorted_unique_allow_empty(
            self.existing_retry_request_refs,
            field_name="existing_retry_request_refs",
        )
        _ensure_sorted_unique(
            self.eligible_retry_request_refs,
            field_name="eligible_retry_request_refs",
        )
        if len(self.eligible_retry_request_refs) != 1:
            raise ValueError("PB-RETRY-0-A allows exactly one eligible retry request per remand")
        row_refs = [row.retry_sequence_ref for row in self.retry_sequence_rows]
        _ensure_sorted_unique(row_refs, field_name="retry_sequence_rows")
        row_request_refs = [row.retry_request_ref for row in self.retry_sequence_rows]
        if row_request_refs != self.eligible_retry_request_refs:
            raise ValueError("retry sequence rows must match eligible retry request refs")
        return self


class ProgrambenchTrialRemandSourceIndex(_RetryBase):
    schema_id: Literal[PROGRAMBENCH_TRIAL_REMAND_SOURCE_INDEX_SCHEMA] = Field(alias="schema")
    remand_source_index_ref: str
    retry_request_ref: str
    trial_remand_decision_ref: str
    remand_source_rows: list[ProgrambenchTrialRemandSourceRow] = Field(min_length=1)
    retry_rationale_rows: list[ProgrambenchLocalRetryRationaleRow] = Field(min_length=1)
    local_retryable_source_refs: list[str] = Field(min_length=1)
    local_non_retryable_source_refs: list[str] = Field(default_factory=list)
    blocked_source_refs: list[str] = Field(default_factory=list)
    forbidden_source_refs: list[str] = Field(default_factory=list)
    support_only_source_refs: list[str] = Field(default_factory=list)
    source_visibility_posture: Literal["local_remand_sources_only"]
    hidden_or_forbidden_exposure_posture: Literal[
        "hidden_and_forbidden_sources_not_exposed_or_summarized"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_source_index(self) -> "ProgrambenchTrialRemandSourceIndex":
        row_refs = [row.remand_source_ref for row in self.remand_source_rows]
        _ensure_sorted_unique(row_refs, field_name="remand_source_rows")
        rationale_refs = [row.retry_rationale_ref for row in self.retry_rationale_rows]
        _ensure_sorted_unique(rationale_refs, field_name="retry_rationale_rows")
        for field_name in (
            "local_retryable_source_refs",
            "local_non_retryable_source_refs",
            "blocked_source_refs",
            "forbidden_source_refs",
            "support_only_source_refs",
        ):
            values = getattr(self, field_name)
            if field_name == "local_retryable_source_refs":
                _ensure_sorted_unique(values, field_name=field_name)
            else:
                _ensure_sorted_unique_allow_empty(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
        all_row_refs = {row.remand_source_ref for row in self.remand_source_rows}
        for field_name in (
            "local_retryable_source_refs",
            "local_non_retryable_source_refs",
            "blocked_source_refs",
            "forbidden_source_refs",
            "support_only_source_refs",
        ):
            unknown = sorted(set(getattr(self, field_name)) - all_row_refs)
            if unknown:
                raise ValueError(f"{field_name} contains unknown remand source refs: {unknown}")
        expected_refs_by_posture = {
            "blocked": set(self.blocked_source_refs),
            "forbidden": set(self.forbidden_source_refs),
            "local_non_retryable": set(self.local_non_retryable_source_refs),
            "local_retryable": set(self.local_retryable_source_refs),
            "support_only": set(self.support_only_source_refs),
        }
        row_refs_by_posture: dict[str, set[str]] = {
            "blocked": set(),
            "forbidden": set(),
            "local_non_retryable": set(),
            "local_retryable": set(),
            "support_only": set(),
        }
        for row in self.remand_source_rows:
            row_refs_by_posture[row.retryability_posture].add(row.remand_source_ref)
        mismatched_postures = sorted(
            posture
            for posture, row_refs in row_refs_by_posture.items()
            if row_refs != expected_refs_by_posture[posture]
        )
        if mismatched_postures:
            raise ValueError(
                "remand source classification refs must match row retryability "
                f"postures: {mismatched_postures}"
            )
        rationale_kinds = {row.retry_rationale_kind for row in self.retry_rationale_rows}
        invalid = sorted(rationale_kinds - _ALLOWED_RETRY_RATIONALE_KINDS)
        if invalid:
            raise ValueError(f"retry rationale contains forbidden kinds: {invalid}")
        _ensure_no_forbidden_content(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalRetryEligibilityReview(_RetryBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_RETRY_ELIGIBILITY_REVIEW_SCHEMA] = Field(
        alias="schema"
    )
    retry_eligibility_review_ref: str
    retry_request_ref: str
    retry_lineage_registry_ref: str
    remand_source_index_ref: str
    released_trial_lineage_refs: list[str] = Field(min_length=1)
    cleanroom_continuity_refs: list[str] = Field(min_length=1)
    retry_scope_contract_refs: list[str] = Field(min_length=1)
    eligibility_posture: Literal[
        "blocked_by_contamination",
        "blocked_by_hidden_or_forbidden_source",
        "blocked_by_missing_local_remand",
        "blocked_by_missing_trial_closeout",
        "blocked_by_prior_local_acceptance",
        "blocked_by_retry_uniqueness_violation",
        "blocked_by_sandbox_violation",
        "blocked_by_scope_widening",
        "eligible_for_later_local_retry_dispatch_review",
        "future_family_only",
    ]
    ready_basis_posture: Literal["ready_no_blockers", "blocked", "future_family_only"]
    carried_blocker_refs: list[str] = Field(default_factory=list)
    carried_warning_refs: list[str] = Field(default_factory=list)
    non_authority_guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_eligibility_review(self) -> "ProgrambenchLocalRetryEligibilityReview":
        for field_name in (
            "released_trial_lineage_refs",
            "cleanroom_continuity_refs",
            "retry_scope_contract_refs",
            "non_authority_guardrail_refs",
        ):
            _ensure_sorted_unique(getattr(self, field_name), field_name=field_name)
        _ensure_sorted_unique_allow_empty(
            self.carried_blocker_refs,
            field_name="carried_blocker_refs",
        )
        _ensure_sorted_unique_allow_empty(
            self.carried_warning_refs,
            field_name="carried_warning_refs",
        )
        if self.eligibility_posture == "future_family_only":
            raise ValueError("PB-RETRY-0-A cannot mark retry eligibility future-family-only")
        if self.eligibility_posture == "eligible_for_later_local_retry_dispatch_review":
            if self.ready_basis_posture != "ready_no_blockers":
                raise ValueError("eligible retry reviews require ready_no_blockers basis")
            if self.carried_blocker_refs:
                raise ValueError("eligible retry reviews cannot carry blockers")
        elif not self.carried_blocker_refs:
            raise ValueError("blocked retry reviews require blocker refs")
        return self


class ProgrambenchLocalRetryScopeContract(_RetryBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_RETRY_SCOPE_CONTRACT_SCHEMA] = Field(alias="schema")
    retry_scope_contract_ref: str
    retry_request_ref: str
    retry_lineage_ref: str
    retry_scope_delta_refs: list[str] = Field(min_length=1)
    retry_scope_delta_manifest_hash: str
    unchanged_worker_visible_source_refs: list[str] = Field(min_length=1)
    unchanged_forbidden_source_refs: list[str] = Field(min_length=1)
    unchanged_tool_policy_refs: list[str] = Field(min_length=1)
    unchanged_sandbox_policy_refs: list[str] = Field(min_length=1)
    unchanged_worker_visible_source_set_hash: str
    unchanged_forbidden_source_set_hash: str
    unchanged_tool_policy_hash: str
    unchanged_sandbox_policy_hash: str
    unchanged_write_scope_hash: str
    unchanged_network_policy_hash: str
    allowed_retry_action_rows: list[ProgrambenchLocalRetryAllowedActionRow] = Field(min_length=1)
    forbidden_retry_action_rows: list[ProgrambenchLocalRetryForbiddenActionRow] = Field(
        min_length=1
    )
    retry_depth_limit: int = Field(ge=1)
    retry_chain_posture: Literal["single_retry_only_no_chain_authority"]
    scope_authority_posture: Literal["no_scope_widening_authority_granted_by_pb_retry_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_scope_contract(self) -> "ProgrambenchLocalRetryScopeContract":
        for field_name in (
            "retry_scope_delta_manifest_hash",
            "unchanged_worker_visible_source_set_hash",
            "unchanged_forbidden_source_set_hash",
            "unchanged_tool_policy_hash",
            "unchanged_sandbox_policy_hash",
            "unchanged_write_scope_hash",
            "unchanged_network_policy_hash",
        ):
            _ensure_hash(getattr(self, field_name), field_name=field_name)
        for field_name in (
            "retry_scope_delta_refs",
            "unchanged_worker_visible_source_refs",
            "unchanged_forbidden_source_refs",
            "unchanged_tool_policy_refs",
            "unchanged_sandbox_policy_refs",
        ):
            _ensure_sorted_unique(getattr(self, field_name), field_name=field_name)
            _ensure_no_forbidden_refs(getattr(self, field_name), field_name=field_name)
        if self.retry_depth_limit != 1:
            raise ValueError("PB-RETRY-0-A allows only retry_depth_limit = 1")
        allowed_refs = [row.allowed_action_ref for row in self.allowed_retry_action_rows]
        _ensure_sorted_unique(allowed_refs, field_name="allowed_retry_action_rows")
        forbidden_refs = [row.forbidden_action_ref for row in self.forbidden_retry_action_rows]
        _ensure_sorted_unique(forbidden_refs, field_name="forbidden_retry_action_rows")
        required_forbidden_actions = {
            "add_evidence_source",
            "add_tool",
            "benchmark_scoring",
            "decompilation",
            "docker_socket_access",
            "external_repo_lookup",
            "hidden_test_access",
            "host_secret_access",
            "internet_lookup",
            "model_ranking",
            "network_access",
            "official_submission",
            "source_lookup",
            "widen_write_scope",
        }
        observed = {row.action_kind for row in self.forbidden_retry_action_rows}
        missing = sorted(required_forbidden_actions - observed)
        if missing:
            raise ValueError(f"retry scope missing forbidden action kinds: {missing}")
        return self


class ProgrambenchLocalRetryNonAuthorityGuardrail(_RetryBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_RETRY_NON_AUTHORITY_GUARDRAIL_SCHEMA] = Field(
        alias="schema"
    )
    retry_guardrail_ref: str
    retry_request_refs: list[str] = Field(min_length=1)
    guardrail_source_refs: list[str] = Field(min_length=1)
    non_authority_rows: list[ProgrambenchLocalRetryForbiddenAuthorityRow] = Field(min_length=1)
    forbidden_future_artifact_kinds: list[str] = Field(min_length=1)
    retry_dispatch_posture: Literal["no_retry_dispatch_authority_granted_by_pb_retry_0a"]
    official_programbench_posture: Literal[
        "no_official_programbench_authority_granted_by_pb_retry_0a"
    ]
    hidden_test_posture: Literal["hidden_tests_not_visible_not_inference_evidence"]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    model_ranking_posture: Literal["no_model_ranking_claimed_by_pb_retry_0a"]
    second_retry_posture: Literal["no_second_retry_authority_granted_by_pb_retry_0a"]
    future_family_posture: Literal["no_future_family_selected_by_pb_retry_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_guardrail(self) -> "ProgrambenchLocalRetryNonAuthorityGuardrail":
        _ensure_sorted_unique(self.retry_request_refs, field_name="retry_request_refs")
        _ensure_sorted_unique(self.guardrail_source_refs, field_name="guardrail_source_refs")
        row_refs = [row.forbidden_authority_ref for row in self.non_authority_rows]
        _ensure_sorted_unique(row_refs, field_name="non_authority_rows")
        required_authorities = {
            "benchmark_truth",
            "command_execution",
            "future_family_selection",
            "hidden_test_inference",
            "model_ranking",
            "multi_attempt_comparison",
            "official_programbench_participation",
            "official_submission",
            "remand_settlement",
            "retry_candidate_delta_snapshot",
            "retry_dispatch",
            "retry_execution_capture",
            "retry_lifecycle_projection",
            "retry_outcome_audit",
            "second_retry",
            "source_lookup",
        }
        observed = {row.authority_kind for row in self.non_authority_rows}
        missing = sorted(required_authorities - observed)
        if missing:
            raise ValueError(f"retry guardrail missing forbidden authorities: {missing}")
        _ensure_sorted_unique(
            self.forbidden_future_artifact_kinds,
            field_name="forbidden_future_artifact_kinds",
        )
        forbidden_future = set(self.forbidden_future_artifact_kinds)
        missing_future = sorted(
            PB_RETRY_0A_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS - forbidden_future
        )
        if missing_future:
            raise ValueError(f"retry guardrail missing future artifact kinds: {missing_future}")
        current = sorted(PB_RETRY_0A_ARTIFACT_KINDS & forbidden_future)
        if current:
            raise ValueError(f"retry guardrail cannot forbid current A artifact kinds: {current}")
        return self


class ProgrambenchLocalRetryDispatchRecord(_RetryBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_RETRY_DISPATCH_RECORD_SCHEMA] = Field(
        alias="schema"
    )
    retry_dispatch_record_ref: str
    retry_request_ref: str
    retry_lineage_ref: str
    source_trial_dispatch_ref: str
    retry_eligibility_review_ref: str
    retry_scope_contract_ref: str
    retry_dispatch_authority_ref: str
    retry_depth: int = Field(ge=1)
    worker_profile_ref: str
    worker_input_packet_hash: str
    worker_visible_context_hash: str
    retry_scope_delta_hash: str
    retry_input_packet_hash: str
    retry_worker_visible_context_hash: str
    retry_scope_contract_hash: str
    retry_allowed_tool_manifest_hash: str
    retry_forbidden_tool_manifest_hash: str
    retry_sandbox_policy_hash: str
    retry_run_budget_hash: str
    tool_manifest_ref: str
    allowed_tool_manifest_hash: str
    forbidden_tool_manifest_hash: str
    sandbox_instance_ref: str
    sandbox_attestation_bundle_ref: str
    input_packet_materialization_hash: str
    dispatch_cardinality_posture: Literal[
        "one_retry_dispatch_specimen_per_retry_request"
    ]
    official_programbench_posture: Literal[
        "no_official_programbench_participation_by_pb_retry_0b"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_dispatch_record(self) -> "ProgrambenchLocalRetryDispatchRecord":
        if self.retry_dispatch_authority_ref != _PB_RETRY_0B_DISPATCH_AUTHORITY_REF:
            raise ValueError("retry dispatch requires released PB-RETRY-0-B lock authority")
        if self.retry_depth != 1:
            raise ValueError("PB-RETRY-0-B allows only retry_depth = 1")
        for field_name in (
            "worker_input_packet_hash",
            "worker_visible_context_hash",
            "retry_scope_delta_hash",
            "retry_input_packet_hash",
            "retry_worker_visible_context_hash",
            "retry_scope_contract_hash",
            "retry_allowed_tool_manifest_hash",
            "retry_forbidden_tool_manifest_hash",
            "retry_sandbox_policy_hash",
            "retry_run_budget_hash",
            "allowed_tool_manifest_hash",
            "forbidden_tool_manifest_hash",
            "input_packet_materialization_hash",
        ):
            _ensure_hash(getattr(self, field_name), field_name=field_name)
        if self.retry_input_packet_hash != self.worker_input_packet_hash:
            raise ValueError("retry input packet hash must match worker input packet hash")
        if self.retry_worker_visible_context_hash != self.worker_visible_context_hash:
            raise ValueError(
                "retry worker-visible context hash must match worker-visible context hash"
            )
        if self.retry_allowed_tool_manifest_hash != self.allowed_tool_manifest_hash:
            raise ValueError("retry allowed tool hash must match allowed tool hash")
        if self.retry_forbidden_tool_manifest_hash != self.forbidden_tool_manifest_hash:
            raise ValueError("retry forbidden tool hash must match forbidden tool hash")
        return self


class ProgrambenchLocalRetryExecutionCapture(_RetryBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_RETRY_EXECUTION_CAPTURE_SCHEMA] = Field(
        alias="schema"
    )
    retry_execution_capture_ref: str
    retry_dispatch_record_ref: str
    stdout_hash: str
    stdout_excerpt_bounded: str = Field(max_length=512)
    stderr_hash: str
    stderr_excerpt_bounded: str = Field(max_length=512)
    transcript_hash: str
    transcript_excerpt_bounded: str = Field(max_length=1024)
    exit_code: int
    duration_ms: int = Field(ge=0)
    timeout_status: Literal["not_timed_out", "timed_out_with_capture"]
    worker_tool_call_manifest_ref: str
    full_output_capture_policy_ref: str
    forbidden_content_screen_verdict: Literal[
        "blocked_excluded_derived",
        "blocked_forbidden_source",
        "blocked_hidden_evidence",
        "blocked_postmortem_only",
        "inconclusive_requires_review",
        "passed",
    ]
    forbidden_content_screening_basis_refs: list[str] = Field(min_length=1)
    screened_output_hashes: list[str] = Field(min_length=1)
    screening_reviewer_or_policy_ref: str
    sandbox_violation_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_execution_capture(self) -> "ProgrambenchLocalRetryExecutionCapture":
        for field_name in ("stdout_hash", "stderr_hash", "transcript_hash"):
            _ensure_hash(getattr(self, field_name), field_name=field_name)
        _ensure_sorted_unique(
            self.forbidden_content_screening_basis_refs,
            field_name="forbidden_content_screening_basis_refs",
        )
        _ensure_no_forbidden_refs(
            self.forbidden_content_screening_basis_refs,
            field_name="forbidden_content_screening_basis_refs",
        )
        _ensure_sorted_unique(
            self.screened_output_hashes,
            field_name="screened_output_hashes",
        )
        for screened_output_hash in self.screened_output_hashes:
            _ensure_hash(screened_output_hash, field_name="screened_output_hashes")
        _ensure_sorted_unique_allow_empty(
            self.sandbox_violation_refs,
            field_name="sandbox_violation_refs",
        )
        _ensure_no_forbidden_refs(
            self.sandbox_violation_refs,
            field_name="sandbox_violation_refs",
        )
        return self


class ProgrambenchLocalRetryCandidateDeltaSnapshot(_RetryBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_RETRY_CANDIDATE_DELTA_SNAPSHOT_SCHEMA] = Field(
        alias="schema"
    )
    retry_candidate_delta_snapshot_ref: str
    retry_execution_capture_ref: str
    source_trial_candidate_snapshot_ref: str
    generated_file_manifest_ref: str
    materialization_input_hash: str
    materialization_output_manifest_hash: str
    write_scope_ref: str
    inside_released_write_scope: Literal[True]
    forbidden_content_screen_verdict: Literal["passed"]
    official_submission_posture: Literal[
        "no_official_submission_authority_by_pb_retry_0b"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_candidate_delta_snapshot(
        self,
    ) -> "ProgrambenchLocalRetryCandidateDeltaSnapshot":
        _ensure_hash(self.materialization_input_hash, field_name="materialization_input_hash")
        _ensure_hash(
            self.materialization_output_manifest_hash,
            field_name="materialization_output_manifest_hash",
        )
        return self


class ProgrambenchLocalRetryLifecycleProjection(_RetryBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_RETRY_LIFECYCLE_PROJECTION_SCHEMA] = Field(
        alias="schema"
    )
    retry_lifecycle_projection_ref: str
    retry_request_ref: str
    retry_dispatch_record_ref: str
    retry_execution_capture_ref: str
    retry_candidate_delta_snapshot_ref: str
    trial_lifecycle_projection_ref: str
    attempt_lifecycle_projection_refs: list[str] = Field(min_length=1)
    pb_trial_validator_binding_refs: list[str] = Field(min_length=1)
    pb_attempt_validator_binding_refs: list[str] = Field(min_length=1)
    projection_validation_posture: Literal[
        "projected_to_released_trial_and_attempt_lifecycle_refs"
    ]
    new_evidence_law_posture: Literal["no_new_evidence_law_defined_by_pb_retry_0b"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_lifecycle_projection(
        self,
    ) -> "ProgrambenchLocalRetryLifecycleProjection":
        for field_name in (
            "attempt_lifecycle_projection_refs",
            "pb_trial_validator_binding_refs",
            "pb_attempt_validator_binding_refs",
        ):
            _ensure_sorted_unique(getattr(self, field_name), field_name=field_name)
            _ensure_no_forbidden_refs(getattr(self, field_name), field_name=field_name)
        return self


class ProgrambenchLocalRetrySandboxApplicationTrace(_RetryBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_RETRY_SANDBOX_APPLICATION_TRACE_SCHEMA] = Field(
        alias="schema"
    )
    retry_sandbox_trace_ref: str
    retry_dispatch_record_ref: str
    sandbox_instance_ref: str
    sandbox_attestation_bundle_ref: str
    network_mode_witness_ref: str
    docker_socket_absence_witness_ref: str
    secret_absence_witness_ref: str
    source_lookup_absence_witness_ref: str
    decompilation_absence_witness_ref: str
    write_scope_attestation_ref: str
    resource_limit_attestation_ref: str
    tool_manifest_match_ref: str
    sandbox_violation_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_sandbox_trace(
        self,
    ) -> "ProgrambenchLocalRetrySandboxApplicationTrace":
        _ensure_sorted_unique_allow_empty(
            self.sandbox_violation_refs,
            field_name="sandbox_violation_refs",
        )
        _ensure_no_forbidden_refs(
            self.sandbox_violation_refs,
            field_name="sandbox_violation_refs",
        )
        return self


def validate_pb_retry_0a_retry_bundle(
    *,
    trial_outcome_audit: ProgrambenchLocalTrialOutcomeAudit,
    trial_observation_summary: ProgrambenchLocalTrialObservationSummary,
    trial_remand_decision: ProgrambenchLocalTrialRemandDecision,
    trial_family_closeout: ProgrambenchLocalTrialFamilyCloseoutAlignment,
    retry_request: ProgrambenchLocalRetryRequest,
    retry_lineage_registry: ProgrambenchLocalRetryLineageRegistry,
    remand_source_index: ProgrambenchTrialRemandSourceIndex,
    retry_eligibility_review: ProgrambenchLocalRetryEligibilityReview,
    retry_scope_contract: ProgrambenchLocalRetryScopeContract,
    retry_guardrail: ProgrambenchLocalRetryNonAuthorityGuardrail,
) -> None:
    if trial_family_closeout.closed_family_ref != "PB-TRIAL-0":
        raise ValueError("retry request requires released PB-TRIAL-0 closeout")
    if trial_outcome_audit.trial_outcome_audit_ref not in (
        trial_family_closeout.trial_outcome_audit_refs
    ):
        raise ValueError("trial closeout must release outcome audit")
    if trial_observation_summary.trial_observation_summary_ref not in (
        trial_family_closeout.trial_observation_summary_refs
    ):
        raise ValueError("trial closeout must release observation summary")
    if trial_remand_decision.trial_remand_decision_ref not in (
        trial_family_closeout.trial_remand_decision_refs
    ):
        raise ValueError("trial closeout must release remand decision")
    if trial_observation_summary.trial_outcome_audit_ref != (
        trial_outcome_audit.trial_outcome_audit_ref
    ):
        raise ValueError("trial observation summary must reference outcome audit")
    if trial_remand_decision.trial_outcome_audit_ref != trial_outcome_audit.trial_outcome_audit_ref:
        raise ValueError("trial remand decision must reference outcome audit")
    if trial_remand_decision.trial_observation_summary_ref != (
        trial_observation_summary.trial_observation_summary_ref
    ):
        raise ValueError("trial remand decision must reference observation summary")
    if trial_outcome_audit.local_outcome_posture == "trial_locally_accepted":
        raise ValueError("retry request cannot be eligible from locally accepted trial")
    if not trial_remand_decision.remand_decision_rows:
        raise ValueError("retry request requires local remand decision rows")

    if retry_request.trial_outcome_audit_ref != trial_outcome_audit.trial_outcome_audit_ref:
        raise ValueError("retry request must reference trial outcome audit")
    if retry_request.trial_observation_summary_ref != (
        trial_observation_summary.trial_observation_summary_ref
    ):
        raise ValueError("retry request must reference trial observation summary")
    if retry_request.trial_remand_decision_ref != trial_remand_decision.trial_remand_decision_ref:
        raise ValueError("retry request must reference trial remand decision")
    if retry_request.trial_family_closeout_ref != trial_family_closeout.family_closeout_ref:
        raise ValueError("retry request must reference trial family closeout")

    if retry_lineage_registry.retry_lineage_registry_ref != (
        retry_request.retry_lineage_registry_ref
    ):
        raise ValueError("retry request must reference retry lineage registry")
    if retry_lineage_registry.trial_lineage_ref != retry_request.trial_lineage_ref:
        raise ValueError("retry lineage registry must preserve trial lineage")
    if retry_lineage_registry.trial_remand_decision_ref != (
        retry_request.trial_remand_decision_ref
    ):
        raise ValueError("retry lineage registry must reference trial remand decision")
    if retry_lineage_registry.eligible_retry_request_refs != [retry_request.retry_request_ref]:
        raise ValueError("retry lineage registry must release exactly this retry request")
    if retry_request.prior_retry_request_refs:
        raise ValueError("prior retry request refs block PB-RETRY-0-A eligibility")
    if retry_lineage_registry.existing_retry_request_refs:
        raise ValueError("prior retry request refs block PB-RETRY-0-A eligibility")

    if remand_source_index.retry_request_ref != retry_request.retry_request_ref:
        raise ValueError("remand source index must reference retry request")
    if remand_source_index.trial_remand_decision_ref != (
        trial_remand_decision.trial_remand_decision_ref
    ):
        raise ValueError("remand source index must reference trial remand decision")
    trial_remand_source_refs = {
        row.remand_decision_row_ref for row in trial_remand_decision.remand_decision_rows
    }
    unknown_remand_refs = sorted(
        set(remand_source_index.local_retryable_source_refs) - trial_remand_source_refs
    )
    if unknown_remand_refs:
        raise ValueError(
            "local retryable source refs must be released by trial remand decision: "
            f"{unknown_remand_refs}"
        )

    if retry_scope_contract.retry_request_ref != retry_request.retry_request_ref:
        raise ValueError("retry scope contract must reference retry request")
    if retry_scope_contract.retry_lineage_ref != retry_request.retry_lineage_ref:
        raise ValueError("retry scope contract must preserve retry lineage")
    if retry_scope_contract.retry_depth_limit != retry_request.retry_depth_limit:
        raise ValueError("retry scope contract must preserve retry depth limit")

    if retry_eligibility_review.retry_request_ref != retry_request.retry_request_ref:
        raise ValueError("retry eligibility review must reference retry request")
    if retry_eligibility_review.retry_lineage_registry_ref != (
        retry_lineage_registry.retry_lineage_registry_ref
    ):
        raise ValueError("retry eligibility review must reference retry lineage registry")
    if retry_eligibility_review.remand_source_index_ref != (
        remand_source_index.remand_source_index_ref
    ):
        raise ValueError("retry eligibility review must reference remand source index")
    if retry_scope_contract.retry_scope_contract_ref not in (
        retry_eligibility_review.retry_scope_contract_refs
    ):
        raise ValueError("retry eligibility review must release retry scope contract")
    if retry_eligibility_review.eligibility_posture != (
        "eligible_for_later_local_retry_dispatch_review"
    ):
        raise ValueError("retry bundle requires eligible retry posture")

    if retry_request.retry_request_ref not in retry_guardrail.retry_request_refs:
        raise ValueError("retry guardrail must reference retry request")
    if retry_guardrail.retry_dispatch_posture != (
        "no_retry_dispatch_authority_granted_by_pb_retry_0a"
    ):
        raise ValueError("retry guardrail must deny dispatch authority")


def validate_pb_retry_0b_dispatch_bundle(
    *,
    retry_request: ProgrambenchLocalRetryRequest,
    retry_lineage_registry: ProgrambenchLocalRetryLineageRegistry,
    remand_source_index: ProgrambenchTrialRemandSourceIndex,
    retry_eligibility_review: ProgrambenchLocalRetryEligibilityReview,
    retry_scope_contract: ProgrambenchLocalRetryScopeContract,
    retry_guardrail: ProgrambenchLocalRetryNonAuthorityGuardrail,
    source_trial_dispatch: ProgrambenchLocalTrialWorkerDispatchRecord,
    source_trial_candidate_snapshot: ProgrambenchLocalTrialCandidateArtifactSnapshot,
    source_trial_lifecycle_projection: ProgrambenchLocalTrialLifecycleProjection,
    retry_dispatch_record: ProgrambenchLocalRetryDispatchRecord,
    retry_execution_capture: ProgrambenchLocalRetryExecutionCapture,
    retry_candidate_delta_snapshot: ProgrambenchLocalRetryCandidateDeltaSnapshot,
    retry_lifecycle_projection: ProgrambenchLocalRetryLifecycleProjection,
    retry_sandbox_trace: ProgrambenchLocalRetrySandboxApplicationTrace,
) -> None:
    if retry_eligibility_review.eligibility_posture != (
        "eligible_for_later_local_retry_dispatch_review"
    ):
        raise ValueError("PB-RETRY-0-B requires released eligible A retry review")
    if retry_eligibility_review.ready_basis_posture != "ready_no_blockers":
        raise ValueError("PB-RETRY-0-B requires ready_no_blockers A basis")
    if retry_eligibility_review.carried_blocker_refs:
        raise ValueError("PB-RETRY-0-B cannot dispatch with A carried blockers")
    if retry_eligibility_review.retry_request_ref != retry_request.retry_request_ref:
        raise ValueError("retry eligibility review must reference retry request")
    if retry_eligibility_review.retry_lineage_registry_ref != (
        retry_lineage_registry.retry_lineage_registry_ref
    ):
        raise ValueError("retry eligibility review must reference retry lineage registry")
    if retry_scope_contract.retry_scope_contract_ref not in (
        retry_eligibility_review.retry_scope_contract_refs
    ):
        raise ValueError("retry eligibility review must release retry scope contract")
    if retry_guardrail.retry_guardrail_ref not in (
        retry_eligibility_review.non_authority_guardrail_refs
    ):
        raise ValueError("retry eligibility review must release retry guardrail")
    if retry_request.retry_request_ref not in retry_lineage_registry.eligible_retry_request_refs:
        raise ValueError("retry request must be released by retry lineage registry")
    if retry_request.prior_retry_request_refs or retry_lineage_registry.existing_retry_request_refs:
        raise ValueError("PB-RETRY-0-B cannot dispatch after an existing retry request")
    if remand_source_index.retry_request_ref != retry_request.retry_request_ref:
        raise ValueError("remand source index must reference retry request")
    if retry_scope_contract.retry_request_ref != retry_request.retry_request_ref:
        raise ValueError("retry scope contract must reference retry request")
    if retry_guardrail.retry_dispatch_posture != (
        "no_retry_dispatch_authority_granted_by_pb_retry_0a"
    ):
        raise ValueError("A guardrail must deny retry dispatch authority")

    if retry_dispatch_record.retry_request_ref != retry_request.retry_request_ref:
        raise ValueError("retry dispatch must reference retry request")
    if retry_dispatch_record.retry_lineage_ref != retry_request.retry_lineage_ref:
        raise ValueError("retry dispatch must preserve retry lineage")
    if retry_dispatch_record.retry_eligibility_review_ref != (
        retry_eligibility_review.retry_eligibility_review_ref
    ):
        raise ValueError("retry dispatch must reference A eligibility review")
    if retry_dispatch_record.retry_scope_contract_ref != (
        retry_scope_contract.retry_scope_contract_ref
    ):
        raise ValueError("retry dispatch must reference A scope contract")
    if retry_dispatch_record.source_trial_dispatch_ref != (
        source_trial_dispatch.trial_worker_dispatch_ref
    ):
        raise ValueError("retry dispatch must bind to source trial dispatch")
    if retry_dispatch_record.retry_depth != retry_request.retry_depth_limit:
        raise ValueError("retry dispatch must preserve retry depth limit")
    if retry_dispatch_record.retry_dispatch_authority_ref != (
        _PB_RETRY_0B_DISPATCH_AUTHORITY_REF
    ):
        raise ValueError("retry dispatch requires PB-RETRY-0-B lock authority")
    if retry_dispatch_record.retry_scope_delta_hash != (
        retry_scope_contract.retry_scope_delta_manifest_hash
    ):
        raise ValueError("retry dispatch must bind to A retry scope delta hash")
    if retry_dispatch_record.retry_sandbox_policy_hash != (
        retry_scope_contract.unchanged_sandbox_policy_hash
    ):
        raise ValueError("retry dispatch must preserve A unchanged sandbox policy hash")
    if retry_dispatch_record.worker_input_packet_hash != (
        source_trial_dispatch.worker_input_packet_hash
    ):
        raise ValueError("retry dispatch must preserve source trial worker input hash")
    if retry_dispatch_record.worker_visible_context_hash != (
        source_trial_dispatch.worker_visible_context_hash
    ):
        raise ValueError("retry dispatch must preserve source trial worker context hash")
    if retry_dispatch_record.worker_profile_ref != source_trial_dispatch.worker_profile_ref:
        raise ValueError("retry dispatch must preserve source trial worker profile")
    if retry_dispatch_record.tool_manifest_ref != source_trial_dispatch.tool_manifest_ref:
        raise ValueError("retry dispatch must preserve source trial tool manifest")
    if retry_dispatch_record.allowed_tool_manifest_hash != (
        source_trial_dispatch.allowed_tool_manifest_hash
    ):
        raise ValueError("retry dispatch must preserve source trial allowed tool hash")
    if retry_dispatch_record.forbidden_tool_manifest_hash != (
        source_trial_dispatch.forbidden_tool_manifest_hash
    ):
        raise ValueError("retry dispatch must preserve source trial forbidden tool hash")
    if retry_dispatch_record.input_packet_materialization_hash != (
        source_trial_dispatch.input_packet_materialization_hash
    ):
        raise ValueError(
            "retry dispatch must preserve source trial input materialization hash"
        )

    if retry_execution_capture.retry_dispatch_record_ref != (
        retry_dispatch_record.retry_dispatch_record_ref
    ):
        raise ValueError("retry execution capture must reference retry dispatch")
    if retry_execution_capture.forbidden_content_screen_verdict != (
        _PASSED_FORBIDDEN_CONTENT_SCREEN_VERDICT
    ):
        raise ValueError("retry execution capture requires passed forbidden-content screening")
    if retry_execution_capture.sandbox_violation_refs:
        raise ValueError("retry execution capture cannot carry sandbox violations")

    if retry_candidate_delta_snapshot.retry_execution_capture_ref != (
        retry_execution_capture.retry_execution_capture_ref
    ):
        raise ValueError("retry candidate delta must reference execution capture")
    if retry_candidate_delta_snapshot.source_trial_candidate_snapshot_ref != (
        source_trial_candidate_snapshot.candidate_artifact_snapshot_ref
    ):
        raise ValueError("retry candidate delta must bind to source trial candidate snapshot")
    if retry_candidate_delta_snapshot.forbidden_content_screen_verdict != (
        retry_execution_capture.forbidden_content_screen_verdict
    ):
        raise ValueError("retry candidate delta must preserve screening verdict")
    if retry_candidate_delta_snapshot.materialization_input_hash not in (
        retry_execution_capture.screened_output_hashes
    ):
        raise ValueError("retry candidate delta input hash must be a screened output hash")
    if retry_candidate_delta_snapshot.write_scope_ref != (
        source_trial_candidate_snapshot.write_scope_ref
    ):
        raise ValueError("retry candidate delta must preserve released source write scope")

    if retry_lifecycle_projection.retry_request_ref != retry_request.retry_request_ref:
        raise ValueError("retry lifecycle projection must reference retry request")
    if retry_lifecycle_projection.retry_dispatch_record_ref != (
        retry_dispatch_record.retry_dispatch_record_ref
    ):
        raise ValueError("retry lifecycle projection must reference retry dispatch")
    if retry_lifecycle_projection.retry_execution_capture_ref != (
        retry_execution_capture.retry_execution_capture_ref
    ):
        raise ValueError("retry lifecycle projection must reference execution capture")
    if retry_lifecycle_projection.retry_candidate_delta_snapshot_ref != (
        retry_candidate_delta_snapshot.retry_candidate_delta_snapshot_ref
    ):
        raise ValueError("retry lifecycle projection must reference candidate delta")
    if retry_lifecycle_projection.trial_lifecycle_projection_ref != (
        source_trial_lifecycle_projection.trial_lifecycle_projection_ref
    ):
        raise ValueError("retry lifecycle projection must bind to source trial lifecycle")
    if retry_lifecycle_projection.projection_validation_posture != (
        "projected_to_released_trial_and_attempt_lifecycle_refs"
    ):
        raise ValueError("retry lifecycle projection must use released lifecycle refs")
    if retry_lifecycle_projection.new_evidence_law_posture != (
        "no_new_evidence_law_defined_by_pb_retry_0b"
    ):
        raise ValueError("retry lifecycle projection cannot define new evidence law")

    if retry_sandbox_trace.retry_dispatch_record_ref != (
        retry_dispatch_record.retry_dispatch_record_ref
    ):
        raise ValueError("retry sandbox trace must reference retry dispatch")
    if retry_sandbox_trace.sandbox_instance_ref != retry_dispatch_record.sandbox_instance_ref:
        raise ValueError("retry sandbox trace must bind to dispatch sandbox instance")
    if retry_sandbox_trace.sandbox_attestation_bundle_ref != (
        retry_dispatch_record.sandbox_attestation_bundle_ref
    ):
        raise ValueError("retry sandbox trace must bind to dispatch sandbox attestation")
    if retry_sandbox_trace.sandbox_violation_refs:
        raise ValueError("retry sandbox trace cannot carry sandbox violations")
