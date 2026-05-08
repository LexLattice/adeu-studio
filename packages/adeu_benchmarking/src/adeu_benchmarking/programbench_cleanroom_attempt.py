from __future__ import annotations

import re
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

from .programbench_cleanroom_reconstruction import (
    ProgrambenchReconstructionContextExclusionManifest,
    ProgrambenchReconstructionResultSummary,
    ProgrambenchReconstructionRunBudget,
    ProgrambenchReconstructionSandboxPolicy,
    ProgrambenchReconstructionWorkbenchFamilyCloseoutAlignment,
    ProgrambenchReconstructionWorkbenchNonAuthorityGuardrail,
    ProgrambenchReconstructionWorkerContextPacket,
    ProgrambenchReconstructionWorkOrder,
)

MODEL_CONFIG = ConfigDict(
    extra="forbid",
    frozen=True,
    populate_by_name=True,
    protected_namespaces=(),
)

PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_REQUEST_SCHEMA = "programbench_reconstruction_attempt_request@1"
PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_WORKER_INPUT_PACKET_SCHEMA = (
    "programbench_reconstruction_attempt_worker_input_packet@1"
)
PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_DISPATCH_PREFLIGHT_SCHEMA = (
    "programbench_reconstruction_attempt_dispatch_preflight@1"
)
PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_NON_AUTHORITY_GUARDRAIL_SCHEMA = (
    "programbench_reconstruction_attempt_non_authority_guardrail@1"
)

PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_WORKER_INVOCATION_RECORD_SCHEMA = (
    "programbench_reconstruction_attempt_worker_invocation_record@1"
)
PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_OUTPUT_CAPTURE_SCHEMA = (
    "programbench_reconstruction_attempt_output_capture@1"
)
PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_CANDIDATE_MATERIALIZATION_SCHEMA = (
    "programbench_reconstruction_attempt_candidate_materialization@1"
)
PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_SANDBOX_APPLICATION_TRACE_SCHEMA = (
    "programbench_reconstruction_attempt_sandbox_application_trace@1"
)
PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_WORKBENCH_EVIDENCE_EXPORT_SCHEMA = (
    "programbench_reconstruction_attempt_workbench_evidence_export@1"
)
PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_RESULT_REVIEW_SCHEMA = (
    "programbench_reconstruction_attempt_result_review@1"
)
PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_REMAND_QUEUE_SCHEMA = (
    "programbench_reconstruction_attempt_remand_queue@1"
)
PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA = (
    "programbench_reconstruction_attempt_family_closeout_alignment@1"
)

PB_ATTEMPT_0A_ARTIFACT_KINDS = {
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_REQUEST_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_WORKER_INPUT_PACKET_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_DISPATCH_PREFLIGHT_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_NON_AUTHORITY_GUARDRAIL_SCHEMA,
}
PB_ATTEMPT_0B_ARTIFACT_KINDS = {
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_WORKER_INVOCATION_RECORD_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_OUTPUT_CAPTURE_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_CANDIDATE_MATERIALIZATION_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_SANDBOX_APPLICATION_TRACE_SCHEMA,
}
PB_ATTEMPT_0C_ARTIFACT_KINDS = {
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_WORKBENCH_EVIDENCE_EXPORT_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_RESULT_REVIEW_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_REMAND_QUEUE_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
}
PB_ATTEMPT_0A_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS = (
    PB_ATTEMPT_0B_ARTIFACT_KINDS | PB_ATTEMPT_0C_ARTIFACT_KINDS
)

_SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
_REQUIRED_SANDBOX_WITNESSES = {
    "argv_shaped_command_policy",
    "bounded_filesystem_write_scope",
    "network_disabled",
    "no_decompilation",
    "no_docker_socket",
    "no_host_secrets",
    "no_source_lookup",
}
_REQUIRED_BUDGET_WITNESSES = {
    "bounded_filesystem_budget_declared",
    "bounded_timeout_budget_declared",
    "bounded_token_budget_declared",
    "max_candidate_artifact_count_declared",
    "max_local_run_count_declared",
    "max_probe_run_count_declared",
    "max_remand_count_declared",
}
_COMPATIBLE_RESULT_POSTURES = {
    "blocked_by_missing_evidence",
    "inconclusive_local_audit",
    "local_remand_required",
}
_BLOCKED_RESULT_POSTURES = {
    "blocked_by_contamination",
    "blocked_by_sandbox_violation",
    "future_family_only",
    "local_accepted",
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


def _ensure_refs_resolve(
    refs: list[str],
    allowed_refs: set[str],
    *,
    field_name: str,
    allowed_name: str,
) -> None:
    missing = sorted(set(refs) - allowed_refs)
    if missing:
        raise ValueError(f"{field_name} contains refs outside {allowed_name}: {missing}")


class _AttemptBase(BaseModel):
    model_config = MODEL_CONFIG


class ProgrambenchReconstructionAttemptExcludedRefSummaryRow(_AttemptBase):
    exclusion_summary_ref: str
    exclusion_category: Literal[
        "excluded_derived_summary",
        "forbidden_source",
        "postmortem_only",
        "worker_hidden_source",
    ]
    excluded_ref_count: int = Field(ge=1)
    reason_code: Literal[
        "excluded_derived_not_worker_visible",
        "forbidden_not_worker_visible",
        "hidden_not_worker_visible",
        "postmortem_only_not_worker_visible",
    ]
    authority_posture: Literal["auditor_only_summary_not_worker_context"]
    non_exposure_statement: Literal["no_source_identity_or_content_exposed"]
    limitation_note: str


class ProgrambenchReconstructionAttemptContextDerivationRow(_AttemptBase):
    derivation_ref: str
    source_ref: str
    derived_ref: str
    derivation_kind: Literal[
        "advisory_concept_profile_ref",
        "advisory_realization_ref",
        "probe_expectation_ref",
        "released_worker_context_ref",
        "run_budget_summary_ref",
        "sandbox_summary_ref",
    ]
    worker_visibility_posture: Literal["worker_visible_attempt_input"]
    limitation_note: str


class ProgrambenchReconstructionAttemptPreflightCheckRow(_AttemptBase):
    preflight_check_ref: str
    check_kind: Literal[
        "excluded_ref_non_exposure",
        "guardrail_bound",
        "released_workbench_refs",
        "result_summary_compatible",
        "run_budget_bound",
        "sandbox_policy_bound",
        "worker_input_visibility",
    ]
    check_posture: Literal["blocked", "passed"]
    evidence_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_preflight_check(self) -> "ProgrambenchReconstructionAttemptPreflightCheckRow":
        _ensure_sorted_unique(self.evidence_refs, field_name="evidence_refs")
        return self


class ProgrambenchReconstructionAttemptForbiddenAuthorityRow(_AttemptBase):
    forbidden_authority_ref: str
    authority_kind: Literal[
        "benchmark_truth",
        "candidate_materialization",
        "command_execution",
        "future_family_selection",
        "hidden_test_inference",
        "local_probe_execution",
        "model_ranking",
        "official_programbench_participation",
        "official_submission",
        "source_lookup",
        "worker_invocation",
        "workbench_evidence_export",
    ]
    forbiddance_posture: Literal["forbidden_by_pb_attempt_0a"]
    limitation_note: str


class ProgrambenchReconstructionAttemptRequest(_AttemptBase):
    schema_id: Literal[PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_REQUEST_SCHEMA] = Field(alias="schema")
    attempt_request_ref: str
    work_order_ref: str
    worker_context_packet_ref: str
    context_exclusion_manifest_ref: str
    sandbox_policy_ref: str
    run_budget_ref: str
    result_summary_ref: str
    workbench_family_closeout_ref: str
    worker_profile_ref: str
    attempt_purpose: Literal[
        "local_evidence_gap_remediation_attempt",
        "local_remand_correction_attempt",
        "future_family_only",
    ]
    attempt_scope_posture: Literal["local_cleanroom_attempt_packaging_only"]
    dispatch_authority_posture: Literal["no_worker_dispatch_authority_granted_by_pb_attempt_0a"]
    official_programbench_posture: Literal[
        "no_official_programbench_participation_by_pb_attempt_0a"
    ]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    model_ranking_posture: Literal["no_model_ranking_claimed_by_pb_attempt_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_attempt_request(self) -> "ProgrambenchReconstructionAttemptRequest":
        if self.attempt_purpose == "future_family_only":
            raise ValueError("PB-ATTEMPT-0-A requests must package local attempt review only")
        return self


class ProgrambenchReconstructionAttemptWorkerInputPacket(_AttemptBase):
    schema_id: Literal[PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_WORKER_INPUT_PACKET_SCHEMA] = Field(
        alias="schema"
    )
    worker_input_packet_ref: str
    attempt_request_ref: str
    work_order_ref: str
    worker_context_packet_ref: str
    context_exclusion_manifest_ref: str
    worker_visible_source_refs: list[str] = Field(min_length=1)
    advisory_concept_profile_refs: list[str] = Field(min_length=1)
    advisory_realization_refs: list[str] = Field(min_length=1)
    probe_expectation_refs: list[str] = Field(min_length=1)
    sandbox_summary_refs: list[str] = Field(min_length=1)
    run_budget_summary_refs: list[str] = Field(min_length=1)
    excluded_ref_summary_rows: list[ProgrambenchReconstructionAttemptExcludedRefSummaryRow] = Field(
        min_length=1
    )
    context_derivation_rows: list[ProgrambenchReconstructionAttemptContextDerivationRow] = Field(
        min_length=1
    )
    worker_input_manifest_hash: str
    worker_visible_ref_count: int = Field(ge=1)
    forbidden_ref_exposure_check_hash: str
    worker_visibility_posture: Literal["worker_input_cleanroom_visible_only"]
    input_materialization_posture: Literal["no_candidate_materialization_by_pb_attempt_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_worker_input_packet(
        self,
    ) -> "ProgrambenchReconstructionAttemptWorkerInputPacket":
        for field_name in (
            "worker_visible_source_refs",
            "advisory_concept_profile_refs",
            "advisory_realization_refs",
            "probe_expectation_refs",
            "sandbox_summary_refs",
            "run_budget_summary_refs",
        ):
            _ensure_sorted_unique(getattr(self, field_name), field_name=field_name)
        summary_refs = [row.exclusion_summary_ref for row in self.excluded_ref_summary_rows]
        _ensure_sorted_unique(summary_refs, field_name="excluded_ref_summary_refs")
        derivation_refs = [row.derivation_ref for row in self.context_derivation_rows]
        _ensure_sorted_unique(derivation_refs, field_name="context_derivation_refs")
        _ensure_hash(self.worker_input_manifest_hash, field_name="worker_input_manifest_hash")
        _ensure_hash(
            self.forbidden_ref_exposure_check_hash,
            field_name="forbidden_ref_exposure_check_hash",
        )
        all_worker_refs = self.all_worker_visible_refs()
        if self.worker_visible_ref_count != len(all_worker_refs):
            raise ValueError(
                "worker_visible_ref_count must equal the unique worker-visible input refs"
            )
        all_derivation_refs = all_worker_refs | {
            self.attempt_request_ref,
            self.context_exclusion_manifest_ref,
            self.work_order_ref,
            self.worker_context_packet_ref,
            self.worker_input_packet_ref,
        }
        for row in self.context_derivation_rows:
            if (
                row.source_ref not in all_derivation_refs
                or row.derived_ref not in all_derivation_refs
            ):
                raise ValueError(
                    "context derivation rows must reference only worker-visible input "
                    "or explicit packet linkage refs"
                )
        return self

    def all_worker_visible_refs(self) -> set[str]:
        return (
            set(self.worker_visible_source_refs)
            | set(self.advisory_concept_profile_refs)
            | set(self.advisory_realization_refs)
            | set(self.probe_expectation_refs)
            | set(self.sandbox_summary_refs)
            | set(self.run_budget_summary_refs)
        )


class ProgrambenchReconstructionAttemptDispatchPreflight(_AttemptBase):
    schema_id: Literal[PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_DISPATCH_PREFLIGHT_SCHEMA] = Field(
        alias="schema"
    )
    dispatch_preflight_ref: str
    attempt_request_ref: str
    worker_input_packet_ref: str
    sandbox_policy_ref: str
    run_budget_ref: str
    guardrail_ref: str
    preflight_check_rows: list[ProgrambenchReconstructionAttemptPreflightCheckRow] = Field(
        min_length=1
    )
    sandbox_enforcement_requirement_refs: list[str] = Field(min_length=1)
    budget_enforcement_requirement_refs: list[str] = Field(min_length=1)
    preflight_scope_posture: Literal["eligibility_review_only_no_invocation"]
    preflight_posture: Literal[
        "blocked_no_dispatch_eligible",
        "preflight_passed_for_later_local_attempt_review",
        "future_family_only",
    ]
    dispatch_authority_posture: Literal["no_worker_dispatch_authority_granted_by_pb_attempt_0a"]
    execution_authority_posture: Literal["no_execution_authority_granted_by_pb_attempt_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_dispatch_preflight(
        self,
    ) -> "ProgrambenchReconstructionAttemptDispatchPreflight":
        if self.preflight_posture == "future_family_only":
            raise ValueError("dispatch preflight must review only PB-ATTEMPT-0-A eligibility")
        check_refs = [row.preflight_check_ref for row in self.preflight_check_rows]
        _ensure_sorted_unique(check_refs, field_name="preflight_check_refs")
        _ensure_sorted_unique(
            self.sandbox_enforcement_requirement_refs,
            field_name="sandbox_enforcement_requirement_refs",
        )
        _ensure_sorted_unique(
            self.budget_enforcement_requirement_refs,
            field_name="budget_enforcement_requirement_refs",
        )
        if self.preflight_posture == "preflight_passed_for_later_local_attempt_review":
            blocked = [
                row.preflight_check_ref
                for row in self.preflight_check_rows
                if row.check_posture != "passed"
            ]
            if blocked:
                raise ValueError(
                    f"passed dispatch preflights cannot carry blocked checks: {blocked}"
                )
        return self


class ProgrambenchReconstructionAttemptNonAuthorityGuardrail(_AttemptBase):
    schema_id: Literal[PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_NON_AUTHORITY_GUARDRAIL_SCHEMA] = Field(
        alias="schema"
    )
    guardrail_ref: str
    attempt_request_ref: str
    forbidden_authority_rows: list[ProgrambenchReconstructionAttemptForbiddenAuthorityRow] = Field(
        min_length=1
    )
    forbidden_future_artifact_kinds: list[str] = Field(min_length=1)
    dispatch_non_authority_posture: Literal["no_worker_dispatch_authority_granted_by_pb_attempt_0a"]
    execution_non_authority_posture: Literal["no_execution_authority_granted_by_pb_attempt_0a"]
    official_programbench_non_authority_posture: Literal[
        "no_official_programbench_authority_by_pb_attempt_0a"
    ]
    hidden_test_non_inference_posture: Literal["hidden_tests_not_visible_not_inference_evidence"]
    source_lookup_non_authority_posture: Literal["source_lookup_forbidden_by_pb_attempt_0a"]
    submission_non_authority_posture: Literal["no_submission_authority_by_pb_attempt_0a"]
    benchmark_truth_non_authority_posture: Literal["not_benchmark_truth"]
    model_ranking_non_authority_posture: Literal["no_model_ranking_claimed_by_pb_attempt_0a"]
    future_family_selection_posture: Literal["no_future_family_selected_by_pb_attempt_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_guardrail(
        self,
    ) -> "ProgrambenchReconstructionAttemptNonAuthorityGuardrail":
        row_refs = [row.forbidden_authority_ref for row in self.forbidden_authority_rows]
        _ensure_sorted_unique(row_refs, field_name="forbidden_authority_refs")
        authority_kinds = {row.authority_kind for row in self.forbidden_authority_rows}
        required_authority_kinds = {
            "benchmark_truth",
            "candidate_materialization",
            "command_execution",
            "future_family_selection",
            "hidden_test_inference",
            "local_probe_execution",
            "model_ranking",
            "official_programbench_participation",
            "official_submission",
            "source_lookup",
            "worker_invocation",
            "workbench_evidence_export",
        }
        missing_authority = sorted(required_authority_kinds - authority_kinds)
        if missing_authority:
            raise ValueError(f"guardrail missing forbidden authority kinds: {missing_authority}")
        _ensure_sorted_unique(
            self.forbidden_future_artifact_kinds,
            field_name="forbidden_future_artifact_kinds",
        )
        forbidden_future = set(self.forbidden_future_artifact_kinds)
        missing_future = sorted(
            PB_ATTEMPT_0A_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS - forbidden_future
        )
        if missing_future:
            raise ValueError(f"guardrail missing future artifact kinds: {missing_future}")
        current_kinds = sorted(PB_ATTEMPT_0A_ARTIFACT_KINDS & forbidden_future)
        if current_kinds:
            raise ValueError(f"guardrail cannot forbid current A artifact kinds: {current_kinds}")
        return self


class ProgrambenchReconstructionAttemptCapturedOutputRow(_AttemptBase):
    captured_output_ref: str
    output_kind: Literal[
        "worker_declared_candidate_file",
        "worker_stderr",
        "worker_stdout",
        "worker_transcript",
    ]
    capture_posture: Literal["captured_local_worker_output_only"]
    limitation_note: str


class ProgrambenchReconstructionAttemptDeclaredUncertaintyRow(_AttemptBase):
    uncertainty_ref: str
    uncertainty_kind: Literal[
        "behavior_gap_declared",
        "implementation_gap_declared",
        "probe_expectation_gap_declared",
    ]
    uncertainty_posture: Literal["worker_declared_uncertainty_not_remand_authority"]
    evidence_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_uncertainty_row(
        self,
    ) -> "ProgrambenchReconstructionAttemptDeclaredUncertaintyRow":
        _ensure_sorted_unique(self.evidence_refs, field_name="uncertainty evidence_refs")
        return self


class ProgrambenchReconstructionAttemptForbiddenContentScreeningRow(_AttemptBase):
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
    def _validate_screening_row(
        self,
    ) -> "ProgrambenchReconstructionAttemptForbiddenContentScreeningRow":
        _ensure_sorted_unique(self.evidence_refs, field_name="screening evidence_refs")
        return self


class ProgrambenchReconstructionAttemptOutputHashRow(_AttemptBase):
    output_hash_ref: str
    captured_output_ref: str
    output_hash: str
    hash_role: Literal["local_worker_output_hash"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_output_hash_row(self) -> "ProgrambenchReconstructionAttemptOutputHashRow":
        _ensure_hash(self.output_hash, field_name="output_hash")
        return self


class ProgrambenchReconstructionAttemptBoundedExcerptRow(_AttemptBase):
    excerpt_ref: str
    captured_output_ref: str
    excerpt_text: str = Field(max_length=512)
    excerpt_posture: Literal["bounded_debug_excerpt_not_complete_output_identity"]
    limitation_note: str


class ProgrambenchReconstructionAttemptWorkerInvocationRecord(_AttemptBase):
    schema_id: Literal[PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_WORKER_INVOCATION_RECORD_SCHEMA] = Field(
        alias="schema"
    )
    worker_invocation_ref: str
    attempt_request_ref: str
    worker_input_packet_ref: str
    dispatch_preflight_ref: str
    worker_profile_ref: str
    attempt_invocation_index: int = Field(ge=1)
    input_packet_hash: str
    worker_visible_context_hash: str
    tool_manifest_ref: str
    allowed_tool_manifest_hash: str
    forbidden_tool_manifest_hash: str
    invocation_kind: Literal["local_cleanroom_worker_invocation"]
    invocation_start_posture: Literal["started_after_preflight_passed"]
    invocation_completion_posture: Literal[
        "completed_with_output_capture",
        "failed_with_output_capture",
        "blocked_before_invocation",
    ]
    tool_access_posture: Literal["released_tool_manifest_only"]
    network_access_posture: Literal["network_disabled"]
    source_lookup_posture: Literal["source_lookup_forbidden"]
    hidden_test_access_posture: Literal["hidden_tests_not_visible_not_accessed"]
    official_programbench_posture: Literal[
        "no_official_programbench_participation_by_pb_attempt_0b"
    ]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    model_ranking_posture: Literal["no_model_ranking_claimed_by_pb_attempt_0b"]
    official_submission_posture: Literal["no_official_submission_authority_by_pb_attempt_0b"]
    invocation_transcript_hash: str
    bounded_transcript_excerpt: str = Field(max_length=512)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_invocation_record(
        self,
    ) -> "ProgrambenchReconstructionAttemptWorkerInvocationRecord":
        if self.attempt_invocation_index != 1:
            raise ValueError("PB-ATTEMPT-0-B allows exactly one invocation per attempt request")
        if self.invocation_completion_posture == "blocked_before_invocation":
            raise ValueError("PB-ATTEMPT-0-B invocation records must capture an invocation")
        for field_name in (
            "input_packet_hash",
            "worker_visible_context_hash",
            "allowed_tool_manifest_hash",
            "forbidden_tool_manifest_hash",
            "invocation_transcript_hash",
        ):
            _ensure_hash(getattr(self, field_name), field_name=field_name)
        return self


class ProgrambenchReconstructionAttemptOutputCapture(_AttemptBase):
    schema_id: Literal[PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_OUTPUT_CAPTURE_SCHEMA] = Field(
        alias="schema"
    )
    output_capture_ref: str
    worker_invocation_ref: str
    attempt_request_ref: str
    captured_output_rows: list[ProgrambenchReconstructionAttemptCapturedOutputRow] = Field(
        min_length=1
    )
    declared_uncertainty_rows: list[ProgrambenchReconstructionAttemptDeclaredUncertaintyRow] = (
        Field(default_factory=list)
    )
    forbidden_content_screening_rows: list[
        ProgrambenchReconstructionAttemptForbiddenContentScreeningRow
    ] = Field(min_length=1)
    forbidden_content_screening_posture: Literal[
        "blocked_excluded_derived",
        "blocked_forbidden_source",
        "blocked_hidden_evidence",
        "blocked_postmortem_only",
        "inconclusive_requires_review",
        "passed",
    ]
    output_hash_rows: list[ProgrambenchReconstructionAttemptOutputHashRow] = Field(min_length=1)
    bounded_excerpt_rows: list[ProgrambenchReconstructionAttemptBoundedExcerptRow] = Field(
        min_length=1
    )
    output_capture_posture: Literal["captured_local_candidate_material_only"]
    candidate_materialization_authority_posture: Literal[
        "candidate_materialization_allowed_after_screening_passed",
        "candidate_materialization_blocked_by_screening",
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_output_capture(self) -> "ProgrambenchReconstructionAttemptOutputCapture":
        captured_refs = [row.captured_output_ref for row in self.captured_output_rows]
        _ensure_sorted_unique(captured_refs, field_name="captured_output_rows")
        hash_refs = [row.output_hash_ref for row in self.output_hash_rows]
        _ensure_sorted_unique(hash_refs, field_name="output_hash_rows")
        excerpt_refs = [row.excerpt_ref for row in self.bounded_excerpt_rows]
        _ensure_sorted_unique(excerpt_refs, field_name="bounded_excerpt_rows")
        screening_refs = [row.screening_ref for row in self.forbidden_content_screening_rows]
        _ensure_sorted_unique(screening_refs, field_name="forbidden_content_screening_rows")
        uncertainty_refs = [row.uncertainty_ref for row in self.declared_uncertainty_rows]
        if uncertainty_refs:
            _ensure_sorted_unique(uncertainty_refs, field_name="declared_uncertainty_rows")

        captured_ref_set = set(captured_refs)
        hashed_output_refs = {row.captured_output_ref for row in self.output_hash_rows}
        excerpt_output_refs = {row.captured_output_ref for row in self.bounded_excerpt_rows}
        if hashed_output_refs != captured_ref_set:
            raise ValueError("output hash rows must cover exactly captured output rows")
        if excerpt_output_refs != captured_ref_set:
            raise ValueError("bounded excerpt rows must cover exactly captured output rows")

        blocked_rows = [
            row
            for row in self.forbidden_content_screening_rows
            if row.screening_posture == "blocked"
        ]
        if self.forbidden_content_screening_posture == "passed":
            if blocked_rows:
                blocked_refs = [row.screening_ref for row in blocked_rows]
                raise ValueError(
                    f"passed forbidden-content screening cannot carry blocked rows: {blocked_refs}"
                )
            if (
                self.candidate_materialization_authority_posture
                != "candidate_materialization_allowed_after_screening_passed"
            ):
                raise ValueError("passed screening must allow later candidate materialization")
            return self

        if (
            self.candidate_materialization_authority_posture
            != "candidate_materialization_blocked_by_screening"
        ):
            raise ValueError("non-passing screening must block candidate materialization")
        blocked_posture_kind = {
            "blocked_excluded_derived": "excluded_derived_content",
            "blocked_forbidden_source": "forbidden_source_content",
            "blocked_hidden_evidence": "hidden_evidence_content",
            "blocked_postmortem_only": "postmortem_only_content",
        }
        expected_kind = blocked_posture_kind.get(self.forbidden_content_screening_posture)
        if expected_kind is None:
            if blocked_rows:
                raise ValueError("inconclusive screening posture cannot carry blocked rows")
            return self
        if not any(row.screening_kind == expected_kind for row in blocked_rows):
            raise ValueError(
                f"{self.forbidden_content_screening_posture} requires a matching blocked row"
            )
        return self


class ProgrambenchReconstructionAttemptMaterializedFileRow(_AttemptBase):
    materialized_file_ref: str
    path_ref: str
    file_role: Literal[
        "candidate_config_file",
        "candidate_source_file",
        "candidate_support_file",
        "generated_output_artifact",
    ]
    write_scope_ref: str
    materialization_posture: Literal["local_sandbox_materialized_file"]
    limitation_note: str


class ProgrambenchReconstructionAttemptGeneratedFileHashRow(_AttemptBase):
    generated_file_hash_ref: str
    materialized_file_ref: str
    content_hash: str
    hash_role: Literal["materialized_candidate_content_hash"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_generated_hash_row(
        self,
    ) -> "ProgrambenchReconstructionAttemptGeneratedFileHashRow":
        _ensure_hash(self.content_hash, field_name="content_hash")
        return self


class ProgrambenchReconstructionAttemptCandidateMaterialization(_AttemptBase):
    schema_id: Literal[PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_CANDIDATE_MATERIALIZATION_SCHEMA] = (
        Field(alias="schema")
    )
    candidate_materialization_ref: str
    attempt_request_ref: str
    output_capture_ref: str
    sandbox_policy_ref: str
    materialization_input_hash: str
    materialization_output_manifest_hash: str
    materialized_file_rows: list[ProgrambenchReconstructionAttemptMaterializedFileRow] = Field(
        min_length=1
    )
    generated_file_hash_rows: list[ProgrambenchReconstructionAttemptGeneratedFileHashRow] = Field(
        min_length=1
    )
    write_scope_ref: str
    write_scope_attestation_ref: str
    official_submission_posture: Literal["no_official_submission_authority_by_pb_attempt_0b"]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    materialized_inside_write_scope: Literal[True]
    materialization_posture: Literal["local_candidate_materialized_inside_sandbox_write_scope"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_candidate_materialization(
        self,
    ) -> "ProgrambenchReconstructionAttemptCandidateMaterialization":
        _ensure_hash(self.materialization_input_hash, field_name="materialization_input_hash")
        _ensure_hash(
            self.materialization_output_manifest_hash,
            field_name="materialization_output_manifest_hash",
        )
        file_refs = [row.materialized_file_ref for row in self.materialized_file_rows]
        _ensure_sorted_unique(file_refs, field_name="materialized_file_rows")
        path_refs = [row.path_ref for row in self.materialized_file_rows]
        _ensure_sorted_unique(path_refs, field_name="materialized_file_paths")
        hash_refs = [row.generated_file_hash_ref for row in self.generated_file_hash_rows]
        _ensure_sorted_unique(hash_refs, field_name="generated_file_hash_rows")
        hashed_file_refs = {row.materialized_file_ref for row in self.generated_file_hash_rows}
        if hashed_file_refs != set(file_refs):
            raise ValueError("generated file hash rows must cover exactly materialized files")
        write_scope_refs = {row.write_scope_ref for row in self.materialized_file_rows}
        if write_scope_refs != {self.write_scope_ref}:
            raise ValueError("materialized file rows must use the declared write scope")
        return self


class ProgrambenchReconstructionAttemptApplicationStepRow(_AttemptBase):
    application_step_ref: str
    step_index: int = Field(ge=0)
    step_kind: Literal[
        "candidate_materialization",
        "filesystem_manifest_capture",
        "sandbox_absence_attestation",
        "sandbox_policy_application",
    ]
    step_posture: Literal["passed"]
    evidence_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_application_step_row(
        self,
    ) -> "ProgrambenchReconstructionAttemptApplicationStepRow":
        _ensure_sorted_unique(self.evidence_refs, field_name="application step evidence_refs")
        return self


class ProgrambenchReconstructionAttemptSandboxApplicationTrace(_AttemptBase):
    schema_id: Literal[PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_SANDBOX_APPLICATION_TRACE_SCHEMA] = (
        Field(alias="schema")
    )
    sandbox_application_trace_ref: str
    attempt_request_ref: str
    candidate_materialization_ref: str
    sandbox_policy_ref: str
    run_budget_ref: str
    application_step_rows: list[ProgrambenchReconstructionAttemptApplicationStepRow] = Field(
        min_length=1
    )
    pre_state_manifest_ref: str
    post_state_manifest_ref: str
    fs_diff_ref: str
    network_attestation_ref: str
    secret_absence_attestation_ref: str
    docker_socket_absence_attestation_ref: str
    source_lookup_absence_attestation_ref: str
    application_posture: Literal["local_sandbox_application_recorded"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_sandbox_application_trace(
        self,
    ) -> "ProgrambenchReconstructionAttemptSandboxApplicationTrace":
        step_refs = [row.application_step_ref for row in self.application_step_rows]
        _ensure_sorted_unique(step_refs, field_name="application_step_rows")
        indices = [row.step_index for row in self.application_step_rows]
        if indices != sorted(indices):
            raise ValueError("application step rows must be sorted by step_index")
        if indices != list(range(len(indices))):
            raise ValueError("application step rows must use contiguous step_index values")
        return self


def _excluded_refs_by_category(
    manifest: ProgrambenchReconstructionContextExclusionManifest,
) -> dict[str, list[str]]:
    return {
        "excluded_derived_summary": manifest.excluded_derived_summary_refs,
        "forbidden_source": manifest.forbidden_source_refs,
        "postmortem_only": manifest.postmortem_only_refs,
        "worker_hidden_source": manifest.worker_hidden_source_refs,
    }


def _validate_result_summary_compatible(
    *,
    attempt_request: ProgrambenchReconstructionAttemptRequest,
    result_summary: ProgrambenchReconstructionResultSummary,
) -> None:
    if result_summary.result_posture in _BLOCKED_RESULT_POSTURES:
        raise ValueError("attempt requests require compatible PB-RECON-0 result summary posture")
    if result_summary.result_posture not in _COMPATIBLE_RESULT_POSTURES:
        raise ValueError("attempt requests require compatible PB-RECON-0 result summary posture")
    if (
        result_summary.result_posture == "blocked_by_missing_evidence"
        and attempt_request.attempt_purpose != "local_evidence_gap_remediation_attempt"
    ):
        raise ValueError(
            "blocked-by-missing-evidence summaries require evidence-gap remediation attempts"
        )
    if (
        result_summary.result_posture == "local_remand_required"
        and attempt_request.attempt_purpose != "local_remand_correction_attempt"
    ):
        raise ValueError("remanded summaries require local remand correction attempts")


def validate_pb_attempt_0a_attempt_bundle(
    *,
    work_order: ProgrambenchReconstructionWorkOrder,
    worker_context_packet: ProgrambenchReconstructionWorkerContextPacket,
    context_exclusion_manifest: ProgrambenchReconstructionContextExclusionManifest,
    sandbox_policy: ProgrambenchReconstructionSandboxPolicy,
    run_budget: ProgrambenchReconstructionRunBudget,
    workbench_guardrail: ProgrambenchReconstructionWorkbenchNonAuthorityGuardrail,
    result_summary: ProgrambenchReconstructionResultSummary,
    workbench_family_closeout: ProgrambenchReconstructionWorkbenchFamilyCloseoutAlignment,
    attempt_request: ProgrambenchReconstructionAttemptRequest,
    worker_input_packet: ProgrambenchReconstructionAttemptWorkerInputPacket,
    dispatch_preflight: ProgrambenchReconstructionAttemptDispatchPreflight,
    guardrail: ProgrambenchReconstructionAttemptNonAuthorityGuardrail,
) -> None:
    if work_order.worker_context_packet_ref != worker_context_packet.worker_context_packet_ref:
        raise ValueError("work order must reference worker context packet")
    if work_order.context_exclusion_manifest_ref != (
        context_exclusion_manifest.context_exclusion_manifest_ref
    ):
        raise ValueError("work order must reference context exclusion manifest")
    if work_order.sandbox_policy_ref != sandbox_policy.sandbox_policy_ref:
        raise ValueError("work order must reference sandbox policy")
    if work_order.run_budget_ref != run_budget.run_budget_ref:
        raise ValueError("work order must reference run budget")
    if worker_context_packet.work_order_ref != work_order.work_order_ref:
        raise ValueError("worker context packet must reference work order")
    if context_exclusion_manifest.work_order_ref != work_order.work_order_ref:
        raise ValueError("context exclusion manifest must reference work order")
    if sandbox_policy.work_order_ref != work_order.work_order_ref:
        raise ValueError("sandbox policy must reference work order")
    if run_budget.work_order_ref != work_order.work_order_ref:
        raise ValueError("run budget must reference work order")
    if result_summary.work_order_ref != work_order.work_order_ref:
        raise ValueError("result summary must reference work order")
    if workbench_guardrail.guardrail_ref not in work_order.guardrail_refs:
        raise ValueError("work order must reference released workbench guardrail")
    if work_order.work_order_ref not in workbench_guardrail.work_order_refs:
        raise ValueError("workbench guardrail must reference work order")
    if work_order.work_order_ref not in workbench_family_closeout.work_order_refs:
        raise ValueError("workbench closeout must release work order ref")
    if result_summary.result_summary_ref not in workbench_family_closeout.result_summary_refs:
        raise ValueError("workbench closeout must release result summary ref")

    _validate_result_summary_compatible(
        attempt_request=attempt_request,
        result_summary=result_summary,
    )

    if attempt_request.work_order_ref != work_order.work_order_ref:
        raise ValueError("attempt request must reference work order")
    if attempt_request.worker_context_packet_ref != (
        worker_context_packet.worker_context_packet_ref
    ):
        raise ValueError("attempt request must reference worker context packet")
    if attempt_request.context_exclusion_manifest_ref != (
        context_exclusion_manifest.context_exclusion_manifest_ref
    ):
        raise ValueError("attempt request must reference context exclusion manifest")
    if attempt_request.sandbox_policy_ref != sandbox_policy.sandbox_policy_ref:
        raise ValueError("attempt request must reference sandbox policy")
    if attempt_request.run_budget_ref != run_budget.run_budget_ref:
        raise ValueError("attempt request must reference run budget")
    if attempt_request.result_summary_ref != result_summary.result_summary_ref:
        raise ValueError("attempt request must reference result summary")
    if attempt_request.workbench_family_closeout_ref != (
        workbench_family_closeout.family_closeout_ref
    ):
        raise ValueError("attempt request must reference workbench family closeout")

    if worker_input_packet.attempt_request_ref != attempt_request.attempt_request_ref:
        raise ValueError("worker input packet must reference attempt request")
    if worker_input_packet.work_order_ref != work_order.work_order_ref:
        raise ValueError("worker input packet must reference work order")
    if worker_input_packet.worker_context_packet_ref != (
        worker_context_packet.worker_context_packet_ref
    ):
        raise ValueError("worker input packet must reference worker context packet")
    if worker_input_packet.context_exclusion_manifest_ref != (
        context_exclusion_manifest.context_exclusion_manifest_ref
    ):
        raise ValueError("worker input packet must reference exclusion manifest")

    _ensure_refs_resolve(
        worker_input_packet.worker_visible_source_refs,
        set(worker_context_packet.worker_visible_source_refs),
        field_name="worker_visible_source_refs",
        allowed_name="released worker context source refs",
    )
    _ensure_refs_resolve(
        worker_input_packet.advisory_concept_profile_refs,
        set(worker_context_packet.concept_profile_refs),
        field_name="advisory_concept_profile_refs",
        allowed_name="released worker context concept profile refs",
    )
    _ensure_refs_resolve(
        worker_input_packet.advisory_realization_refs,
        set(worker_context_packet.advisory_realization_refs),
        field_name="advisory_realization_refs",
        allowed_name="released worker context realization refs",
    )
    _ensure_refs_resolve(
        worker_input_packet.probe_expectation_refs,
        set(worker_context_packet.probe_observation_refs),
        field_name="probe_expectation_refs",
        allowed_name="released worker context probe observation refs",
    )
    _ensure_refs_resolve(
        worker_input_packet.sandbox_summary_refs,
        {sandbox_policy.sandbox_policy_ref},
        field_name="sandbox_summary_refs",
        allowed_name="sandbox policy refs",
    )
    _ensure_refs_resolve(
        worker_input_packet.run_budget_summary_refs,
        {run_budget.run_budget_ref},
        field_name="run_budget_summary_refs",
        allowed_name="run budget refs",
    )

    excluded_refs = set(context_exclusion_manifest.all_excluded_refs())
    leaked_refs = worker_input_packet.all_worker_visible_refs() & excluded_refs
    if leaked_refs:
        raise ValueError(
            f"worker input packet contains auditor-only or forbidden refs: {sorted(leaked_refs)}"
        )
    excluded_by_category = _excluded_refs_by_category(context_exclusion_manifest)
    expected_categories = {category for category, refs in excluded_by_category.items() if refs}
    observed_categories = {
        row.exclusion_category for row in worker_input_packet.excluded_ref_summary_rows
    }
    if observed_categories != expected_categories:
        raise ValueError("excluded ref summaries must cover exactly non-empty exclusion categories")
    for row in worker_input_packet.excluded_ref_summary_rows:
        expected_count = len(excluded_by_category[row.exclusion_category])
        if row.excluded_ref_count != expected_count:
            raise ValueError("excluded ref summary counts must match exclusion manifest")

    if dispatch_preflight.attempt_request_ref != attempt_request.attempt_request_ref:
        raise ValueError("dispatch preflight must reference attempt request")
    if dispatch_preflight.worker_input_packet_ref != (worker_input_packet.worker_input_packet_ref):
        raise ValueError("dispatch preflight must reference worker input packet")
    if dispatch_preflight.sandbox_policy_ref != sandbox_policy.sandbox_policy_ref:
        raise ValueError("dispatch preflight must reference sandbox policy")
    if dispatch_preflight.run_budget_ref != run_budget.run_budget_ref:
        raise ValueError("dispatch preflight must reference run budget")
    if dispatch_preflight.guardrail_ref != guardrail.guardrail_ref:
        raise ValueError("dispatch preflight must reference guardrail")
    missing_witnesses = sorted(
        _REQUIRED_SANDBOX_WITNESSES - set(dispatch_preflight.sandbox_enforcement_requirement_refs)
    )
    if missing_witnesses:
        raise ValueError(f"dispatch preflight missing sandbox witnesses: {missing_witnesses}")
    missing_policy_witnesses = sorted(
        set(dispatch_preflight.sandbox_enforcement_requirement_refs)
        - set(sandbox_policy.sandbox_enforcement_witness_requirements)
    )
    if missing_policy_witnesses:
        raise ValueError(
            "dispatch preflight sandbox witnesses must be required by sandbox policy: "
            f"{missing_policy_witnesses}"
        )
    missing_budget_witnesses = sorted(
        _REQUIRED_BUDGET_WITNESSES - set(dispatch_preflight.budget_enforcement_requirement_refs)
    )
    if missing_budget_witnesses:
        raise ValueError(f"dispatch preflight missing budget witnesses: {missing_budget_witnesses}")
    expected_budget_witnesses = {
        f"{run_budget.filesystem_budget_policy}",
        f"{run_budget.timeout_budget_policy}",
        f"{run_budget.token_budget_policy}",
        "max_candidate_artifact_count_declared",
        "max_local_run_count_declared",
        "max_probe_run_count_declared",
        "max_remand_count_declared",
    }
    unknown_budget_witnesses = sorted(
        set(dispatch_preflight.budget_enforcement_requirement_refs) - expected_budget_witnesses
    )
    if unknown_budget_witnesses:
        raise ValueError(
            "dispatch preflight budget witnesses must be required by run budget: "
            f"{unknown_budget_witnesses}"
        )

    if guardrail.attempt_request_ref != attempt_request.attempt_request_ref:
        raise ValueError("guardrail must reference attempt request")


def validate_pb_attempt_0b_invocation_bundle(
    *,
    attempt_request: ProgrambenchReconstructionAttemptRequest,
    worker_input_packet: ProgrambenchReconstructionAttemptWorkerInputPacket,
    dispatch_preflight: ProgrambenchReconstructionAttemptDispatchPreflight,
    guardrail: ProgrambenchReconstructionAttemptNonAuthorityGuardrail,
    sandbox_policy: ProgrambenchReconstructionSandboxPolicy,
    run_budget: ProgrambenchReconstructionRunBudget,
    worker_invocation_record: ProgrambenchReconstructionAttemptWorkerInvocationRecord,
    output_capture: ProgrambenchReconstructionAttemptOutputCapture,
    candidate_materialization: ProgrambenchReconstructionAttemptCandidateMaterialization,
    sandbox_application_trace: ProgrambenchReconstructionAttemptSandboxApplicationTrace,
) -> None:
    if worker_input_packet.attempt_request_ref != attempt_request.attempt_request_ref:
        raise ValueError("worker input packet must reference attempt request")
    if dispatch_preflight.attempt_request_ref != attempt_request.attempt_request_ref:
        raise ValueError("dispatch preflight must reference attempt request")
    if dispatch_preflight.worker_input_packet_ref != worker_input_packet.worker_input_packet_ref:
        raise ValueError("dispatch preflight must reference worker input packet")
    if dispatch_preflight.guardrail_ref != guardrail.guardrail_ref:
        raise ValueError("dispatch preflight must reference guardrail")
    if guardrail.attempt_request_ref != attempt_request.attempt_request_ref:
        raise ValueError("guardrail must reference attempt request")
    if dispatch_preflight.preflight_posture != ("preflight_passed_for_later_local_attempt_review"):
        raise ValueError("PB-ATTEMPT-0-B invocation requires a passed A preflight")

    if worker_invocation_record.attempt_request_ref != attempt_request.attempt_request_ref:
        raise ValueError("worker invocation must reference attempt request")
    if worker_invocation_record.worker_input_packet_ref != (
        worker_input_packet.worker_input_packet_ref
    ):
        raise ValueError("worker invocation must reference worker input packet")
    if worker_invocation_record.dispatch_preflight_ref != dispatch_preflight.dispatch_preflight_ref:
        raise ValueError("worker invocation must reference dispatch preflight")
    if worker_invocation_record.worker_profile_ref != attempt_request.worker_profile_ref:
        raise ValueError("worker invocation must preserve worker profile")
    if worker_invocation_record.input_packet_hash != worker_input_packet.worker_input_manifest_hash:
        raise ValueError("worker invocation input hash must match worker input packet manifest")

    if output_capture.worker_invocation_ref != worker_invocation_record.worker_invocation_ref:
        raise ValueError("output capture must reference worker invocation")
    if output_capture.attempt_request_ref != attempt_request.attempt_request_ref:
        raise ValueError("output capture must reference attempt request")

    if output_capture.forbidden_content_screening_posture != "passed":
        raise ValueError("candidate materialization requires passed forbidden-content screening")
    if (
        output_capture.candidate_materialization_authority_posture
        != "candidate_materialization_allowed_after_screening_passed"
    ):
        raise ValueError("candidate materialization requires screening-passed authority posture")

    if candidate_materialization.attempt_request_ref != attempt_request.attempt_request_ref:
        raise ValueError("candidate materialization must reference attempt request")
    if candidate_materialization.output_capture_ref != output_capture.output_capture_ref:
        raise ValueError("candidate materialization must reference output capture")
    candidate_output_refs = [
        row.captured_output_ref
        for row in output_capture.captured_output_rows
        if row.output_kind == "worker_declared_candidate_file"
    ]
    if len(candidate_output_refs) != 1:
        raise ValueError("output capture must contain exactly one worker candidate-file output")
    candidate_output_ref = candidate_output_refs[0]
    candidate_output_hashes = [
        row.output_hash
        for row in output_capture.output_hash_rows
        if row.captured_output_ref == candidate_output_ref
    ]
    if len(candidate_output_hashes) != 1:
        raise ValueError("candidate-file output must have exactly one output hash")
    if candidate_materialization.materialization_input_hash != candidate_output_hashes[0]:
        raise ValueError(
            "candidate materialization input hash must match screened candidate-file output hash"
        )
    if candidate_materialization.sandbox_policy_ref != sandbox_policy.sandbox_policy_ref:
        raise ValueError("candidate materialization must reference sandbox policy")
    if candidate_materialization.sandbox_policy_ref != attempt_request.sandbox_policy_ref:
        raise ValueError("candidate materialization must preserve attempt sandbox policy")
    if len(candidate_materialization.materialized_file_rows) > (
        run_budget.max_candidate_artifact_count
    ):
        raise ValueError("candidate materialization exceeds candidate artifact budget")
    allowed_write_scope_refs = set(sandbox_policy.allowed_write_scope_refs)
    if candidate_materialization.write_scope_ref not in allowed_write_scope_refs:
        raise ValueError("candidate materialization write scope must be allowed by sandbox policy")
    row_write_scope_refs = {
        row.write_scope_ref for row in candidate_materialization.materialized_file_rows
    }
    unallowed_write_scope_refs = row_write_scope_refs - allowed_write_scope_refs
    if unallowed_write_scope_refs:
        raise ValueError(
            "candidate materialization file write scopes must be allowed by sandbox policy: "
            f"{sorted(unallowed_write_scope_refs)}"
        )

    if sandbox_application_trace.attempt_request_ref != attempt_request.attempt_request_ref:
        raise ValueError("sandbox trace must reference attempt request")
    if sandbox_application_trace.candidate_materialization_ref != (
        candidate_materialization.candidate_materialization_ref
    ):
        raise ValueError("sandbox trace must reference candidate materialization")
    if sandbox_application_trace.sandbox_policy_ref != sandbox_policy.sandbox_policy_ref:
        raise ValueError("sandbox trace must reference sandbox policy")
    if sandbox_application_trace.run_budget_ref != run_budget.run_budget_ref:
        raise ValueError("sandbox trace must reference run budget")
    if sandbox_application_trace.sandbox_policy_ref != attempt_request.sandbox_policy_ref:
        raise ValueError("sandbox trace must preserve attempt sandbox policy")
    if sandbox_application_trace.run_budget_ref != attempt_request.run_budget_ref:
        raise ValueError("sandbox trace must preserve attempt run budget")
