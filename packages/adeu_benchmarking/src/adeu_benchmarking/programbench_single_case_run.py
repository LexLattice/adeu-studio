from __future__ import annotations

import re
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

from .programbench_cleanroom_matrix_inclusion import (
    ProgrambenchLocalMatrixInclusionFamilyCloseoutAlignment,
    ProgrambenchLocalMatrixRevisionReadinessSummary,
    ProgrambenchLocalMatrixRevisionRegistration,
)

MODEL_CONFIG = ConfigDict(
    extra="forbid",
    frozen=True,
    populate_by_name=True,
    protected_namespaces=(),
)

PROGRAMBENCH_SINGLE_CASE_RUN_REQUEST_SCHEMA = "programbench_single_case_run_request@1"
PROGRAMBENCH_SINGLE_CASE_TARGET_SELECTION_SCHEMA = (
    "programbench_single_case_target_selection@1"
)
PROGRAMBENCH_SINGLE_CASE_EXECUTION_PREFLIGHT_SCHEMA = (
    "programbench_single_case_execution_preflight@1"
)
PROGRAMBENCH_SINGLE_CASE_RUN_CONTROL_CONTRACT_SCHEMA = (
    "programbench_single_case_run_control_contract@1"
)
PROGRAMBENCH_SINGLE_CASE_RUN_NON_AUTHORITY_GUARDRAIL_SCHEMA = (
    "programbench_single_case_run_non_authority_guardrail@1"
)

PROGRAMBENCH_SINGLE_CASE_WORKER_DISPATCH_SPECIMEN_SCHEMA = (
    "programbench_single_case_worker_dispatch_specimen@1"
)
PROGRAMBENCH_SINGLE_CASE_EXECUTION_TRACE_SCHEMA = (
    "programbench_single_case_execution_trace@1"
)
PROGRAMBENCH_SINGLE_CASE_PROBE_OBSERVATION_BUNDLE_SCHEMA = (
    "programbench_single_case_probe_observation_bundle@1"
)
PROGRAMBENCH_SINGLE_CASE_CANDIDATE_ARTIFACT_CAPTURE_SCHEMA = (
    "programbench_single_case_candidate_artifact_capture@1"
)
PROGRAMBENCH_SINGLE_CASE_LIFECYCLE_PROJECTION_SCHEMA = (
    "programbench_single_case_lifecycle_projection@1"
)
PROGRAMBENCH_SINGLE_CASE_LOCAL_OUTCOME_AUDIT_SCHEMA = (
    "programbench_single_case_local_outcome_audit@1"
)
PROGRAMBENCH_SINGLE_CASE_RUN_OBSERVATION_SUMMARY_SCHEMA = (
    "programbench_single_case_run_observation_summary@1"
)
PROGRAMBENCH_SINGLE_CASE_REMAND_OR_ACCEPTANCE_DECISION_SCHEMA = (
    "programbench_single_case_remand_or_acceptance_decision@1"
)
PROGRAMBENCH_SINGLE_CASE_RUN_HANDOFF_SCHEMA = "programbench_single_case_run_handoff@1"
PROGRAMBENCH_SINGLE_CASE_RUN_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA = (
    "programbench_single_case_run_family_closeout_alignment@1"
)

PB_SINGLE_CASE_RUN_0A_ARTIFACT_KINDS = {
    PROGRAMBENCH_SINGLE_CASE_RUN_REQUEST_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_TARGET_SELECTION_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_EXECUTION_PREFLIGHT_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_RUN_CONTROL_CONTRACT_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_RUN_NON_AUTHORITY_GUARDRAIL_SCHEMA,
}
PB_SINGLE_CASE_RUN_0B_ARTIFACT_KINDS = {
    PROGRAMBENCH_SINGLE_CASE_WORKER_DISPATCH_SPECIMEN_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_EXECUTION_TRACE_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_PROBE_OBSERVATION_BUNDLE_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_CANDIDATE_ARTIFACT_CAPTURE_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_LIFECYCLE_PROJECTION_SCHEMA,
}
PB_SINGLE_CASE_RUN_0C_ARTIFACT_KINDS = {
    PROGRAMBENCH_SINGLE_CASE_LOCAL_OUTCOME_AUDIT_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_RUN_OBSERVATION_SUMMARY_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_REMAND_OR_ACCEPTANCE_DECISION_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_RUN_HANDOFF_SCHEMA,
    PROGRAMBENCH_SINGLE_CASE_RUN_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
}
PB_SINGLE_CASE_RUN_0A_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS = (
    PB_SINGLE_CASE_RUN_0B_ARTIFACT_KINDS | PB_SINGLE_CASE_RUN_0C_ARTIFACT_KINDS
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
    "leaderboard",
    "model-ranking",
    "official-evaluator",
    "official-submission",
    "original-source",
    "postmortem-only",
    "source-lookup",
)
_SOFT_RESULT_LANGUAGE_MARKERS = (
    "baseline comparison",
    "baseline win",
    "benchmark score",
    "case score",
    "leaderboard",
    "model improved",
    "model ranking",
    "pass rate",
    "passed programbench",
    "representative result",
    "solve rate",
    "solved the case",
    "success rate",
)
_REQUIRED_B_WITNESS_REFS = [
    "decompilation_absence_witness_ref",
    "docker_socket_absence_witness_ref",
    "network_mode_witness_ref",
    "sandbox_attestation_bundle_ref",
    "sandbox_instance_ref",
    "secret_absence_witness_ref",
    "source_lookup_absence_witness_ref",
    "write_scope_attestation_ref",
]


def _ensure_non_empty_trimmed(values: list[str], *, field_name: str) -> None:
    for value in values:
        if not isinstance(value, str) or not value or value != value.strip():
            raise ValueError(f"{field_name} entries must be non-empty trimmed strings")


def _ensure_sorted_unique(values: list[str], *, field_name: str) -> None:
    if not values:
        raise ValueError(f"{field_name} must contain at least one entry")
    _ensure_non_empty_trimmed(values, field_name=field_name)
    if len(values) != len(set(values)):
        raise ValueError(f"{field_name} must not contain duplicates")
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
        ref
        for ref in values
        if any(marker in ref.lower() for marker in _FORBIDDEN_REF_MARKERS)
    )
    if leaked:
        raise ValueError(f"{field_name} contains forbidden single-case-run refs: {leaked}")


def _ensure_no_result_language(value: str, *, field_name: str) -> None:
    lowered = value.lower()
    leaked = [marker for marker in _SOFT_RESULT_LANGUAGE_MARKERS if marker in lowered]
    if leaked:
        raise ValueError(
            f"{field_name} contains benchmark-like result or comparison language: {leaked}"
        )


class _SingleCaseRunBase(BaseModel):
    model_config = MODEL_CONFIG


class ProgrambenchSingleCaseRunRationaleRow(_SingleCaseRunBase):
    run_rationale_ref: str
    rationale_kind: Literal[
        "matrix_member_local_run_probe",
        "ready_expanded_case_lineage_exception",
        "direct_adapter_case_exception",
    ]
    selected_case_lineage_ref: str
    rationale_scope_posture: Literal[
        "local_single_case_run_selection_only_not_benchmark_result"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_row(self) -> "ProgrambenchSingleCaseRunRationaleRow":
        _ensure_no_forbidden_refs(
            [self.run_rationale_ref, self.selected_case_lineage_ref],
            field_name="run_rationale_refs",
        )
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCasePreflightCheckRow(_SingleCaseRunBase):
    preflight_check_ref: str
    check_kind: Literal[
        "network_disabled",
        "source_lookup_disabled",
        "decompilation_disabled",
        "docker_socket_absent",
        "host_secret_absent",
        "tool_manifest_closed",
        "write_scope_bounded",
        "run_budget_bounded",
        "local_probe_basis_declared",
    ]
    check_status: Literal["passed_for_preflight_review", "blocked"]
    blocker_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_row(self) -> "ProgrambenchSingleCasePreflightCheckRow":
        _ensure_sorted_unique_allow_empty(self.blocker_refs, field_name="blocker_refs")
        _ensure_no_forbidden_refs(
            [self.preflight_check_ref, *self.blocker_refs],
            field_name="preflight_check_refs",
        )
        if self.check_status == "passed_for_preflight_review" and self.blocker_refs:
            raise ValueError("passed preflight checks cannot carry blockers")
        if self.check_status == "blocked" and not self.blocker_refs:
            raise ValueError("blocked preflight checks require blocker refs")
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseForbiddenAuthorityRow(_SingleCaseRunBase):
    forbidden_authority_ref: str
    authority_kind: Literal[
        "baseline_comparison",
        "batch_execution",
        "benchmark_score",
        "benchmark_truth",
        "candidate_artifact_capture",
        "command_execution",
        "future_family_selection",
        "hidden_test_inference",
        "lifecycle_projection",
        "local_outcome_audit",
        "model_ranking",
        "official_programbench_participation",
        "official_submission",
        "probe_execution",
        "retry_authority",
        "worker_dispatch",
    ]
    forbiddance_posture: Literal["forbidden_by_pb_single_case_run_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_row(self) -> "ProgrambenchSingleCaseForbiddenAuthorityRow":
        _ensure_no_forbidden_refs(
            [self.forbidden_authority_ref],
            field_name="forbidden_authority_refs",
        )
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseRunRequest(_SingleCaseRunBase):
    schema_id: Literal[PROGRAMBENCH_SINGLE_CASE_RUN_REQUEST_SCHEMA] = Field(
        alias="schema"
    )
    single_case_run_request_ref: str
    requested_case_lineage_ref: str
    requested_case_lineage_hash: str
    request_source_family_ref: str
    request_source_closeout_ref: str
    single_case_run_relation_to_prior_lifecycle: Literal[
        "matrix_member_run",
        "expanded_case_lineage_run",
        "direct_adapter_case_run_exception",
    ]
    target_origin_route: Literal[
        "matrix_member",
        "ready_expanded_case_lineage",
        "direct_adapter_case_exception",
    ]
    target_origin_justification: str
    target_origin_exception_posture: Literal[
        "not_applicable_matrix_member_route",
        "not_applicable_ready_expanded_case_lineage_route",
        "direct_adapter_case_exception_declared_with_non_matrix_lineage_warning",
    ]
    run_horizon: Literal["local_single_case_cleanroom_specimen_preflight_only"]
    run_rationale_rows: list[ProgrambenchSingleCaseRunRationaleRow] = Field(
        min_length=1
    )
    single_case_only_posture: Literal["exactly_one_case_lineage_selected"]
    official_programbench_posture: Literal[
        "no_official_programbench_authority_granted_by_pb_single_case_run_0a"
    ]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    baseline_comparison_authority_posture: Literal[
        "no_baseline_comparison_authority_granted_by_pb_single_case_run_0a"
    ]
    model_ranking_authority_posture: Literal[
        "no_model_ranking_authority_granted_by_pb_single_case_run_0a"
    ]
    batch_execution_authority_posture: Literal[
        "no_batch_execution_authority_granted_by_pb_single_case_run_0a"
    ]
    future_family_selection_posture: Literal[
        "no_future_family_selection_authority_granted_by_pb_single_case_run_0a"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_request(self) -> "ProgrambenchSingleCaseRunRequest":
        _ensure_hash(self.requested_case_lineage_hash, field_name="requested_case_lineage_hash")
        _ensure_no_forbidden_refs(
            [
                self.single_case_run_request_ref,
                self.requested_case_lineage_ref,
                self.request_source_family_ref,
                self.request_source_closeout_ref,
            ],
            field_name="single_case_run_request_refs",
        )
        expected_relation = {
            "matrix_member": "matrix_member_run",
            "ready_expanded_case_lineage": "expanded_case_lineage_run",
            "direct_adapter_case_exception": "direct_adapter_case_run_exception",
        }[self.target_origin_route]
        if self.single_case_run_relation_to_prior_lifecycle != expected_relation:
            raise ValueError("target origin route must match prior lifecycle relation")
        expected_exception_posture = {
            "matrix_member": "not_applicable_matrix_member_route",
            "ready_expanded_case_lineage": (
                "not_applicable_ready_expanded_case_lineage_route"
            ),
            "direct_adapter_case_exception": (
                "direct_adapter_case_exception_declared_with_non_matrix_lineage_warning"
            ),
        }[self.target_origin_route]
        if self.target_origin_exception_posture != expected_exception_posture:
            raise ValueError("target origin route must match exception posture")
        rationale_refs = [row.run_rationale_ref for row in self.run_rationale_rows]
        _ensure_sorted_unique(rationale_refs, field_name="run_rationale_rows")
        if not any(
            row.selected_case_lineage_ref == self.requested_case_lineage_ref
            for row in self.run_rationale_rows
        ):
            raise ValueError("run rationale rows must cover selected case lineage")
        _ensure_no_result_language(
            self.target_origin_justification,
            field_name="target_origin_justification",
        )
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseTargetSelection(_SingleCaseRunBase):
    schema_id: Literal[PROGRAMBENCH_SINGLE_CASE_TARGET_SELECTION_SCHEMA] = Field(
        alias="schema"
    )
    single_case_target_selection_ref: str
    single_case_run_request_ref: str
    selected_case_lineage_ref: str
    selected_case_lineage_hash: str
    selected_case_origin_posture: Literal[
        "released_matrix_member",
        "released_ready_expanded_case_lineage",
        "released_adapter_case_exception",
    ]
    target_origin_route: Literal[
        "matrix_member",
        "ready_expanded_case_lineage",
        "direct_adapter_case_exception",
    ]
    target_origin_required_refs: list[str] = Field(min_length=1)
    source_matrix_ref: str
    source_matrix_revision_ref: str
    source_matrix_revision_hash: str
    matrix_membership_row_ref: str
    matrix_membership_status: Literal[
        "included",
        "deferred",
        "rejected",
        "not_applicable_non_matrix_route",
    ]
    source_visibility_boundary_hash: str
    cleanroom_boundary_hash: str
    case_artifact_manifest_ref: str
    case_artifact_manifest_hash: str
    worker_visible_packet_ref: str
    worker_visible_packet_hash: str
    local_probe_basis_ref: str
    local_probe_basis_hash: str
    contamination_posture: Literal["clean", "contaminated"]
    target_selection_status: Literal[
        "selected_for_later_local_run_preflight",
        "blocked",
    ]
    target_selection_blocker_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_selection(self) -> "ProgrambenchSingleCaseTargetSelection":
        for field_name in (
            "selected_case_lineage_hash",
            "source_matrix_revision_hash",
            "source_visibility_boundary_hash",
            "cleanroom_boundary_hash",
            "case_artifact_manifest_hash",
            "worker_visible_packet_hash",
            "local_probe_basis_hash",
        ):
            _ensure_hash(getattr(self, field_name), field_name=field_name)
        _ensure_sorted_unique(
            self.target_origin_required_refs,
            field_name="target_origin_required_refs",
        )
        _ensure_sorted_unique_allow_empty(
            self.target_selection_blocker_refs,
            field_name="target_selection_blocker_refs",
        )
        _ensure_no_forbidden_refs(
            [
                self.single_case_target_selection_ref,
                self.single_case_run_request_ref,
                self.selected_case_lineage_ref,
                self.source_matrix_ref,
                self.source_matrix_revision_ref,
                self.matrix_membership_row_ref,
                self.case_artifact_manifest_ref,
                self.worker_visible_packet_ref,
                self.local_probe_basis_ref,
                *self.target_origin_required_refs,
                *self.target_selection_blocker_refs,
            ],
            field_name="single_case_target_selection_refs",
        )
        expected_origin = {
            "matrix_member": "released_matrix_member",
            "ready_expanded_case_lineage": "released_ready_expanded_case_lineage",
            "direct_adapter_case_exception": "released_adapter_case_exception",
        }[self.target_origin_route]
        if self.selected_case_origin_posture != expected_origin:
            raise ValueError("target origin route must match selected case origin posture")
        if self.target_origin_route == "matrix_member":
            if self.matrix_membership_status != "included":
                raise ValueError("matrix-member targets must have included membership status")
            if self.source_matrix_ref.startswith("not-applicable:"):
                raise ValueError("matrix-member targets require source matrix refs")
            if self.source_matrix_revision_ref.startswith("not-applicable:"):
                raise ValueError("matrix-member targets require source matrix revision refs")
        elif self.matrix_membership_status != "not_applicable_non_matrix_route":
            raise ValueError("non-matrix target routes require non-applicable membership status")
        if self.target_selection_status == "selected_for_later_local_run_preflight":
            if self.contamination_posture != "clean":
                raise ValueError("selected single-case targets must be clean")
            if self.target_selection_blocker_refs:
                raise ValueError("selected single-case targets cannot carry blockers")
        elif not self.target_selection_blocker_refs:
            raise ValueError("blocked single-case target selection requires blockers")
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseExecutionPreflight(_SingleCaseRunBase):
    schema_id: Literal[PROGRAMBENCH_SINGLE_CASE_EXECUTION_PREFLIGHT_SCHEMA] = Field(
        alias="schema"
    )
    single_case_execution_preflight_ref: str
    single_case_run_request_ref: str
    single_case_target_selection_ref: str
    runbook_ref: str
    runbook_hash: str
    sandbox_policy_ref: str
    sandbox_policy_hash: str
    sandbox_witness_requirement_refs: list[str] = Field(min_length=1)
    required_b_witness_refs: list[str] = Field(min_length=1)
    run_budget_ref: str
    run_budget_hash: str
    tool_manifest_ref: str
    tool_manifest_hash: str
    write_scope_ref: str
    write_scope_hash: str
    environment_policy_ref: str
    environment_policy_hash: str
    network_posture: Literal["disabled"]
    source_lookup_posture: Literal["disabled"]
    decompilation_posture: Literal["disabled"]
    docker_socket_posture: Literal["absent"]
    host_secret_posture: Literal["absent"]
    preflight_check_rows: list[ProgrambenchSingleCasePreflightCheckRow] = Field(
        min_length=1
    )
    preflight_status: Literal[
        "ready_for_later_local_single_case_execution_review",
        "blocked",
    ]
    preflight_scope_posture: Literal["eligibility_review_only_no_dispatch"]
    dispatch_authority_posture: Literal[
        "no_worker_dispatch_authority_granted_by_pb_single_case_run_0a"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_preflight(self) -> "ProgrambenchSingleCaseExecutionPreflight":
        for field_name in (
            "runbook_hash",
            "sandbox_policy_hash",
            "run_budget_hash",
            "tool_manifest_hash",
            "write_scope_hash",
            "environment_policy_hash",
        ):
            _ensure_hash(getattr(self, field_name), field_name=field_name)
        for field_name in ("sandbox_witness_requirement_refs", "required_b_witness_refs"):
            values = getattr(self, field_name)
            _ensure_sorted_unique(values, field_name=field_name)
        if self.sandbox_witness_requirement_refs != _REQUIRED_B_WITNESS_REFS:
            raise ValueError(
                "sandbox_witness_requirement_refs must match B witness requirements"
            )
        if self.required_b_witness_refs != _REQUIRED_B_WITNESS_REFS:
            raise ValueError("required_b_witness_refs must match B witness requirements")
        row_refs = [row.preflight_check_ref for row in self.preflight_check_rows]
        _ensure_sorted_unique(row_refs, field_name="preflight_check_rows")
        _ensure_no_forbidden_refs(
            [
                self.single_case_execution_preflight_ref,
                self.single_case_run_request_ref,
                self.single_case_target_selection_ref,
                self.runbook_ref,
                self.sandbox_policy_ref,
                self.run_budget_ref,
                self.tool_manifest_ref,
                self.write_scope_ref,
                self.environment_policy_ref,
            ],
            field_name="single_case_execution_preflight_refs",
        )
        blocked_rows = [
            row
            for row in self.preflight_check_rows
            if row.check_status == "blocked"
        ]
        if self.preflight_status == "ready_for_later_local_single_case_execution_review":
            if blocked_rows:
                raise ValueError("ready preflight cannot carry blocked checks")
        elif not blocked_rows:
            raise ValueError("blocked preflight requires at least one blocked check")
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseRunControlContract(_SingleCaseRunBase):
    schema_id: Literal[PROGRAMBENCH_SINGLE_CASE_RUN_CONTROL_CONTRACT_SCHEMA] = Field(
        alias="schema"
    )
    single_case_run_control_contract_ref: str
    single_case_run_request_ref: str
    worker_visible_packet_hash: str
    runbook_hash: str
    sandbox_policy_hash: str
    run_budget_hash: str
    tool_manifest_hash: str
    write_scope_hash: str
    local_probe_basis_hash: str
    allowed_command_policy: Literal["argv_shaped_commands_only_no_shell_strings"]
    timeout_policy: Literal["bounded_timeout_required"]
    resource_limit_policy: Literal["bounded_resources_required"]
    artifact_capture_policy: Literal["deferred_to_pb_single_case_run_0b"]
    forbidden_content_screen_policy: Literal[
        "required_before_candidate_artifact_capture"
    ]
    single_dispatch_limit_posture: Literal[
        "one_dispatch_specimen_only_if_pb_single_case_run_0b_authorized"
    ]
    local_only_probe_posture: Literal["declared_local_probes_only_not_hidden_tests"]
    official_evaluator_access_posture: Literal["no_official_evaluator_access"]
    hidden_test_access_posture: Literal["no_hidden_test_access"]
    benchmark_score_authority_posture: Literal[
        "no_benchmark_score_authority_granted_by_pb_single_case_run_0a"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_contract(self) -> "ProgrambenchSingleCaseRunControlContract":
        for field_name in (
            "worker_visible_packet_hash",
            "runbook_hash",
            "sandbox_policy_hash",
            "run_budget_hash",
            "tool_manifest_hash",
            "write_scope_hash",
            "local_probe_basis_hash",
        ):
            _ensure_hash(getattr(self, field_name), field_name=field_name)
        _ensure_no_forbidden_refs(
            [self.single_case_run_control_contract_ref, self.single_case_run_request_ref],
            field_name="single_case_run_control_contract_refs",
        )
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseRunNonAuthorityGuardrail(_SingleCaseRunBase):
    schema_id: Literal[PROGRAMBENCH_SINGLE_CASE_RUN_NON_AUTHORITY_GUARDRAIL_SCHEMA] = (
        Field(alias="schema")
    )
    single_case_run_guardrail_ref: str
    single_case_run_request_ref: str
    forbidden_authority_rows: list[ProgrambenchSingleCaseForbiddenAuthorityRow] = Field(
        min_length=1
    )
    forbidden_future_artifact_kinds: list[str] = Field(min_length=1)
    worker_dispatch_deferred_posture: Literal[
        "worker_dispatch_deferred_to_pb_single_case_run_0b"
    ]
    command_execution_deferred_posture: Literal[
        "command_execution_deferred_to_pb_single_case_run_0b"
    ]
    candidate_artifact_capture_deferred_posture: Literal[
        "candidate_artifact_capture_deferred_to_pb_single_case_run_0b"
    ]
    local_outcome_audit_deferred_posture: Literal[
        "local_outcome_audit_deferred_to_pb_single_case_run_0c"
    ]
    official_programbench_authority_posture: Literal[
        "no_official_programbench_authority_granted_by_pb_single_case_run_0a"
    ]
    benchmark_score_authority_posture: Literal[
        "no_benchmark_score_authority_granted_by_pb_single_case_run_0a"
    ]
    baseline_comparison_authority_posture: Literal[
        "no_baseline_comparison_authority_granted_by_pb_single_case_run_0a"
    ]
    model_ranking_authority_posture: Literal[
        "no_model_ranking_authority_granted_by_pb_single_case_run_0a"
    ]
    batch_execution_authority_posture: Literal[
        "no_batch_execution_authority_granted_by_pb_single_case_run_0a"
    ]
    future_family_selection_posture: Literal[
        "no_future_family_selection_authority_granted_by_pb_single_case_run_0a"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_guardrail(self) -> "ProgrambenchSingleCaseRunNonAuthorityGuardrail":
        row_refs = [row.forbidden_authority_ref for row in self.forbidden_authority_rows]
        _ensure_sorted_unique(row_refs, field_name="forbidden_authority_rows")
        observed = {row.authority_kind for row in self.forbidden_authority_rows}
        if len(observed) != len(self.forbidden_authority_rows):
            raise ValueError("forbidden_authority_rows must not duplicate authority kinds")
        required = {
            "baseline_comparison",
            "batch_execution",
            "benchmark_score",
            "benchmark_truth",
            "candidate_artifact_capture",
            "command_execution",
            "future_family_selection",
            "hidden_test_inference",
            "lifecycle_projection",
            "local_outcome_audit",
            "model_ranking",
            "official_programbench_participation",
            "official_submission",
            "probe_execution",
            "retry_authority",
            "worker_dispatch",
        }
        missing = sorted(required - observed)
        if missing:
            raise ValueError(f"single-case run guardrail missing authorities: {missing}")
        _ensure_sorted_unique(
            self.forbidden_future_artifact_kinds,
            field_name="forbidden_future_artifact_kinds",
        )
        missing_future = sorted(
            PB_SINGLE_CASE_RUN_0A_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS
            - set(self.forbidden_future_artifact_kinds)
        )
        if missing_future:
            raise ValueError(
                f"single-case run guardrail missing future artifact kinds: {missing_future}"
            )
        current = sorted(
            PB_SINGLE_CASE_RUN_0A_ARTIFACT_KINDS & set(self.forbidden_future_artifact_kinds)
        )
        if current:
            raise ValueError(
                f"single-case run guardrail cannot forbid current A artifact kinds: {current}"
            )
        _ensure_no_forbidden_refs(
            [self.single_case_run_guardrail_ref, self.single_case_run_request_ref],
            field_name="single_case_run_guardrail_refs",
        )
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


def validate_pb_single_case_run_0a_bundle(
    *,
    matrix_inclusion_family_closeout: ProgrambenchLocalMatrixInclusionFamilyCloseoutAlignment,
    matrix_revision_registration: ProgrambenchLocalMatrixRevisionRegistration,
    matrix_revision_readiness_summary: ProgrambenchLocalMatrixRevisionReadinessSummary,
    run_request: ProgrambenchSingleCaseRunRequest,
    target_selection: ProgrambenchSingleCaseTargetSelection,
    execution_preflight: ProgrambenchSingleCaseExecutionPreflight,
    run_control_contract: ProgrambenchSingleCaseRunControlContract,
    non_authority_guardrail: ProgrambenchSingleCaseRunNonAuthorityGuardrail,
) -> None:
    if run_request.target_origin_route != "matrix_member":
        raise ValueError("PB-SINGLE-CASE-RUN-0-A bundle reference path expects matrix member")
    if target_selection.target_origin_route != run_request.target_origin_route:
        raise ValueError("target selection route must match run request route")
    if target_selection.selected_case_lineage_ref != run_request.requested_case_lineage_ref:
        raise ValueError("target selection must match requested case lineage")
    if target_selection.selected_case_lineage_hash != run_request.requested_case_lineage_hash:
        raise ValueError("target selection hash must match requested case lineage hash")
    if target_selection.matrix_membership_status != "included":
        raise ValueError("matrix-member target must be included")
    if (
        target_selection.source_matrix_ref
        != matrix_revision_registration.target_matrix_ref
    ):
        raise ValueError("target source matrix must match revision registration")
    if (
        target_selection.source_matrix_revision_ref
        != matrix_revision_registration.registered_matrix_revision_ref
    ):
        raise ValueError("target source matrix revision must match registration")
    if (
        target_selection.source_matrix_revision_hash
        != matrix_revision_registration.registered_matrix_revision_hash
    ):
        raise ValueError("target source matrix revision hash must match registration")
    if (
        target_selection.selected_case_lineage_ref
        not in matrix_revision_registration.included_case_lineage_refs
    ):
        raise ValueError("target case lineage must be included in matrix revision")
    if (
        target_selection.selected_case_lineage_ref
        not in matrix_revision_readiness_summary.included_case_lineage_refs
    ):
        raise ValueError("target case lineage must be present in readiness summary")
    if matrix_revision_readiness_summary.revision_readiness_posture != (
        "ready_for_later_local_matrix_review"
    ):
        raise ValueError("matrix revision readiness must be ready for later local review")
    if matrix_inclusion_family_closeout.closed_family_ref != "PB-MATRIX-INCLUSION-0":
        raise ValueError("matrix inclusion family closeout must close PB-MATRIX-INCLUSION-0")
    if "PB-MATRIX-INCLUSION-0-C" not in matrix_inclusion_family_closeout.closed_slice_refs:
        raise ValueError("matrix inclusion family closeout must include slice C")
    if execution_preflight.single_case_run_request_ref != run_request.single_case_run_request_ref:
        raise ValueError("preflight must reference run request")
    if (
        execution_preflight.single_case_target_selection_ref
        != target_selection.single_case_target_selection_ref
    ):
        raise ValueError("preflight must reference target selection")
    if (
        run_control_contract.single_case_run_request_ref
        != run_request.single_case_run_request_ref
    ):
        raise ValueError("control contract must reference run request")
    if (
        non_authority_guardrail.single_case_run_request_ref
        != run_request.single_case_run_request_ref
    ):
        raise ValueError("guardrail must reference run request")
    if (
        run_control_contract.worker_visible_packet_hash
        != target_selection.worker_visible_packet_hash
    ):
        raise ValueError("control contract worker packet hash must match target")
    if run_control_contract.local_probe_basis_hash != target_selection.local_probe_basis_hash:
        raise ValueError("control contract local probe basis hash must match target")
    for field_name in (
        "runbook_hash",
        "sandbox_policy_hash",
        "run_budget_hash",
        "tool_manifest_hash",
        "write_scope_hash",
    ):
        if getattr(run_control_contract, field_name) != getattr(
            execution_preflight, field_name
        ):
            raise ValueError(f"control contract {field_name} must match preflight")
    if execution_preflight.preflight_status != (
        "ready_for_later_local_single_case_execution_review"
    ):
        raise ValueError("reference bundle requires ready execution preflight")
    if target_selection.contamination_posture != "clean":
        raise ValueError("reference bundle target selection must be clean")
