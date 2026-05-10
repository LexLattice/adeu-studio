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
PROGRAMBENCH_SINGLE_CASE_TARGET_SELECTION_SCHEMA = "programbench_single_case_target_selection@1"
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
PROGRAMBENCH_SINGLE_CASE_EXECUTION_TRACE_SCHEMA = "programbench_single_case_execution_trace@1"
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
    "hidden-test equivalence",
    "official-like result",
    "pass rate",
    "passed programbench",
    "representative result",
    "solve rate",
    "solved the case",
    "success rate",
)
_REQUIRED_B_WITNESS_REFS = (
    "decompilation_absence_witness_ref",
    "docker_socket_absence_witness_ref",
    "network_mode_witness_ref",
    "sandbox_attestation_bundle_ref",
    "sandbox_instance_ref",
    "secret_absence_witness_ref",
    "source_lookup_absence_witness_ref",
    "write_scope_attestation_ref",
)
_REQUIRED_PREFLIGHT_CHECK_KINDS = (
    "decompilation_disabled",
    "docker_socket_absent",
    "host_secret_absent",
    "local_probe_basis_declared",
    "network_disabled",
    "run_budget_bounded",
    "source_lookup_disabled",
    "tool_manifest_closed",
    "write_scope_bounded",
)
_PB_SINGLE_CASE_RUN_0B_DISPATCH_AUTHORITY_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS270.md"
_PB_SINGLE_CASE_RUN_CLOSED_SLICES = [
    "PB-SINGLE-CASE-RUN-0-A",
    "PB-SINGLE-CASE-RUN-0-B",
    "PB-SINGLE-CASE-RUN-0-C",
]
_PASSED_FORBIDDEN_CONTENT_SCREEN_VERDICT = "passed"
_RAW_SHELL_MARKERS = ("&&", "||", ";", "|", "$(", "`", ">", "<", "&", "\n", "\r")
_RAW_SHELL_EXECUTABLES = {
    "ash",
    "bash",
    "csh",
    "cmd",
    "cmd.exe",
    "dash",
    "fish",
    "ksh",
    "powershell",
    "powershell.exe",
    "pwsh",
    "pwsh.exe",
    "sh",
    "tcsh",
    "zsh",
}


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
        ref for ref in values if any(marker in ref.lower() for marker in _FORBIDDEN_REF_MARKERS)
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


def _argv_executable_name(value: str) -> str:
    return re.split(r"[\\/]+", value)[-1].lower()


def _ensure_argv_shaped(argv: list[str], *, field_name: str) -> None:
    if not argv:
        raise ValueError(f"{field_name} must contain at least one argv token")
    _ensure_non_empty_trimmed(argv, field_name=field_name)
    executable = _argv_executable_name(argv[0])
    if executable in _RAW_SHELL_EXECUTABLES:
        raise ValueError(f"{field_name} must not invoke a shell executable")
    shell_like = [token for token in argv if any(marker in token for marker in _RAW_SHELL_MARKERS)]
    if shell_like:
        raise ValueError(f"{field_name} must not contain raw shell markers")


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
    rationale_scope_posture: Literal["local_single_case_run_selection_only_not_benchmark_result"]
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
    schema_id: Literal[PROGRAMBENCH_SINGLE_CASE_RUN_REQUEST_SCHEMA] = Field(alias="schema")
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
    run_rationale_rows: list[ProgrambenchSingleCaseRunRationaleRow] = Field(min_length=1)
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
            "ready_expanded_case_lineage": ("not_applicable_ready_expanded_case_lineage_route"),
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
    schema_id: Literal[PROGRAMBENCH_SINGLE_CASE_TARGET_SELECTION_SCHEMA] = Field(alias="schema")
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
    schema_id: Literal[PROGRAMBENCH_SINGLE_CASE_EXECUTION_PREFLIGHT_SCHEMA] = Field(alias="schema")
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
    preflight_check_rows: list[ProgrambenchSingleCasePreflightCheckRow] = Field(min_length=1)
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
        if self.sandbox_witness_requirement_refs != list(_REQUIRED_B_WITNESS_REFS):
            raise ValueError("sandbox_witness_requirement_refs must match B witness requirements")
        if self.required_b_witness_refs != list(_REQUIRED_B_WITNESS_REFS):
            raise ValueError("required_b_witness_refs must match B witness requirements")
        row_refs = [row.preflight_check_ref for row in self.preflight_check_rows]
        _ensure_sorted_unique(row_refs, field_name="preflight_check_rows")
        check_kinds = [row.check_kind for row in self.preflight_check_rows]
        if len(check_kinds) != len(set(check_kinds)):
            raise ValueError("preflight_check_rows must not duplicate check kinds")
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
        blocked_rows = [row for row in self.preflight_check_rows if row.check_status == "blocked"]
        if self.preflight_status == "ready_for_later_local_single_case_execution_review":
            missing_check_kinds = sorted(set(_REQUIRED_PREFLIGHT_CHECK_KINDS) - set(check_kinds))
            unexpected_check_kinds = sorted(set(check_kinds) - set(_REQUIRED_PREFLIGHT_CHECK_KINDS))
            if missing_check_kinds or unexpected_check_kinds:
                raise ValueError(
                    "ready preflight must cover required check kinds: "
                    f"missing={missing_check_kinds}, unexpected={unexpected_check_kinds}"
                )
            if blocked_rows:
                raise ValueError("ready preflight cannot carry blocked checks")
        elif not blocked_rows:
            raise ValueError("blocked preflight requires at least one blocked check")
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseRunControlContract(_SingleCaseRunBase):
    schema_id: Literal[PROGRAMBENCH_SINGLE_CASE_RUN_CONTROL_CONTRACT_SCHEMA] = Field(alias="schema")
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
    forbidden_content_screen_policy: Literal["required_before_candidate_artifact_capture"]
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
    schema_id: Literal[PROGRAMBENCH_SINGLE_CASE_RUN_NON_AUTHORITY_GUARDRAIL_SCHEMA] = Field(
        alias="schema"
    )
    single_case_run_guardrail_ref: str
    single_case_run_request_ref: str
    forbidden_authority_rows: list[ProgrambenchSingleCaseForbiddenAuthorityRow] = Field(
        min_length=1
    )
    forbidden_future_artifact_kinds: list[str] = Field(min_length=1)
    worker_dispatch_deferred_posture: Literal["worker_dispatch_deferred_to_pb_single_case_run_0b"]
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


class ProgrambenchSingleCaseCommandArgvRow(_SingleCaseRunBase):
    command_argv_ref: str
    argv: list[str] = Field(min_length=1)
    command_role: Literal[
        "worker_dispatch",
        "candidate_local_probe",
        "candidate_artifact_build",
        "harness_capture",
    ]
    command_shape_posture: Literal["argv_shaped_no_raw_shell_string"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_row(self) -> "ProgrambenchSingleCaseCommandArgvRow":
        _ensure_no_forbidden_refs([self.command_argv_ref], field_name="command_argv_refs")
        _ensure_argv_shaped(self.argv, field_name="argv")
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseProbeObservationRow(_SingleCaseRunBase):
    probe_observation_ref: str
    local_probe_ref: str
    probe_kind: Literal["positive", "negative"]
    probe_result_status: Literal[
        "passed",
        "failed",
        "missing",
        "inconclusive",
        "not_applicable",
    ]
    local_only_posture: Literal["declared_local_probe_only_not_hidden_test"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_row(self) -> "ProgrambenchSingleCaseProbeObservationRow":
        _ensure_no_forbidden_refs(
            [self.probe_observation_ref, self.local_probe_ref],
            field_name="probe_observation_refs",
        )
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseGeneratedArtifactRow(_SingleCaseRunBase):
    generated_artifact_ref: str
    artifact_path_ref: str
    artifact_hash: str
    inside_write_scope_posture: Literal["inside_released_write_scope"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_row(self) -> "ProgrambenchSingleCaseGeneratedArtifactRow":
        _ensure_hash(self.artifact_hash, field_name="artifact_hash")
        _ensure_no_forbidden_refs(
            [self.generated_artifact_ref, self.artifact_path_ref],
            field_name="generated_artifact_refs",
        )
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseArtifactHashRow(_SingleCaseRunBase):
    artifact_hash_ref: str
    artifact_ref: str
    artifact_hash: str
    hash_role: Literal["generated_artifact_hash", "manifest_member_hash"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_row(self) -> "ProgrambenchSingleCaseArtifactHashRow":
        _ensure_hash(self.artifact_hash, field_name="artifact_hash")
        _ensure_no_forbidden_refs(
            [self.artifact_hash_ref, self.artifact_ref],
            field_name="artifact_hash_refs",
        )
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseLocalProbeSummaryRow(_SingleCaseRunBase):
    local_probe_summary_ref: str
    local_probe_ref: str
    probe_kind: Literal["positive", "negative"]
    probe_result_status: Literal[
        "failed",
        "inconclusive",
        "missing",
        "not_applicable",
        "passed",
    ]
    local_only_posture: Literal["declared_local_probe_only_not_hidden_test"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_row(self) -> "ProgrambenchSingleCaseLocalProbeSummaryRow":
        _ensure_no_forbidden_refs(
            [self.local_probe_summary_ref, self.local_probe_ref],
            field_name="local_probe_summary_refs",
        )
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseDecisionBasisRow(_SingleCaseRunBase):
    decision_basis_ref: str
    basis_kind: Literal[
        "artifact_capture_inside_write_scope",
        "declared_local_probes_satisfied",
        "local_evidence_inconclusive",
        "output_capture_satisfied",
        "projection_validated",
        "sandbox_satisfied",
    ]
    basis_status: Literal["supports_local_acceptance", "supports_remand_pressure"]
    local_only_posture: Literal["local_single_case_only_not_benchmark_truth"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_row(self) -> "ProgrambenchSingleCaseDecisionBasisRow":
        _ensure_no_forbidden_refs([self.decision_basis_ref], field_name="decision_basis_refs")
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseRemandReasonRow(_SingleCaseRunBase):
    remand_reason_ref: str
    remand_source_kind: Literal[
        "artifact_capture_gap",
        "filesystem_expectation_gap",
        "lifecycle_projection_gap",
        "local_evidence_inconclusive",
        "local_probe_gap",
        "output_capture_gap",
        "sandbox_violation",
        "worker_declared_uncertainty",
    ]
    remand_scope_posture: Literal["pressure_only_requires_later_retry_or_trial_governance"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_row(self) -> "ProgrambenchSingleCaseRemandReasonRow":
        _ensure_no_forbidden_refs([self.remand_reason_ref], field_name="remand_reason_refs")
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseAcceptanceBasisRow(_SingleCaseRunBase):
    acceptance_basis_ref: str
    acceptance_basis_kind: Literal[
        "artifact_capture_inside_write_scope",
        "declared_local_probes_satisfied",
        "filesystem_expectations_satisfied",
        "lifecycle_projection_validated",
        "output_capture_satisfied",
        "sandbox_satisfied",
        "stdio_exit_expectations_satisfied",
    ]
    acceptance_scope_posture: Literal["local_acceptance_only_not_benchmark_truth"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_row(self) -> "ProgrambenchSingleCaseAcceptanceBasisRow":
        _ensure_no_forbidden_refs([self.acceptance_basis_ref], field_name="acceptance_basis_refs")
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseRunHandoffPressureRow(_SingleCaseRunBase):
    handoff_pressure_ref: str
    pressure_kind: Literal[
        "future_batch_execution_governance_review",
        "future_benchmark_result_governance_review",
        "future_local_case_expansion_review",
        "future_official_participation_governance_review",
        "future_retry_governance_review",
    ]
    pressure_scope_posture: Literal["pressure_only_no_authority_granted"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_row(self) -> "ProgrambenchSingleCaseRunHandoffPressureRow":
        _ensure_no_forbidden_refs([self.handoff_pressure_ref], field_name="handoff_pressure_refs")
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseWorkerDispatchSpecimen(_SingleCaseRunBase):
    schema_id: Literal[PROGRAMBENCH_SINGLE_CASE_WORKER_DISPATCH_SPECIMEN_SCHEMA] = Field(
        alias="schema"
    )
    single_case_worker_dispatch_specimen_ref: str
    single_case_run_request_ref: str
    single_case_target_selection_ref: str
    single_case_execution_preflight_ref: str
    single_case_run_control_contract_ref: str
    b_slice_dispatch_authority_ref: str
    dispatch_authority_kind: Literal["b_slice_lock_local_single_specimen_only"]
    dispatch_specimen_index: Literal[1]
    single_case_dispatch_cardinality_posture: Literal["exactly_one_dispatch_specimen"]
    worker_profile_ref: str
    input_packet_materialization_hash: str
    worker_visible_context_materialization_hash: str
    tool_manifest_materialization_hash: str
    sandbox_policy_materialization_hash: str
    run_control_contract_hash: str
    worker_visible_packet_hash: str
    runbook_hash: str
    sandbox_policy_hash: str
    tool_manifest_hash: str
    write_scope_hash: str
    local_probe_basis_hash: str
    sandbox_instance_ref: str
    sandbox_attestation_bundle_ref: str
    network_mode_witness_ref: str
    docker_socket_absence_witness_ref: str
    secret_absence_witness_ref: str
    source_lookup_absence_witness_ref: str
    decompilation_absence_witness_ref: str
    write_scope_attestation_ref: str
    dispatch_status: Literal["local_single_case_dispatch_specimen_recorded"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_dispatch_specimen(
        self,
    ) -> "ProgrambenchSingleCaseWorkerDispatchSpecimen":
        if self.b_slice_dispatch_authority_ref != _PB_SINGLE_CASE_RUN_0B_DISPATCH_AUTHORITY_REF:
            raise ValueError(
                "single-case dispatch requires released PB-SINGLE-CASE-RUN-0-B lock authority"
            )
        for field_name in (
            "input_packet_materialization_hash",
            "worker_visible_context_materialization_hash",
            "tool_manifest_materialization_hash",
            "sandbox_policy_materialization_hash",
            "run_control_contract_hash",
            "worker_visible_packet_hash",
            "runbook_hash",
            "sandbox_policy_hash",
            "tool_manifest_hash",
            "write_scope_hash",
            "local_probe_basis_hash",
        ):
            _ensure_hash(getattr(self, field_name), field_name=field_name)
        _ensure_no_forbidden_refs(
            [
                self.single_case_worker_dispatch_specimen_ref,
                self.single_case_run_request_ref,
                self.single_case_target_selection_ref,
                self.single_case_execution_preflight_ref,
                self.single_case_run_control_contract_ref,
                self.b_slice_dispatch_authority_ref,
                self.worker_profile_ref,
                self.sandbox_instance_ref,
                self.sandbox_attestation_bundle_ref,
                self.network_mode_witness_ref,
                self.docker_socket_absence_witness_ref,
                self.secret_absence_witness_ref,
                self.source_lookup_absence_witness_ref,
                self.decompilation_absence_witness_ref,
                self.write_scope_attestation_ref,
            ],
            field_name="single_case_worker_dispatch_refs",
        )
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseExecutionTrace(_SingleCaseRunBase):
    schema_id: Literal[PROGRAMBENCH_SINGLE_CASE_EXECUTION_TRACE_SCHEMA] = Field(alias="schema")
    single_case_execution_trace_ref: str
    single_case_worker_dispatch_specimen_ref: str
    command_argv_rows: list[ProgrambenchSingleCaseCommandArgvRow] = Field(min_length=1)
    execution_trace_kind: Literal[
        "worker_dispatch_trace",
        "candidate_local_probe_trace",
        "candidate_artifact_build_trace",
        "harness_capture_trace",
    ]
    command_rows_must_be_argv_shaped: Literal[True]
    raw_shell_string_posture: Literal["raw_shell_strings_forbidden_unless_later_explicit_authority"]
    command_allowlist_match_ref: str
    working_directory_ref: str
    environment_policy_hash: str
    stdout_hash: str
    stdout_excerpt_bounded: str = Field(max_length=512)
    stderr_hash: str
    stderr_excerpt_bounded: str = Field(max_length=512)
    exit_code: int
    duration_ms: int = Field(ge=0)
    timeout_status: Literal["completed_without_timeout", "timed_out_with_capture"]
    resource_limit_status: Literal["within_limits", "limit_exceeded_with_capture"]
    worker_tool_call_manifest_ref: str
    pre_fs_manifest_ref: str
    post_fs_manifest_ref: str
    fs_diff_ref: str
    sandbox_violation_refs: list[str] = Field(default_factory=list)
    forbidden_content_screen_verdict: Literal[
        "blocked_excluded_derived",
        "blocked_forbidden_source",
        "blocked_hidden_evidence",
        "blocked_postmortem_only",
        "inconclusive_requires_review",
        "passed",
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_execution_trace(self) -> "ProgrambenchSingleCaseExecutionTrace":
        for field_name in ("environment_policy_hash", "stdout_hash", "stderr_hash"):
            _ensure_hash(getattr(self, field_name), field_name=field_name)
        command_refs = [row.command_argv_ref for row in self.command_argv_rows]
        _ensure_sorted_unique(command_refs, field_name="command_argv_rows")
        row_roles = {row.command_role for row in self.command_argv_rows}
        expected_role = {
            "worker_dispatch_trace": "worker_dispatch",
            "candidate_local_probe_trace": "candidate_local_probe",
            "candidate_artifact_build_trace": "candidate_artifact_build",
            "harness_capture_trace": "harness_capture",
        }[self.execution_trace_kind]
        if row_roles != {expected_role}:
            raise ValueError("command argv row roles must match execution trace kind")
        _ensure_sorted_unique_allow_empty(
            self.sandbox_violation_refs,
            field_name="sandbox_violation_refs",
        )
        _ensure_no_forbidden_refs(
            [
                self.single_case_execution_trace_ref,
                self.single_case_worker_dispatch_specimen_ref,
                self.command_allowlist_match_ref,
                self.working_directory_ref,
                self.worker_tool_call_manifest_ref,
                self.pre_fs_manifest_ref,
                self.post_fs_manifest_ref,
                self.fs_diff_ref,
                *self.sandbox_violation_refs,
            ],
            field_name="single_case_execution_trace_refs",
        )
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseProbeObservationBundle(_SingleCaseRunBase):
    schema_id: Literal[PROGRAMBENCH_SINGLE_CASE_PROBE_OBSERVATION_BUNDLE_SCHEMA] = Field(
        alias="schema"
    )
    single_case_probe_observation_bundle_ref: str
    single_case_execution_trace_ref: str
    local_probe_basis_ref: str
    local_probe_basis_hash: str
    probe_observation_rows: list[ProgrambenchSingleCaseProbeObservationRow] = Field(min_length=1)
    positive_probe_result_refs: list[str] = Field(default_factory=list)
    negative_probe_result_refs: list[str] = Field(default_factory=list)
    missing_probe_refs: list[str] = Field(default_factory=list)
    inconclusive_probe_refs: list[str] = Field(default_factory=list)
    hidden_test_equivalence_posture: Literal["not_hidden_test_equivalence"]
    official_evaluator_posture: Literal["no_official_evaluator_access"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_probe_bundle(self) -> "ProgrambenchSingleCaseProbeObservationBundle":
        _ensure_hash(self.local_probe_basis_hash, field_name="local_probe_basis_hash")
        row_refs = [row.probe_observation_ref for row in self.probe_observation_rows]
        _ensure_sorted_unique(row_refs, field_name="probe_observation_rows")
        for field_name in (
            "positive_probe_result_refs",
            "negative_probe_result_refs",
            "missing_probe_refs",
            "inconclusive_probe_refs",
        ):
            values = getattr(self, field_name)
            _ensure_sorted_unique_allow_empty(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
        row_result_refs = {row.local_probe_ref for row in self.probe_observation_rows}
        reported_refs = set(
            self.positive_probe_result_refs
            + self.negative_probe_result_refs
            + self.missing_probe_refs
            + self.inconclusive_probe_refs
        )
        if not reported_refs <= row_result_refs:
            raise ValueError("probe result refs must be present in observation rows")
        _ensure_no_forbidden_refs(
            [
                self.single_case_probe_observation_bundle_ref,
                self.single_case_execution_trace_ref,
                self.local_probe_basis_ref,
            ],
            field_name="single_case_probe_observation_refs",
        )
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseCandidateArtifactCapture(_SingleCaseRunBase):
    schema_id: Literal[PROGRAMBENCH_SINGLE_CASE_CANDIDATE_ARTIFACT_CAPTURE_SCHEMA] = Field(
        alias="schema"
    )
    single_case_candidate_artifact_capture_ref: str
    single_case_execution_trace_ref: str
    artifact_capture_policy_ref: str
    write_scope_ref: str
    write_scope_hash: str
    materialization_input_hash: str
    materialization_output_manifest_hash: str
    generated_artifact_rows: list[ProgrambenchSingleCaseGeneratedArtifactRow] = Field(
        default_factory=list
    )
    artifact_hash_rows: list[ProgrambenchSingleCaseArtifactHashRow] = Field(
        default_factory=list
    )
    candidate_artifact_capture_status: Literal[
        "captured_inside_write_scope",
        "missing",
        "outside_write_scope",
        "screening_not_passed",
    ] = "captured_inside_write_scope"
    artifact_capture_blocker_refs: list[str] = Field(default_factory=list)
    inside_write_scope_posture: Literal[
        "inside_released_write_scope",
        "not_applicable_missing_capture",
        "not_applicable_screening_not_passed",
        "outside_released_write_scope",
    ]
    forbidden_content_screen_verdict: Literal[
        "blocked_excluded_derived",
        "blocked_forbidden_source",
        "blocked_hidden_evidence",
        "blocked_postmortem_only",
        "inconclusive_requires_review",
        "passed",
    ]
    official_submission_posture: Literal["not_official_submission"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_artifact_capture(
        self,
    ) -> "ProgrambenchSingleCaseCandidateArtifactCapture":
        for field_name in (
            "write_scope_hash",
            "materialization_input_hash",
            "materialization_output_manifest_hash",
        ):
            _ensure_hash(getattr(self, field_name), field_name=field_name)
        _ensure_sorted_unique_allow_empty(
            self.artifact_capture_blocker_refs,
            field_name="artifact_capture_blocker_refs",
        )
        generated_refs = [row.generated_artifact_ref for row in self.generated_artifact_rows]
        _ensure_sorted_unique_allow_empty(generated_refs, field_name="generated_artifact_rows")
        artifact_hash_refs = [row.artifact_hash_ref for row in self.artifact_hash_rows]
        _ensure_sorted_unique_allow_empty(artifact_hash_refs, field_name="artifact_hash_rows")
        generated_hashes_by_ref = {
            row.generated_artifact_ref: row.artifact_hash for row in self.generated_artifact_rows
        }
        hash_rows_by_artifact_ref = {
            row.artifact_ref: row.artifact_hash for row in self.artifact_hash_rows
        }
        if len(hash_rows_by_artifact_ref) != len(self.artifact_hash_rows):
            raise ValueError("artifact hash rows must not duplicate artifact refs")
        if not set(generated_refs) <= set(hash_rows_by_artifact_ref):
            raise ValueError("generated artifacts must have artifact hash rows")
        mismatched_artifacts = sorted(
            artifact_ref
            for artifact_ref, artifact_hash in generated_hashes_by_ref.items()
            if hash_rows_by_artifact_ref[artifact_ref] != artifact_hash
        )
        if mismatched_artifacts:
            raise ValueError(
                f"generated artifact hashes must match artifact hash rows: {mismatched_artifacts}"
            )
        if self.candidate_artifact_capture_status == "captured_inside_write_scope":
            if self.forbidden_content_screen_verdict != "passed":
                raise ValueError("captured artifacts require passed forbidden-content screening")
            if self.inside_write_scope_posture != "inside_released_write_scope":
                raise ValueError("captured artifacts require inside released write scope posture")
            if not self.generated_artifact_rows or not self.artifact_hash_rows:
                raise ValueError("captured artifacts require generated artifact and hash rows")
            if self.artifact_capture_blocker_refs:
                raise ValueError("captured artifacts cannot carry artifact capture blockers")
        else:
            if self.generated_artifact_rows or self.artifact_hash_rows:
                raise ValueError("non-captured artifact status cannot carry generated artifacts")
            if not self.artifact_capture_blocker_refs:
                raise ValueError("non-captured artifact status requires artifact blockers")
            if self.candidate_artifact_capture_status == "missing":
                if self.forbidden_content_screen_verdict != "passed":
                    raise ValueError("missing artifact capture expects passed content screening")
                if self.inside_write_scope_posture != "not_applicable_missing_capture":
                    raise ValueError("missing artifact capture requires missing-capture posture")
            elif self.candidate_artifact_capture_status == "outside_write_scope":
                if self.forbidden_content_screen_verdict != "passed":
                    raise ValueError("outside-scope capture expects passed content screening")
                if self.inside_write_scope_posture != "outside_released_write_scope":
                    raise ValueError("outside-scope capture requires outside write scope posture")
            elif self.candidate_artifact_capture_status == "screening_not_passed":
                if self.forbidden_content_screen_verdict == "passed":
                    raise ValueError("screening-not-passed capture requires a non-passed verdict")
                if self.inside_write_scope_posture != "not_applicable_screening_not_passed":
                    raise ValueError("screening-not-passed capture requires screening posture")
        _ensure_no_forbidden_refs(
            [
                self.single_case_candidate_artifact_capture_ref,
                self.single_case_execution_trace_ref,
                self.artifact_capture_policy_ref,
                self.write_scope_ref,
                *self.artifact_capture_blocker_refs,
            ],
            field_name="single_case_artifact_capture_refs",
        )
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseLifecycleProjection(_SingleCaseRunBase):
    schema_id: Literal[PROGRAMBENCH_SINGLE_CASE_LIFECYCLE_PROJECTION_SCHEMA] = Field(alias="schema")
    single_case_lifecycle_projection_ref: str
    single_case_worker_dispatch_specimen_ref: str
    single_case_execution_trace_ref: str
    single_case_probe_observation_bundle_ref: str
    single_case_candidate_artifact_capture_ref: str
    projected_attempt_lifecycle_refs: list[str] = Field(min_length=1)
    projected_trial_lifecycle_refs: list[str] = Field(min_length=1)
    projected_workbench_evidence_refs: list[str] = Field(min_length=1)
    projection_validator_binding_refs: list[str] = Field(min_length=1)
    projection_gap_refs: list[str] = Field(default_factory=list)
    projection_is_not_new_truth_posture: Literal["projection_is_not_new_truth"]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_lifecycle_projection(
        self,
    ) -> "ProgrambenchSingleCaseLifecycleProjection":
        for field_name in (
            "projected_attempt_lifecycle_refs",
            "projected_trial_lifecycle_refs",
            "projected_workbench_evidence_refs",
            "projection_validator_binding_refs",
        ):
            values = getattr(self, field_name)
            _ensure_sorted_unique(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
        _ensure_sorted_unique_allow_empty(
            self.projection_gap_refs,
            field_name="projection_gap_refs",
        )
        _ensure_no_forbidden_refs(
            [
                self.single_case_lifecycle_projection_ref,
                self.single_case_worker_dispatch_specimen_ref,
                self.single_case_execution_trace_ref,
                self.single_case_probe_observation_bundle_ref,
                self.single_case_candidate_artifact_capture_ref,
                *self.projection_gap_refs,
            ],
            field_name="single_case_lifecycle_projection_refs",
        )
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseLocalOutcomeAudit(_SingleCaseRunBase):
    schema_id: Literal[PROGRAMBENCH_SINGLE_CASE_LOCAL_OUTCOME_AUDIT_SCHEMA] = Field(alias="schema")
    single_case_local_outcome_audit_ref: str
    single_case_run_request_ref: str
    single_case_target_selection_ref: str
    single_case_worker_dispatch_specimen_ref: str
    single_case_execution_trace_ref: str
    single_case_probe_observation_bundle_ref: str
    single_case_candidate_artifact_capture_ref: str
    single_case_lifecycle_projection_ref: str
    contamination_audit_status: Literal["clean", "blocked_by_contamination"]
    contamination_blocker_refs: list[str] = Field(default_factory=list)
    sandbox_audit_status: Literal["clean", "blocked_by_sandbox"]
    sandbox_blocker_refs: list[str] = Field(default_factory=list)
    lifecycle_projection_status: Literal["validated", "blocked_by_projection_gap"]
    lifecycle_projection_blocker_refs: list[str] = Field(default_factory=list)
    output_capture_status: Literal["captured", "blocked_by_output_gap"]
    output_capture_blocker_refs: list[str] = Field(default_factory=list)
    candidate_artifact_capture_status: Literal[
        "captured_inside_write_scope",
        "missing",
        "outside_write_scope",
        "screening_not_passed",
    ]
    artifact_capture_blocker_refs: list[str] = Field(default_factory=list)
    candidate_artifact_inside_write_scope_posture: Literal[
        "inside_released_write_scope",
        "not_applicable_screening_not_passed",
        "outside_released_write_scope",
        "not_applicable_missing_capture",
    ]
    positive_probe_status: Literal["passed", "failed", "missing", "inconclusive"]
    negative_probe_status: Literal[
        "passed",
        "failed",
        "missing",
        "inconclusive",
        "not_applicable_with_reason",
    ]
    stdout_expectation_status: Literal["satisfied", "failed", "not_applicable_with_reason"]
    stderr_expectation_status: Literal["satisfied", "failed", "not_applicable_with_reason"]
    exit_code_expectation_status: Literal["satisfied", "failed", "not_applicable_with_reason"]
    filesystem_expectation_status: Literal[
        "satisfied",
        "failed",
        "not_applicable_with_reason",
    ]
    hidden_test_equivalence_posture: Literal["not_hidden_test_equivalence"]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    local_outcome_posture: Literal[
        "single_case_blocked_by_artifact_capture_gap",
        "single_case_blocked_by_contamination",
        "single_case_blocked_by_lifecycle_projection_gap",
        "single_case_blocked_by_output_capture_gap",
        "single_case_blocked_by_sandbox",
        "single_case_inconclusive_local_only",
        "single_case_locally_accepted",
        "single_case_remand_recommended",
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_outcome_audit(self) -> "ProgrambenchSingleCaseLocalOutcomeAudit":
        for field_name in (
            "contamination_blocker_refs",
            "sandbox_blocker_refs",
            "lifecycle_projection_blocker_refs",
            "output_capture_blocker_refs",
            "artifact_capture_blocker_refs",
        ):
            values = getattr(self, field_name)
            _ensure_sorted_unique_allow_empty(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
        _ensure_no_forbidden_refs(
            [
                self.single_case_local_outcome_audit_ref,
                self.single_case_run_request_ref,
                self.single_case_target_selection_ref,
                self.single_case_worker_dispatch_specimen_ref,
                self.single_case_execution_trace_ref,
                self.single_case_probe_observation_bundle_ref,
                self.single_case_candidate_artifact_capture_ref,
                self.single_case_lifecycle_projection_ref,
            ],
            field_name="single_case_local_outcome_audit_refs",
        )
        blockers = (
            self.contamination_blocker_refs
            + self.sandbox_blocker_refs
            + self.lifecycle_projection_blocker_refs
            + self.output_capture_blocker_refs
            + self.artifact_capture_blocker_refs
        )
        if self.local_outcome_posture == "single_case_locally_accepted":
            if blockers:
                raise ValueError("local acceptance cannot carry blockers")
            expected_statuses = {
                "contamination_audit_status": "clean",
                "sandbox_audit_status": "clean",
                "lifecycle_projection_status": "validated",
                "output_capture_status": "captured",
                "candidate_artifact_capture_status": "captured_inside_write_scope",
                "candidate_artifact_inside_write_scope_posture": ("inside_released_write_scope"),
                "positive_probe_status": "passed",
                "stdout_expectation_status": "satisfied",
                "stderr_expectation_status": "satisfied",
                "exit_code_expectation_status": "satisfied",
                "filesystem_expectation_status": "satisfied",
            }
            for field_name, expected in expected_statuses.items():
                if getattr(self, field_name) != expected:
                    raise ValueError(
                        f"local acceptance requires satisfied audit status: {field_name}"
                    )
            if self.negative_probe_status not in {
                "passed",
                "not_applicable_with_reason",
            }:
                raise ValueError(
                    "local acceptance requires negative probes to pass or be not applicable"
                )
        else:
            blocked_requirements: dict[str, tuple[str, str | set[str], str]] = {
                "single_case_blocked_by_artifact_capture_gap": (
                    "candidate_artifact_capture_status",
                    {"missing", "outside_write_scope", "screening_not_passed"},
                    "artifact_capture_blocker_refs",
                ),
                "single_case_blocked_by_contamination": (
                    "contamination_audit_status",
                    "blocked_by_contamination",
                    "contamination_blocker_refs",
                ),
                "single_case_blocked_by_lifecycle_projection_gap": (
                    "lifecycle_projection_status",
                    "blocked_by_projection_gap",
                    "lifecycle_projection_blocker_refs",
                ),
                "single_case_blocked_by_output_capture_gap": (
                    "output_capture_status",
                    "blocked_by_output_gap",
                    "output_capture_blocker_refs",
                ),
                "single_case_blocked_by_sandbox": (
                    "sandbox_audit_status",
                    "blocked_by_sandbox",
                    "sandbox_blocker_refs",
                ),
            }
            requirement = blocked_requirements.get(self.local_outcome_posture)
            if requirement is not None:
                status_field, expected_status, blocker_field = requirement
                status = getattr(self, status_field)
                expected_statuses = (
                    expected_status if isinstance(expected_status, set) else {expected_status}
                )
                if status not in expected_statuses:
                    raise ValueError(
                        "blocked local outcome posture requires matching blocked status: "
                        f"{status_field}"
                    )
                if not getattr(self, blocker_field):
                    raise ValueError(
                        "blocked local outcome posture requires matching blocker refs: "
                        f"{blocker_field}"
                    )
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseRunObservationSummary(_SingleCaseRunBase):
    schema_id: Literal[PROGRAMBENCH_SINGLE_CASE_RUN_OBSERVATION_SUMMARY_SCHEMA] = Field(
        alias="schema"
    )
    single_case_run_observation_summary_ref: str
    single_case_local_outcome_audit_ref: str
    single_case_local_scope_statement: Literal[
        "local_only_against_declared_probes_and_oracle_not_programbench_truth"
    ]
    local_probe_summary_rows: list[ProgrambenchSingleCaseLocalProbeSummaryRow] = Field(min_length=1)
    local_outcome_posture: Literal[
        "single_case_blocked_by_artifact_capture_gap",
        "single_case_blocked_by_contamination",
        "single_case_blocked_by_lifecycle_projection_gap",
        "single_case_blocked_by_output_capture_gap",
        "single_case_blocked_by_sandbox",
        "single_case_inconclusive_local_only",
        "single_case_locally_accepted",
        "single_case_remand_recommended",
    ]
    stdout_summary_posture: Literal[
        "local_stdout_expectation_failed",
        "local_stdout_expectation_not_applicable_with_reason",
        "local_stdout_expectation_satisfied",
    ]
    stderr_summary_posture: Literal[
        "local_stderr_expectation_failed",
        "local_stderr_expectation_not_applicable_with_reason",
        "local_stderr_expectation_satisfied",
    ]
    exit_code_summary_posture: Literal[
        "local_exit_code_expectation_failed",
        "local_exit_code_expectation_not_applicable_with_reason",
        "local_exit_code_expectation_satisfied",
    ]
    filesystem_summary_posture: Literal[
        "local_filesystem_expectation_failed",
        "local_filesystem_expectation_not_applicable_with_reason",
        "local_filesystem_expectation_satisfied",
    ]
    artifact_summary_posture: Literal[
        "local_artifact_capture_inside_write_scope",
        "local_artifact_capture_missing",
        "local_artifact_capture_outside_write_scope",
        "local_artifact_capture_screening_not_passed",
    ]
    single_specimen_scope_posture: Literal["single_local_specimen_only_no_comparison"]
    benchmark_score_language_posture: Literal["benchmark_score_language_absent"]
    baseline_comparison_language_posture: Literal["baseline_comparison_language_absent"]
    model_ranking_language_posture: Literal["model_ranking_language_absent"]
    soft_benchmark_language_screen_status: Literal["passed"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_observation_summary(
        self,
    ) -> "ProgrambenchSingleCaseRunObservationSummary":
        row_refs = [row.local_probe_summary_ref for row in self.local_probe_summary_rows]
        _ensure_sorted_unique(row_refs, field_name="local_probe_summary_rows")
        _ensure_no_forbidden_refs(
            [
                self.single_case_run_observation_summary_ref,
                self.single_case_local_outcome_audit_ref,
            ],
            field_name="single_case_run_observation_summary_refs",
        )
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseRemandOrAcceptanceDecision(_SingleCaseRunBase):
    schema_id: Literal[PROGRAMBENCH_SINGLE_CASE_REMAND_OR_ACCEPTANCE_DECISION_SCHEMA] = Field(
        alias="schema"
    )
    single_case_remand_or_acceptance_decision_ref: str
    single_case_local_outcome_audit_ref: str
    single_case_run_observation_summary_ref: str
    decision_posture: Literal[
        "local_acceptance_recorded",
        "local_inconclusive_pressure_recorded",
        "local_remand_pressure_recorded",
    ]
    decision_basis_rows: list[ProgrambenchSingleCaseDecisionBasisRow] = Field(min_length=1)
    remand_reason_rows: list[ProgrambenchSingleCaseRemandReasonRow] = Field(default_factory=list)
    acceptance_basis_rows: list[ProgrambenchSingleCaseAcceptanceBasisRow] = Field(
        default_factory=list
    )
    retry_authority_posture: Literal["no_retry_authority_granted_by_pb_single_case_run_0c"]
    remand_pressure_posture: Literal["pressure_only_requires_later_retry_or_trial_governance"]
    official_submission_authority_posture: Literal["no_official_submission_authority"]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    future_family_selection_posture: Literal[
        "no_future_family_selection_authority_granted_by_pb_single_case_run_0c"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_decision(self) -> "ProgrambenchSingleCaseRemandOrAcceptanceDecision":
        for field_name, attr in (
            ("decision_basis_rows", "decision_basis_ref"),
            ("remand_reason_rows", "remand_reason_ref"),
            ("acceptance_basis_rows", "acceptance_basis_ref"),
        ):
            rows = getattr(self, field_name)
            refs = [getattr(row, attr) for row in rows]
            _ensure_sorted_unique_allow_empty(refs, field_name=field_name)
        _ensure_no_forbidden_refs(
            [
                self.single_case_remand_or_acceptance_decision_ref,
                self.single_case_local_outcome_audit_ref,
                self.single_case_run_observation_summary_ref,
            ],
            field_name="single_case_remand_or_acceptance_decision_refs",
        )
        if self.decision_posture == "local_acceptance_recorded":
            if self.remand_reason_rows:
                raise ValueError("local acceptance cannot carry remand reasons")
            if not self.acceptance_basis_rows:
                raise ValueError("local acceptance requires acceptance basis rows")
            if any(
                row.basis_status != "supports_local_acceptance" for row in self.decision_basis_rows
            ):
                raise ValueError(
                    "local acceptance decision basis rows must support local acceptance"
                )
        else:
            if not self.remand_reason_rows:
                raise ValueError("non-acceptance decisions require remand reasons")
            if self.acceptance_basis_rows:
                raise ValueError("non-acceptance decisions cannot carry acceptance basis")
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseRunHandoff(_SingleCaseRunBase):
    schema_id: Literal[PROGRAMBENCH_SINGLE_CASE_RUN_HANDOFF_SCHEMA] = Field(alias="schema")
    single_case_run_handoff_ref: str
    single_case_remand_or_acceptance_decision_ref: str
    handoff_pressure_rows: list[ProgrambenchSingleCaseRunHandoffPressureRow] = Field(
        default_factory=list
    )
    handoff_pressure_kind: Literal[
        "future_batch_execution_governance_review",
        "future_benchmark_result_governance_review",
        "future_local_case_expansion_review",
        "future_official_participation_governance_review",
        "future_retry_governance_review",
        "none_local_acceptance_recorded",
    ]
    handoff_non_selection_posture: Literal[
        "pressure_only_no_future_family_selected_by_pb_single_case_run_0c"
    ]
    retry_authority_posture: Literal["no_retry_authority_granted_by_pb_single_case_run_0c"]
    batch_execution_authority_posture: Literal[
        "no_batch_execution_authority_granted_by_pb_single_case_run_0c"
    ]
    official_programbench_authority_posture: Literal[
        "no_official_programbench_authority_granted_by_pb_single_case_run_0c"
    ]
    model_ranking_authority_posture: Literal[
        "no_model_ranking_authority_granted_by_pb_single_case_run_0c"
    ]
    future_family_selection_posture: Literal[
        "no_future_family_selection_authority_granted_by_pb_single_case_run_0c"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_handoff(self) -> "ProgrambenchSingleCaseRunHandoff":
        row_refs = [row.handoff_pressure_ref for row in self.handoff_pressure_rows]
        _ensure_sorted_unique_allow_empty(row_refs, field_name="handoff_pressure_rows")
        _ensure_no_forbidden_refs(
            [
                self.single_case_run_handoff_ref,
                self.single_case_remand_or_acceptance_decision_ref,
            ],
            field_name="single_case_run_handoff_refs",
        )
        if self.handoff_pressure_kind == "none_local_acceptance_recorded":
            if self.handoff_pressure_rows:
                raise ValueError("no-pressure handoff cannot carry pressure rows")
        elif not any(
            row.pressure_kind == self.handoff_pressure_kind for row in self.handoff_pressure_rows
        ):
            raise ValueError("handoff pressure kind must be represented by a row")
        _ensure_no_result_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchSingleCaseRunFamilyCloseoutAlignment(_SingleCaseRunBase):
    schema_id: Literal[PROGRAMBENCH_SINGLE_CASE_RUN_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA] = Field(
        alias="schema"
    )
    single_case_run_family_closeout_alignment_ref: str
    family_ref: Literal["PB-SINGLE-CASE-RUN-0"]
    closed_slices: list[str] = Field(min_length=1)
    slice_a_closeout_ref: str
    slice_b_closeout_ref: str
    slice_c_closeout_ref: str
    local_outcome_audit_refs: list[str] = Field(min_length=1)
    observation_summary_refs: list[str] = Field(min_length=1)
    remand_or_acceptance_decision_refs: list[str] = Field(min_length=1)
    handoff_refs: list[str] = Field(min_length=1)
    family_scope_posture: Literal["pb_single_case_run_0_closed_local_single_case_only"]
    official_programbench_authority_posture: Literal[
        "no_official_programbench_authority_granted_by_pb_single_case_run_0c"
    ]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    retry_authority_posture: Literal["no_retry_authority_granted_by_pb_single_case_run_0c"]
    future_family_selection_posture: Literal[
        "no_future_family_selection_authority_granted_by_pb_single_case_run_0c"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_closeout(
        self,
    ) -> "ProgrambenchSingleCaseRunFamilyCloseoutAlignment":
        if self.closed_slices != _PB_SINGLE_CASE_RUN_CLOSED_SLICES:
            raise ValueError("PB-SINGLE-CASE-RUN-0 closeout must close exactly A, B, and C")
        for field_name in (
            "local_outcome_audit_refs",
            "observation_summary_refs",
            "remand_or_acceptance_decision_refs",
            "handoff_refs",
        ):
            values = getattr(self, field_name)
            _ensure_sorted_unique(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
        _ensure_no_forbidden_refs(
            [
                self.single_case_run_family_closeout_alignment_ref,
                self.slice_a_closeout_ref,
                self.slice_b_closeout_ref,
                self.slice_c_closeout_ref,
            ],
            field_name="single_case_run_family_closeout_refs",
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
    if target_selection.target_selection_status != "selected_for_later_local_run_preflight":
        raise ValueError("target selection must be selected for later local run preflight")
    if target_selection.target_selection_blocker_refs:
        raise ValueError("target selection must not carry blockers")
    if target_selection.source_matrix_ref != matrix_revision_registration.target_matrix_ref:
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
    if run_control_contract.single_case_run_request_ref != run_request.single_case_run_request_ref:
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
    if run_control_contract.runbook_hash != execution_preflight.runbook_hash:
        raise ValueError("control contract runbook_hash must match preflight")
    if run_control_contract.sandbox_policy_hash != execution_preflight.sandbox_policy_hash:
        raise ValueError("control contract sandbox_policy_hash must match preflight")
    if run_control_contract.run_budget_hash != execution_preflight.run_budget_hash:
        raise ValueError("control contract run_budget_hash must match preflight")
    if run_control_contract.tool_manifest_hash != execution_preflight.tool_manifest_hash:
        raise ValueError("control contract tool_manifest_hash must match preflight")
    if run_control_contract.write_scope_hash != execution_preflight.write_scope_hash:
        raise ValueError("control contract write_scope_hash must match preflight")
    if execution_preflight.preflight_status != (
        "ready_for_later_local_single_case_execution_review"
    ):
        raise ValueError("reference bundle requires ready execution preflight")
    if target_selection.contamination_posture != "clean":
        raise ValueError("reference bundle target selection must be clean")


def validate_pb_single_case_run_0b_bundle(
    *,
    matrix_inclusion_family_closeout: ProgrambenchLocalMatrixInclusionFamilyCloseoutAlignment,
    matrix_revision_registration: ProgrambenchLocalMatrixRevisionRegistration,
    matrix_revision_readiness_summary: ProgrambenchLocalMatrixRevisionReadinessSummary,
    run_request: ProgrambenchSingleCaseRunRequest,
    target_selection: ProgrambenchSingleCaseTargetSelection,
    execution_preflight: ProgrambenchSingleCaseExecutionPreflight,
    run_control_contract: ProgrambenchSingleCaseRunControlContract,
    non_authority_guardrail: ProgrambenchSingleCaseRunNonAuthorityGuardrail,
    worker_dispatch_specimen: ProgrambenchSingleCaseWorkerDispatchSpecimen,
    execution_trace: ProgrambenchSingleCaseExecutionTrace,
    probe_observation_bundle: ProgrambenchSingleCaseProbeObservationBundle,
    candidate_artifact_capture: ProgrambenchSingleCaseCandidateArtifactCapture,
    lifecycle_projection: ProgrambenchSingleCaseLifecycleProjection,
) -> None:
    validate_pb_single_case_run_0a_bundle(
        matrix_inclusion_family_closeout=matrix_inclusion_family_closeout,
        matrix_revision_registration=matrix_revision_registration,
        matrix_revision_readiness_summary=matrix_revision_readiness_summary,
        run_request=run_request,
        target_selection=target_selection,
        execution_preflight=execution_preflight,
        run_control_contract=run_control_contract,
        non_authority_guardrail=non_authority_guardrail,
    )

    if (
        worker_dispatch_specimen.single_case_run_request_ref
        != run_request.single_case_run_request_ref
    ):
        raise ValueError("worker dispatch specimen must reference run request")
    if (
        worker_dispatch_specimen.single_case_target_selection_ref
        != target_selection.single_case_target_selection_ref
    ):
        raise ValueError("worker dispatch specimen must reference target selection")
    if (
        worker_dispatch_specimen.single_case_execution_preflight_ref
        != execution_preflight.single_case_execution_preflight_ref
    ):
        raise ValueError("worker dispatch specimen must reference execution preflight")
    if (
        worker_dispatch_specimen.single_case_run_control_contract_ref
        != run_control_contract.single_case_run_control_contract_ref
    ):
        raise ValueError("worker dispatch specimen must reference run control contract")
    if (
        worker_dispatch_specimen.b_slice_dispatch_authority_ref
        != _PB_SINGLE_CASE_RUN_0B_DISPATCH_AUTHORITY_REF
    ):
        raise ValueError("PB-SINGLE-CASE-RUN-0-B dispatch authority is required")
    if worker_dispatch_specimen.dispatch_specimen_index != 1:
        raise ValueError("PB-SINGLE-CASE-RUN-0-B allows exactly one dispatch specimen")
    if execution_preflight.dispatch_authority_posture != (
        "no_worker_dispatch_authority_granted_by_pb_single_case_run_0a"
    ):
        raise ValueError("A preflight cannot grant dispatch authority")

    expected_hashes = {
        "worker_visible_packet_hash": target_selection.worker_visible_packet_hash,
        "runbook_hash": execution_preflight.runbook_hash,
        "sandbox_policy_hash": execution_preflight.sandbox_policy_hash,
        "tool_manifest_hash": execution_preflight.tool_manifest_hash,
        "write_scope_hash": execution_preflight.write_scope_hash,
        "local_probe_basis_hash": target_selection.local_probe_basis_hash,
    }
    for field_name, expected_value in expected_hashes.items():
        if getattr(worker_dispatch_specimen, field_name) != expected_value:
            raise ValueError(f"worker dispatch {field_name} must match released A basis")
    if (
        worker_dispatch_specimen.sandbox_policy_materialization_hash
        == worker_dispatch_specimen.sandbox_policy_hash
    ):
        raise ValueError("sandbox policy materialization hash must be separately recorded")
    if (
        worker_dispatch_specimen.tool_manifest_materialization_hash
        == worker_dispatch_specimen.tool_manifest_hash
    ):
        raise ValueError("tool manifest materialization hash must be separately recorded")

    if (
        execution_trace.single_case_worker_dispatch_specimen_ref
        != worker_dispatch_specimen.single_case_worker_dispatch_specimen_ref
    ):
        raise ValueError("execution trace must reference worker dispatch specimen")
    if execution_trace.execution_trace_kind != "worker_dispatch_trace":
        raise ValueError("reference B bundle records the worker dispatch trace")
    if execution_trace.sandbox_violation_refs:
        raise ValueError("execution trace cannot carry sandbox violations")

    if (
        probe_observation_bundle.single_case_execution_trace_ref
        != execution_trace.single_case_execution_trace_ref
    ):
        raise ValueError("probe observation bundle must reference execution trace")
    if probe_observation_bundle.local_probe_basis_ref != target_selection.local_probe_basis_ref:
        raise ValueError("probe observation bundle must use selected local probe basis")
    if probe_observation_bundle.local_probe_basis_hash != target_selection.local_probe_basis_hash:
        raise ValueError("probe observation bundle hash must match selected probe basis")
    if probe_observation_bundle.missing_probe_refs:
        raise ValueError("reference B probe bundle cannot carry missing probes")
    if probe_observation_bundle.inconclusive_probe_refs:
        raise ValueError("reference B probe bundle cannot carry inconclusive probes")

    if (
        candidate_artifact_capture.single_case_execution_trace_ref
        != execution_trace.single_case_execution_trace_ref
    ):
        raise ValueError("candidate artifact capture must reference execution trace")
    if candidate_artifact_capture.forbidden_content_screen_verdict != (
        execution_trace.forbidden_content_screen_verdict
    ):
        raise ValueError("candidate artifact capture must preserve screening verdict")
    if (
        execution_trace.forbidden_content_screen_verdict
        != _PASSED_FORBIDDEN_CONTENT_SCREEN_VERDICT
        and candidate_artifact_capture.candidate_artifact_capture_status
        != "screening_not_passed"
    ):
        raise ValueError(
            "non-passed content screening requires screening-not-passed artifact capture"
        )
    if candidate_artifact_capture.write_scope_ref != execution_preflight.write_scope_ref:
        raise ValueError("candidate artifact capture must use released write scope")
    if candidate_artifact_capture.write_scope_hash != execution_preflight.write_scope_hash:
        raise ValueError("candidate artifact capture write scope hash must match preflight")
    if candidate_artifact_capture.materialization_input_hash not in {
        execution_trace.stdout_hash,
        execution_trace.stderr_hash,
    }:
        raise ValueError("candidate artifact input hash must bind captured output")

    if (
        lifecycle_projection.single_case_worker_dispatch_specimen_ref
        != worker_dispatch_specimen.single_case_worker_dispatch_specimen_ref
    ):
        raise ValueError("lifecycle projection must reference worker dispatch specimen")
    if (
        lifecycle_projection.single_case_execution_trace_ref
        != execution_trace.single_case_execution_trace_ref
    ):
        raise ValueError("lifecycle projection must reference execution trace")
    if (
        lifecycle_projection.single_case_probe_observation_bundle_ref
        != probe_observation_bundle.single_case_probe_observation_bundle_ref
    ):
        raise ValueError("lifecycle projection must reference probe bundle")
    if (
        lifecycle_projection.single_case_candidate_artifact_capture_ref
        != candidate_artifact_capture.single_case_candidate_artifact_capture_ref
    ):
        raise ValueError("lifecycle projection must reference candidate artifact capture")
    if lifecycle_projection.projection_gap_refs:
        raise ValueError("reference B lifecycle projection cannot carry projection gaps")
    if lifecycle_projection.projection_is_not_new_truth_posture != ("projection_is_not_new_truth"):
        raise ValueError("lifecycle projection cannot create new truth")
    if lifecycle_projection.benchmark_truth_posture != "not_benchmark_truth":
        raise ValueError("lifecycle projection cannot claim benchmark truth")


def validate_pb_single_case_run_0c_bundle(
    *,
    matrix_inclusion_family_closeout: ProgrambenchLocalMatrixInclusionFamilyCloseoutAlignment,
    matrix_revision_registration: ProgrambenchLocalMatrixRevisionRegistration,
    matrix_revision_readiness_summary: ProgrambenchLocalMatrixRevisionReadinessSummary,
    run_request: ProgrambenchSingleCaseRunRequest,
    target_selection: ProgrambenchSingleCaseTargetSelection,
    execution_preflight: ProgrambenchSingleCaseExecutionPreflight,
    run_control_contract: ProgrambenchSingleCaseRunControlContract,
    non_authority_guardrail: ProgrambenchSingleCaseRunNonAuthorityGuardrail,
    worker_dispatch_specimen: ProgrambenchSingleCaseWorkerDispatchSpecimen,
    execution_trace: ProgrambenchSingleCaseExecutionTrace,
    probe_observation_bundle: ProgrambenchSingleCaseProbeObservationBundle,
    candidate_artifact_capture: ProgrambenchSingleCaseCandidateArtifactCapture,
    lifecycle_projection: ProgrambenchSingleCaseLifecycleProjection,
    local_outcome_audit: ProgrambenchSingleCaseLocalOutcomeAudit,
    observation_summary: ProgrambenchSingleCaseRunObservationSummary,
    remand_or_acceptance_decision: ProgrambenchSingleCaseRemandOrAcceptanceDecision,
    handoff: ProgrambenchSingleCaseRunHandoff,
    family_closeout: ProgrambenchSingleCaseRunFamilyCloseoutAlignment,
) -> None:
    validate_pb_single_case_run_0b_bundle(
        matrix_inclusion_family_closeout=matrix_inclusion_family_closeout,
        matrix_revision_registration=matrix_revision_registration,
        matrix_revision_readiness_summary=matrix_revision_readiness_summary,
        run_request=run_request,
        target_selection=target_selection,
        execution_preflight=execution_preflight,
        run_control_contract=run_control_contract,
        non_authority_guardrail=non_authority_guardrail,
        worker_dispatch_specimen=worker_dispatch_specimen,
        execution_trace=execution_trace,
        probe_observation_bundle=probe_observation_bundle,
        candidate_artifact_capture=candidate_artifact_capture,
        lifecycle_projection=lifecycle_projection,
    )

    if local_outcome_audit.single_case_run_request_ref != run_request.single_case_run_request_ref:
        raise ValueError("outcome audit must reference run request")
    if (
        local_outcome_audit.single_case_target_selection_ref
        != target_selection.single_case_target_selection_ref
    ):
        raise ValueError("outcome audit must reference target selection")
    if (
        local_outcome_audit.single_case_worker_dispatch_specimen_ref
        != worker_dispatch_specimen.single_case_worker_dispatch_specimen_ref
    ):
        raise ValueError("outcome audit must reference worker dispatch specimen")
    if (
        local_outcome_audit.single_case_execution_trace_ref
        != execution_trace.single_case_execution_trace_ref
    ):
        raise ValueError("outcome audit must reference execution trace")
    if (
        local_outcome_audit.single_case_probe_observation_bundle_ref
        != probe_observation_bundle.single_case_probe_observation_bundle_ref
    ):
        raise ValueError("outcome audit must reference probe observation bundle")
    if (
        local_outcome_audit.single_case_candidate_artifact_capture_ref
        != candidate_artifact_capture.single_case_candidate_artifact_capture_ref
    ):
        raise ValueError("outcome audit must reference candidate artifact capture")
    if (
        local_outcome_audit.candidate_artifact_capture_status
        != candidate_artifact_capture.candidate_artifact_capture_status
    ):
        raise ValueError("outcome audit artifact capture status must match capture row")
    if (
        local_outcome_audit.candidate_artifact_inside_write_scope_posture
        != candidate_artifact_capture.inside_write_scope_posture
    ):
        raise ValueError("outcome audit write-scope posture must match capture row")
    if (
        local_outcome_audit.single_case_lifecycle_projection_ref
        != lifecycle_projection.single_case_lifecycle_projection_ref
    ):
        raise ValueError("outcome audit must reference lifecycle projection")

    if local_outcome_audit.local_outcome_posture == "single_case_locally_accepted":
        required_audit_statuses = {
            "contamination_audit_status": "clean",
            "sandbox_audit_status": "clean",
            "lifecycle_projection_status": "validated",
            "output_capture_status": "captured",
            "candidate_artifact_capture_status": "captured_inside_write_scope",
            "candidate_artifact_inside_write_scope_posture": "inside_released_write_scope",
            "positive_probe_status": "passed",
            "stdout_expectation_status": "satisfied",
            "stderr_expectation_status": "satisfied",
            "exit_code_expectation_status": "satisfied",
            "filesystem_expectation_status": "satisfied",
        }
        for field_name, expected_value in required_audit_statuses.items():
            if getattr(local_outcome_audit, field_name) != expected_value:
                raise ValueError(f"local acceptance requires satisfied audit status: {field_name}")
        if local_outcome_audit.negative_probe_status not in {
            "passed",
            "not_applicable_with_reason",
        }:
            raise ValueError(
                "local acceptance requires negative probes to pass or be not applicable"
            )
        if execution_trace.sandbox_violation_refs:
            raise ValueError("local acceptance requires no sandbox violations")
        if execution_trace.forbidden_content_screen_verdict != "passed":
            raise ValueError("local acceptance requires passed output screening")
        if candidate_artifact_capture.forbidden_content_screen_verdict != "passed":
            raise ValueError("local acceptance requires screened artifact capture")
        if candidate_artifact_capture.inside_write_scope_posture != ("inside_released_write_scope"):
            raise ValueError("local acceptance requires artifact inside write scope")
        if candidate_artifact_capture.write_scope_ref != execution_preflight.write_scope_ref:
            raise ValueError("local acceptance requires released write scope ref")
        if candidate_artifact_capture.write_scope_hash != execution_preflight.write_scope_hash:
            raise ValueError("local acceptance requires released write scope hash")
        if lifecycle_projection.projection_gap_refs:
            raise ValueError("local acceptance requires no lifecycle projection gaps")
        if not lifecycle_projection.projection_validator_binding_refs:
            raise ValueError("local acceptance requires projection validator bindings")
        failed_probes = [
            row.local_probe_ref
            for row in probe_observation_bundle.probe_observation_rows
            if row.probe_result_status != "passed"
        ]
        if failed_probes:
            raise ValueError(
                f"local acceptance requires declared local probes to pass: {failed_probes}"
            )
        if probe_observation_bundle.missing_probe_refs:
            raise ValueError("local acceptance cannot carry missing probes")
        if probe_observation_bundle.inconclusive_probe_refs:
            raise ValueError("local acceptance cannot carry inconclusive probes")

    if (
        observation_summary.single_case_local_outcome_audit_ref
        != local_outcome_audit.single_case_local_outcome_audit_ref
    ):
        raise ValueError("observation summary must reference local outcome audit")
    if observation_summary.local_outcome_posture != local_outcome_audit.local_outcome_posture:
        raise ValueError("observation summary posture must match outcome audit")
    summary_probe_refs = {
        row.local_probe_ref for row in observation_summary.local_probe_summary_rows
    }
    observed_probe_refs = {
        row.local_probe_ref for row in probe_observation_bundle.probe_observation_rows
    }
    if not summary_probe_refs <= observed_probe_refs:
        raise ValueError("observation summary probe refs must come from probe bundle")

    if (
        remand_or_acceptance_decision.single_case_local_outcome_audit_ref
        != local_outcome_audit.single_case_local_outcome_audit_ref
    ):
        raise ValueError("decision must reference local outcome audit")
    if (
        remand_or_acceptance_decision.single_case_run_observation_summary_ref
        != observation_summary.single_case_run_observation_summary_ref
    ):
        raise ValueError("decision must reference observation summary")
    if local_outcome_audit.local_outcome_posture == "single_case_locally_accepted":
        if remand_or_acceptance_decision.decision_posture != "local_acceptance_recorded":
            raise ValueError("local acceptance requires acceptance decision posture")
        if remand_or_acceptance_decision.remand_reason_rows:
            raise ValueError("local acceptance cannot carry remand pressure")
    elif remand_or_acceptance_decision.decision_posture == "local_acceptance_recorded":
        raise ValueError("non-accepted local outcomes cannot record acceptance")

    if (
        handoff.single_case_remand_or_acceptance_decision_ref
        != remand_or_acceptance_decision.single_case_remand_or_acceptance_decision_ref
    ):
        raise ValueError("handoff must reference remand or acceptance decision")
    if local_outcome_audit.local_outcome_posture == "single_case_locally_accepted":
        if handoff.handoff_pressure_kind != "none_local_acceptance_recorded":
            raise ValueError("local acceptance handoff must not carry pressure")

    if family_closeout.local_outcome_audit_refs != [
        local_outcome_audit.single_case_local_outcome_audit_ref
    ]:
        raise ValueError("family closeout must reference local outcome audit")
    if family_closeout.observation_summary_refs != [
        observation_summary.single_case_run_observation_summary_ref
    ]:
        raise ValueError("family closeout must reference observation summary")
    if family_closeout.remand_or_acceptance_decision_refs != [
        remand_or_acceptance_decision.single_case_remand_or_acceptance_decision_ref
    ]:
        raise ValueError("family closeout must reference remand/acceptance decision")
    if family_closeout.handoff_refs != [handoff.single_case_run_handoff_ref]:
        raise ValueError("family closeout must reference handoff")
