from __future__ import annotations

from pathlib import Path
from typing import Literal

from pydantic import Field, model_validator

from .arc_series_cartography import (
    SourceStatus,
    _CartographyBase,
    _non_empty,
    _repo_ref,
    _sorted_unique,
    _sorted_unique_by_ref,
)
from .candidate_review_classification import _surface_id
from .recursive_candidate_intake import (
    CandidateAuthorityLayer,
    CandidateSourceKind,
    CandidateSourcePresencePosture,
    OdeuLane,
)

REPO_DISPATCH_REVIEW_REQUEST_SCHEMA = "repo_dispatch_review_request@1"
REPO_DISPATCH_SOURCE_INDEX_SCHEMA = "repo_dispatch_source_index@1"
REPO_DISPATCH_NON_EXECUTION_GUARDRAIL_SCHEMA = "repo_dispatch_non_execution_guardrail@1"
REPO_WORKER_ROLE_CAPACITY_PROFILE_SCHEMA = "repo_worker_role_capacity_profile@1"
REPO_MULTI_WORKER_ASSIGNMENT_PLAN_SCHEMA = "repo_multi_worker_assignment_plan@1"
REPO_WORKER_IO_CONTRACT_SCHEMA = "repo_worker_io_contract@1"
REPO_WORKER_TOOL_APPLICABILITY_MATRIX_SCHEMA = "repo_worker_tool_applicability_matrix@1"
REPO_DISPATCH_EXCEPTION_REGISTER_SCHEMA = "repo_dispatch_exception_register@1"
REPO_WORKER_OUTPUT_RECONCILIATION_PLAN_SCHEMA = "repo_worker_output_reconciliation_plan@1"
REPO_DISPATCH_RECONCILIATION_CONTRACT_SCHEMA = "repo_dispatch_reconciliation_contract@1"
REPO_POST_DISPATCH_REVIEW_HANDOFF_SCHEMA = "repo_post_dispatch_review_handoff@1"
REPO_DISPATCH_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA = (
    "repo_dispatch_review_family_closeout_alignment@1"
)

DispatchSourceRole = Literal[
    "v74_post_projection_handoff_source",
    "visibility_contract_source",
    "workbench_projection_source",
    "family_closeout_source",
    "dogfood_source",
    "review_source",
    "roadmap_context_source",
    "v43_branch_posture_source",
    "absence_marker",
]
DispatchReviewPosture = Literal[
    "eligible_for_dispatch_review",
    "blocked_by_required_later_authority",
    "blocked_by_unresolved_exception",
    "blocked_by_missing_source",
    "future_family_only",
    "rejected_out_of_scope",
]
RequestedOrchestrationHorizon = Literal[
    "multi_worker_orchestration_review",
    "worker_output_reconciliation_review",
    "tool_applicability_review",
    "product_review_later",
    "runtime_permission_review_later",
    "external_branch_review_later",
    "future_family_review_only",
]
CarriedExceptionOrigin = Literal[
    "v74_exception_visibility",
    "v74_visibility_contract",
    "v74_post_projection_handoff",
    "absence_marker",
]
RequiredLaterAuthorityKind = Literal[
    "runtime_permission",
    "product_authorization",
    "release_authority",
    "external_branch_activation",
    "dispatch_execution_authority",
    "human_or_maintainer_review",
    "recursive_policy_authority",
]
RequiredBeforeSurface = Literal[
    "before_dispatch_review",
    "before_worker_assignment_review",
    "before_runtime_permission_review",
    "before_product_review",
    "before_release_review",
    "before_external_branch_review",
    "before_human_or_maintainer_review",
    "before_recursive_policy_review",
    "not_selected_here",
]
AuthorityGapPosture = Literal[
    "authority_gap_present",
    "authority_checked_absent",
    "authority_not_applicable",
    "unknown_needs_review",
]
ForbiddenDispatchActionKind = Literal[
    "assign_worker_now",
    "run_command_now",
    "open_pr_now",
    "commit_now",
    "merge_now",
    "release_now",
    "authorize_product_now",
    "grant_runtime_permission_now",
    "enter_external_contest_now",
    "self_approve_now",
]
AllowedDispatchNextReviewSurface = Literal[
    "v75b_worker_orchestration_review",
    "v75c_reconciliation_review",
    "future_runtime_permission_review",
    "future_product_review",
    "future_external_branch_review",
    "future_family_review",
    "deferred_no_selection",
]
WorkerRoleKind = Literal[
    "source_index_worker",
    "evidence_review_worker",
    "adversarial_review_worker",
    "schema_validation_worker",
    "tool_run_worker",
    "reconciliation_worker",
    "operator_projection_worker",
    "external_branch_review_worker",
]
WorkerToolUsePosture = Literal[
    "applicability_record_only",
    "tool_use_requires_later_runtime_permission",
    "tool_use_not_authorized_by_v75",
]
AssignmentPlanPosture = Literal[
    "plan_ready_for_review",
    "blocked_by_missing_role_profile",
    "blocked_by_missing_io_contract",
    "blocked_by_tool_applicability_gap",
    "blocked_by_unresolved_exception",
    "blocked_by_later_authority",
    "future_family_only",
    "rejected_out_of_scope",
]
AssignmentExecutionPosture = Literal[
    "no_execution_authorized",
    "review_plan_only",
    "blocked_pending_later_authority",
]
WorkerOutputAuthorityPosture = Literal[
    "output_for_review_only",
    "output_requires_reconciliation",
    "output_requires_adversarial_review",
    "output_requires_human_ratification",
    "output_not_truth",
]
WorkerToolApplicabilityPosture = Literal[
    "applicable_for_target_horizon",
    "blocked_by_missing_source",
    "blocked_by_missing_tool_evidence",
    "not_applicable_for_target_horizon",
    "requires_negative_control",
    "requires_human_review",
    "unknown_needs_review",
]
DispatchExceptionKind = Literal[
    "missing_dispatch_source",
    "unresolved_projection_exception",
    "missing_role_profile",
    "missing_io_contract",
    "tool_applicability_gap",
    "required_later_authority_missing",
    "product_authority_gap",
    "runtime_authority_gap",
    "external_branch_boundary_gap",
    "worker_output_truth_gap",
    "unknown_needs_review",
]
DispatchExceptionBlockingPosture = Literal[
    "blocking",
    "warning_only",
    "carried_forward",
    "not_applicable",
    "unknown_needs_review",
]
DispatchExceptionNextSurface = Literal[
    "v75c_reconciliation_review",
    "future_runtime_permission_review",
    "future_product_review",
    "future_external_branch_review",
    "future_family_review",
    "deferred_no_selection",
]
TargetNamespaceKind = Literal[
    "dispatch_request",
    "worker_role",
    "io_contract",
    "tool_matrix",
    "candidate",
    "claim_horizon",
]
OutputPresencePosture = Literal[
    "projected_not_observed",
    "observed_from_authorized_prior_run",
    "observed_from_support_artifact",
    "missing_expected_output",
    "not_applicable",
]
V75CDispatchExecutionPosture = Literal["no_dispatch_executed_by_v75"]
WorkerOutputRelationKind = Literal[
    "conflict",
    "complementarity",
    "duplicate",
    "orthogonal",
    "unclear_relation",
    "single_output_no_relation",
]
ReconciliationRequiredNextReviewSurface = Literal[
    "future_runtime_permission_review",
    "future_product_review",
    "future_external_branch_review",
    "future_outcome_review",
    "future_reconciliation_or_arbiter_review",
    "future_experiment_review",
    "future_family_review",
    "deferred_no_selection",
]
DispatchForbiddenInference = Literal[
    "worker_output_as_truth",
    "model_output_as_benchmark_truth",
    "tool_pass_as_scope_expansion",
    "assignment_plan_as_execution",
    "dispatch_review_as_runtime_permission",
]
DispatchSettlementPosture = Literal[
    "preserve_for_later_review",
    "requires_adversarial_review",
    "requires_human_ratification",
    "requires_runtime_permission_review",
    "requires_product_review",
    "requires_external_branch_review",
    "deferred_no_selection",
]
PostDispatchReviewHandoffTarget = Literal[
    "future_runtime_permission_review",
    "future_product_review",
    "future_external_branch_review",
    "future_outcome_review",
    "future_reconciliation_or_arbiter_review",
    "future_experiment_review",
    "future_family_review",
    "deferred_no_selection",
]
PostDispatchReviewHandoffSubjectHorizon = Literal[
    "dispatch_review_process_outcome",
    "projected_orchestration_plan_review",
    "authorized_prior_worker_run_output",
    "future_runtime_execution_outcome",
    "product_review_pressure",
    "external_branch_review_pressure",
    "experiment_design_pressure",
]
PostDispatchReviewHandoffPosture = Literal[
    "ready_for_later_review",
    "blocked_by_unresolved_exception",
    "blocked_by_required_later_authority",
    "blocked_by_output_truth_boundary",
    "deferred_to_future_family",
    "rejected_out_of_scope",
]

_ELIGIBILITY_SOURCE_ROLES = {
    "v74_post_projection_handoff_source",
    "visibility_contract_source",
    "workbench_projection_source",
}
_SUPPORT_ONLY_SOURCE_ROLES = {
    "family_closeout_source",
    "dogfood_source",
    "review_source",
    "roadmap_context_source",
}
_FORBIDDEN_ACTION_KINDS = {
    "assign_worker_now",
    "run_command_now",
    "open_pr_now",
    "commit_now",
    "merge_now",
    "release_now",
    "authorize_product_now",
    "grant_runtime_permission_now",
    "enter_external_contest_now",
    "self_approve_now",
}
_NEXT_REVIEW_SURFACES_BY_HORIZON: dict[
    RequestedOrchestrationHorizon,
    tuple[AllowedDispatchNextReviewSurface, ...],
] = {
    "multi_worker_orchestration_review": (
        "v75b_worker_orchestration_review",
        "v75c_reconciliation_review",
    ),
    "worker_output_reconciliation_review": ("v75c_reconciliation_review",),
    "tool_applicability_review": (
        "v75b_worker_orchestration_review",
        "v75c_reconciliation_review",
    ),
    "product_review_later": (
        "future_product_review",
        "future_family_review",
    ),
    "runtime_permission_review_later": (
        "future_runtime_permission_review",
        "future_family_review",
    ),
    "external_branch_review_later": (
        "future_external_branch_review",
        "future_family_review",
    ),
    "future_family_review_only": (
        "future_family_review",
        "deferred_no_selection",
    ),
}
_WORKER_PLANNING_SCHEMA_NAMES = {
    REPO_WORKER_ROLE_CAPACITY_PROFILE_SCHEMA,
    REPO_MULTI_WORKER_ASSIGNMENT_PLAN_SCHEMA,
    REPO_WORKER_IO_CONTRACT_SCHEMA,
    REPO_WORKER_TOOL_APPLICABILITY_MATRIX_SCHEMA,
    REPO_DISPATCH_EXCEPTION_REGISTER_SCHEMA,
}
_V75C_SCHEMA_NAMES = {
    REPO_WORKER_OUTPUT_RECONCILIATION_PLAN_SCHEMA,
    REPO_DISPATCH_RECONCILIATION_CONTRACT_SCHEMA,
    REPO_POST_DISPATCH_REVIEW_HANDOFF_SCHEMA,
    REPO_DISPATCH_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
}
_REQUIRED_DISPATCH_FORBIDDEN_INFERENCES = {
    "worker_output_as_truth",
    "model_output_as_benchmark_truth",
    "tool_pass_as_scope_expansion",
    "assignment_plan_as_execution",
    "dispatch_review_as_runtime_permission",
}


def _reject_unnegated_authority_claim(value: str, *, field_name: str) -> str:
    lowered = value.lower()
    forbidden = [
        "assign worker",
        "worker assigned",
        "run command",
        "command to run",
        "open pr",
        "commit now",
        "merge now",
        "release now",
        "product authorized",
        "authorizes product",
        "runtime permission granted",
        "grants runtime",
        "external contest entered",
        "enter external contest",
        "dispatch executed",
        "dispatch now",
        "self approve",
        "self-approved",
        "workbench action authorizes",
    ]
    negation_markers = ("no ", "not ", "without ", "forbidden ", "non-")
    for phrase in forbidden:
        index = lowered.find(phrase)
        if index == -1:
            continue
        prefix = lowered[max(0, index - 18) : index]
        if not any(marker in prefix for marker in negation_markers):
            raise ValueError(f"{field_name} may not carry dispatch or downstream authority")
    return value


def _require_terms(value: str, *, field_name: str, terms: tuple[str, ...]) -> str:
    lowered = value.lower()
    missing = [term for term in terms if term not in lowered]
    if missing:
        raise ValueError(f"{field_name} must mention {', '.join(missing)}")
    return value


def _source_path(path: str) -> str:
    _repo_ref(path, field_name="source_ref")
    return path


def _authority_kind_from_v74(value: str) -> RequiredLaterAuthorityKind:
    if value == "dispatch_authority_required":
        return "dispatch_execution_authority"
    if value == "human_ratification_required":
        return "human_or_maintainer_review"
    if value == "product_authority_required":
        return "product_authorization"
    if value == "runtime_authority_required":
        return "runtime_permission"
    if value == "maintainer_release_authority_required":
        return "release_authority"
    if value == "external_contest_authority_required":
        return "external_branch_activation"
    raise ValueError(f"unknown V74 authority kind: {value}")


def _required_before_from_v74(value: str) -> RequiredBeforeSurface:
    if value == "before_dispatch_review":
        return "before_dispatch_review"
    if value == "before_product_review":
        return "before_product_review"
    if value == "before_runtime_review":
        return "before_runtime_permission_review"
    if value == "before_release_review":
        return "before_release_review"
    if value == "before_external_contest_review":
        return "before_external_branch_review"
    if value == "before_ratification_review":
        return "before_human_or_maintainer_review"
    if value == "not_selected_here":
        return "not_selected_here"
    raise ValueError(f"unknown V74 required-before action: {value}")


class RepoDispatchSourceRow(_CartographyBase):
    source_ref: str
    source_kind: CandidateSourceKind
    authority_layer: CandidateAuthorityLayer
    source_status: SourceStatus
    source_presence_posture: CandidateSourcePresencePosture
    dispatch_source_role: DispatchSourceRole
    source_horizon: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_dispatch_source_row(self) -> RepoDispatchSourceRow:
        _repo_ref(self.source_ref, field_name="source_ref")
        _non_empty(self.source_horizon, field_name="source_horizon")
        _reject_unnegated_authority_claim(self.limitation_note, field_name="limitation_note")
        if (
            self.dispatch_source_role != "absence_marker"
            and self.source_presence_posture != "present"
        ):
            raise ValueError("non-absence dispatch source rows must be present")
        if (
            self.dispatch_source_role == "absence_marker"
            and self.source_presence_posture == "present"
        ):
            raise ValueError("absence-marker dispatch source rows must not be present sources")
        if (
            self.dispatch_source_role in _SUPPORT_ONLY_SOURCE_ROLES
            and self.authority_layer == "lock"
        ):
            raise ValueError("support/context dispatch source roles may not be lock authority")
        return self


class RepoDispatchSourceIndex(_CartographyBase):
    schema: Literal["repo_dispatch_source_index@1"] = REPO_DISPATCH_SOURCE_INDEX_SCHEMA
    dispatch_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    source_rows: list[RepoDispatchSourceRow] = Field(min_length=1)
    dispatch_source_summary: str

    @model_validator(mode="after")
    def _validate_dispatch_source_index(self) -> RepoDispatchSourceIndex:
        object.__setattr__(
            self,
            "source_rows",
            _sorted_unique_by_ref(self.source_rows, attr="source_ref", field_name="source_rows"),
        )
        _non_empty(self.review_id, field_name="review_id")
        _non_empty(self.snapshot_id, field_name="snapshot_id")
        _non_empty(self.source_set_id, field_name="source_set_id")
        _require_terms(
            self.dispatch_source_summary,
            field_name="dispatch_source_summary",
            terms=("eligibility", "context", "no prose memory", "no dispatch"),
        )
        expected_id = _surface_id(
            "repo_dispatch_source_index",
            self.schema,
            self.model_dump(mode="json"),
            "dispatch_source_index_id",
        )
        if self.dispatch_source_index_id != expected_id:
            raise ValueError("dispatch_source_index_id does not match canonical payload hash")
        return self


class RepoDispatchRequiredLaterAuthorityRow(_CartographyBase):
    authority_requirement_ref: str
    candidate_ref: str
    authority_kind: RequiredLaterAuthorityKind
    required_before_surface: RequiredBeforeSurface
    source_refs: list[str] = Field(min_length=1)
    source_presence_posture: CandidateSourcePresencePosture
    authority_gap_posture: AuthorityGapPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_required_authority_row(self) -> RepoDispatchRequiredLaterAuthorityRow:
        _non_empty(self.authority_requirement_ref, field_name="authority_requirement_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        object.__setattr__(
            self,
            "source_refs",
            _sorted_unique(self.source_refs, field_name="source_refs"),
        )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        _reject_unnegated_authority_claim(self.limitation_note, field_name="limitation_note")
        if (
            self.source_presence_posture != "present"
            and self.authority_gap_posture != "unknown_needs_review"
        ):
            raise ValueError("missing authority sources must keep unknown-needs-review posture")
        return self


class RepoDispatchReviewRequestRow(_CartographyBase):
    dispatch_request_ref: str
    candidate_ref: str
    case_view_refs: list[str] = Field(default_factory=list)
    visibility_contract_refs: list[str] = Field(default_factory=list)
    workbench_projection_refs: list[str] = Field(default_factory=list)
    post_projection_handoff_refs: list[str] = Field(default_factory=list)
    source_refs: list[str] = Field(min_length=1)
    required_later_authority_refs: list[str] = Field(default_factory=list)
    required_later_authority_rows: list[RepoDispatchRequiredLaterAuthorityRow] = Field(
        default_factory=list
    )
    carried_upstream_exception_refs: list[str] = Field(default_factory=list)
    carried_exception_origin: CarriedExceptionOrigin
    dispatch_review_posture: DispatchReviewPosture
    requested_orchestration_horizon: RequestedOrchestrationHorizon
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_dispatch_request_row(self) -> RepoDispatchReviewRequestRow:
        _non_empty(self.dispatch_request_ref, field_name="dispatch_request_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "case_view_refs",
            "visibility_contract_refs",
            "workbench_projection_refs",
            "post_projection_handoff_refs",
            "source_refs",
            "required_later_authority_refs",
            "carried_upstream_exception_refs",
            "guardrail_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "odeu_lanes",
            _sorted_unique(self.odeu_lanes, field_name="odeu_lanes"),
        )
        object.__setattr__(
            self,
            "required_later_authority_rows",
            _sorted_unique_by_ref(
                self.required_later_authority_rows,
                attr="authority_requirement_ref",
                field_name="required_later_authority_rows",
            ),
        )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        if not self.required_later_authority_rows and self.required_later_authority_refs:
            raise ValueError("required later authority refs must resolve to row-shaped records")
        row_refs = {row.authority_requirement_ref for row in self.required_later_authority_rows}
        if set(self.required_later_authority_refs) != row_refs:
            raise ValueError("required later authority refs must match authority rows")
        for row in self.required_later_authority_rows:
            if row.candidate_ref != self.candidate_ref:
                raise ValueError("required later authority rows must match request candidate")
        if (
            self.carried_upstream_exception_refs
            and self.carried_exception_origin == "absence_marker"
        ):
            raise ValueError("carried upstream exceptions require a V74 exception origin")
        for exception_ref in self.carried_upstream_exception_refs:
            if exception_ref.startswith("dispatch-exception:") or ":v75b:" in exception_ref:
                raise ValueError("V75-A may only carry upstream V74 exception refs")
        _reject_unnegated_authority_claim(self.limitation_note, field_name="limitation_note")
        if self.dispatch_review_posture == "eligible_for_dispatch_review":
            if not self.post_projection_handoff_refs:
                raise ValueError("eligible dispatch-review requests require V74-C handoff refs")
            if not self.visibility_contract_refs:
                raise ValueError("eligible dispatch-review requests require visibility contracts")
            if not self.workbench_projection_refs:
                raise ValueError("eligible dispatch-review requests require workbench projections")
            authority_kinds = {row.authority_kind for row in self.required_later_authority_rows}
            if "dispatch_execution_authority" not in authority_kinds:
                raise ValueError("eligible dispatch-review requests require dispatch authority gap")
            if self.requested_orchestration_horizon in {
                "product_review_later",
                "runtime_permission_review_later",
            }:
                raise ValueError("product/runtime/external pressure is not eligible in V75-A")
        if self.requested_orchestration_horizon == "product_review_later" and not any(
            row.authority_kind == "product_authorization"
            for row in self.required_later_authority_rows
        ):
            raise ValueError("product review pressure requires product authority blocker")
        if self.requested_orchestration_horizon == "runtime_permission_review_later" and not any(
            row.authority_kind == "runtime_permission" for row in self.required_later_authority_rows
        ):
            raise ValueError("runtime pressure requires runtime authority blocker")
        if self.requested_orchestration_horizon == "external_branch_review_later":
            if self.dispatch_review_posture not in {
                "blocked_by_required_later_authority",
                "future_family_only",
            }:
                raise ValueError(
                    "external branch review requires blocked or future-family posture in V75-A"
                )
            if not any(
                row.authority_kind == "external_branch_activation"
                for row in self.required_later_authority_rows
            ):
                raise ValueError(
                    "external branch review requires external branch authority blocker"
                )
        return self


class RepoDispatchReviewRequest(_CartographyBase):
    schema: Literal["repo_dispatch_review_request@1"] = REPO_DISPATCH_REVIEW_REQUEST_SCHEMA
    dispatch_review_request_id: str
    dispatch_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    request_rows: list[RepoDispatchReviewRequestRow] = Field(min_length=1)
    dispatch_review_boundary_summary: str

    @model_validator(mode="after")
    def _validate_dispatch_review_request(self) -> RepoDispatchReviewRequest:
        object.__setattr__(
            self,
            "request_rows",
            _sorted_unique_by_ref(
                self.request_rows,
                attr="dispatch_request_ref",
                field_name="request_rows",
            ),
        )
        _require_terms(
            self.dispatch_review_boundary_summary,
            field_name="dispatch_review_boundary_summary",
            terms=("review", "no worker", "no command", "no runtime", "no release"),
        )
        expected_id = _surface_id(
            "repo_dispatch_review_request",
            self.schema,
            self.model_dump(mode="json"),
            "dispatch_review_request_id",
        )
        if self.dispatch_review_request_id != expected_id:
            raise ValueError("dispatch_review_request_id does not match canonical payload hash")
        return self


class RepoDispatchNonExecutionGuardrailRow(_CartographyBase):
    guardrail_ref: str
    candidate_ref: str
    dispatch_request_refs: list[str] = Field(min_length=1)
    forbidden_action_kinds: list[ForbiddenDispatchActionKind] = Field(min_length=1)
    allowed_next_review_surfaces: list[AllowedDispatchNextReviewSurface] = Field(min_length=1)
    non_execution_guardrail: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_guardrail_row(self) -> RepoDispatchNonExecutionGuardrailRow:
        _non_empty(self.guardrail_ref, field_name="guardrail_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        object.__setattr__(
            self,
            "dispatch_request_refs",
            _sorted_unique(self.dispatch_request_refs, field_name="dispatch_request_refs"),
        )
        object.__setattr__(
            self,
            "forbidden_action_kinds",
            _sorted_unique(self.forbidden_action_kinds, field_name="forbidden_action_kinds"),
        )
        object.__setattr__(
            self,
            "allowed_next_review_surfaces",
            _sorted_unique(
                self.allowed_next_review_surfaces,
                field_name="allowed_next_review_surfaces",
            ),
        )
        missing = _FORBIDDEN_ACTION_KINDS.difference(self.forbidden_action_kinds)
        if missing:
            raise ValueError("dispatch non-execution guardrail omits forbidden action kinds")
        _reject_unnegated_authority_claim(self.non_execution_guardrail, field_name="guardrail")
        _reject_unnegated_authority_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.non_execution_guardrail,
            field_name="non_execution_guardrail",
            terms=("no worker", "no command", "no runtime", "no product", "no release"),
        )
        return self


class RepoDispatchNonExecutionGuardrail(_CartographyBase):
    schema: Literal["repo_dispatch_non_execution_guardrail@1"] = (
        REPO_DISPATCH_NON_EXECUTION_GUARDRAIL_SCHEMA
    )
    dispatch_non_execution_guardrail_id: str
    dispatch_review_request_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    guardrail_rows: list[RepoDispatchNonExecutionGuardrailRow] = Field(min_length=1)
    non_execution_summary: str

    @model_validator(mode="after")
    def _validate_dispatch_guardrail(self) -> RepoDispatchNonExecutionGuardrail:
        object.__setattr__(
            self,
            "guardrail_rows",
            _sorted_unique_by_ref(
                self.guardrail_rows,
                attr="guardrail_ref",
                field_name="guardrail_rows",
            ),
        )
        _require_terms(
            self.non_execution_summary,
            field_name="non_execution_summary",
            terms=("no worker", "no command", "no runtime", "no product", "no release"),
        )
        expected_id = _surface_id(
            "repo_dispatch_non_execution_guardrail",
            self.schema,
            self.model_dump(mode="json"),
            "dispatch_non_execution_guardrail_id",
        )
        if self.dispatch_non_execution_guardrail_id != expected_id:
            raise ValueError(
                "dispatch_non_execution_guardrail_id does not match canonical payload hash"
            )
        return self


def derive_v75a_repo_dispatch_source_index(
    *, repo_root: Path | None = None
) -> RepoDispatchSourceIndex:
    _ = repo_root
    payload = {
        "schema": REPO_DISPATCH_SOURCE_INDEX_SCHEMA,
        "dispatch_source_index_id": "",
        "review_id": "review:v75a:dispatch-review-request",
        "snapshot_id": "vNext+208-closed-on-main",
        "source_set_id": "source-set:v75a:released-v74c-dispatch-pressure",
        "source_rows": [
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus208/"
                    "repo_post_projection_handoff_v208_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "dispatch_source_role": "v74_post_projection_handoff_source",
                "source_horizon": "Released V74-C post-projection handoff rows.",
                "limitation_note": (
                    "Eligibility source for dispatch-review requests only; no dispatch."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus208/"
                    "repo_decision_visibility_contract_v208_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "dispatch_source_role": "visibility_contract_source",
                "source_horizon": "Released V74-C visibility contract rows.",
                "limitation_note": "Eligibility source for visibility posture only; no dispatch.",
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus208/"
                    "repo_ratification_review_workbench_projection_v208_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "dispatch_source_role": "workbench_projection_source",
                "source_horizon": "Released V74-C review-only workbench projection rows.",
                "limitation_note": "Eligibility source for review visibility only; no dispatch.",
            },
            {
                "source_ref": _source_path(
                    "docs/DRAFT_ADEU_OPERATOR_PROJECTION_V74_FAMILY_CLOSEOUT_v0.md"
                ),
                "source_kind": "planning_doc",
                "authority_layer": "planning",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "dispatch_source_role": "family_closeout_source",
                "source_horizon": "V74 family closeout context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no dispatch."
                ),
            },
            {
                "source_ref": _source_path(
                    "docs/support/arc_series_mapping/"
                    "V68_V69_V70_V71_V72_V73_V74_COMBINED_DOGFOOD_TEST_v0.json"
                ),
                "source_kind": "support_doc",
                "authority_layer": "support",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "dispatch_source_role": "dogfood_source",
                "source_horizon": "Combined V68-V74 dogfood context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no dispatch."
                ),
            },
        ],
        "dispatch_source_summary": (
            "Dispatch source rows separate eligibility from context with no prose memory and "
            "no dispatch."
        ),
    }
    payload["source_rows"] = sorted(payload["source_rows"], key=lambda row: row["source_ref"])
    payload["dispatch_source_index_id"] = _surface_id(
        "repo_dispatch_source_index",
        REPO_DISPATCH_SOURCE_INDEX_SCHEMA,
        payload,
        "dispatch_source_index_id",
    )
    return RepoDispatchSourceIndex.model_validate(payload)


def _authority_rows_for_candidate(
    candidate_ref: str,
) -> list[RepoDispatchRequiredLaterAuthorityRow]:
    if candidate_ref == "candidate:internal:self_evidencing_workflow_type_emergence":
        rows = [
            {
                "authority_requirement_ref": "authority:v75a:self-evidencing:dispatch-execution",
                "candidate_ref": candidate_ref,
                "authority_kind": "dispatch_execution_authority",
                "required_before_surface": "before_worker_assignment_review",
                "source_refs": ["docs/LOCKED_CONTINUATION_vNEXT_PLUS209.md"],
                "source_presence_posture": "present",
                "authority_gap_posture": "authority_gap_present",
                "limitation_note": (
                    "Dispatch execution authority remains missing before any worker review."
                ),
            },
            {
                "authority_requirement_ref": "authority:v75a:self-evidencing:human-review",
                "candidate_ref": candidate_ref,
                "authority_kind": "human_or_maintainer_review",
                "required_before_surface": "before_dispatch_review",
                "source_refs": ["docs/LOCKED_CONTINUATION_vNEXT_PLUS209.md"],
                "source_presence_posture": "present",
                "authority_gap_posture": "authority_gap_present",
                "limitation_note": (
                    "Human or maintainer review remains required before later review."
                ),
            },
        ]
    elif candidate_ref == "candidate:internal:typed_adjudication_product_wedge":
        rows = [
            {
                "authority_requirement_ref": "authority:v75a:product-wedge:product-review",
                "candidate_ref": candidate_ref,
                "authority_kind": "product_authorization",
                "required_before_surface": "before_product_review",
                "source_refs": ["docs/LOCKED_CONTINUATION_vNEXT_PLUS209.md"],
                "source_presence_posture": "present",
                "authority_gap_posture": "authority_gap_present",
                "limitation_note": (
                    "Product authorization remains missing before any future product review."
                ),
            }
        ]
    else:
        rows = []
    return [RepoDispatchRequiredLaterAuthorityRow.model_validate(row) for row in rows]


def derive_v75a_repo_dispatch_review_request(
    *,
    repo_root: Path | None = None,
    dispatch_source_index: RepoDispatchSourceIndex | None = None,
) -> RepoDispatchReviewRequest:
    _ = repo_root
    source_index = dispatch_source_index or derive_v75a_repo_dispatch_source_index()
    eligibility_sources = [
        row.source_ref
        for row in source_index.source_rows
        if row.dispatch_source_role in _ELIGIBILITY_SOURCE_ROLES
    ]
    context_sources = [
        row.source_ref
        for row in source_index.source_rows
        if row.dispatch_source_role in _SUPPORT_ONLY_SOURCE_ROLES
    ]
    self_candidate = "candidate:internal:self_evidencing_workflow_type_emergence"
    product_candidate = "candidate:internal:typed_adjudication_product_wedge"
    self_authority_rows = _authority_rows_for_candidate(self_candidate)
    product_authority_rows = _authority_rows_for_candidate(product_candidate)
    payload = {
        "schema": REPO_DISPATCH_REVIEW_REQUEST_SCHEMA,
        "dispatch_review_request_id": "",
        "dispatch_source_index_id": source_index.dispatch_source_index_id,
        "review_id": source_index.review_id,
        "snapshot_id": source_index.snapshot_id,
        "source_set_id": source_index.source_set_id,
        "request_rows": [
            {
                "dispatch_request_ref": "dispatch-request:v75a:self-evidencing:review",
                "candidate_ref": self_candidate,
                "case_view_refs": ["case-view:v74a:self-evidencing:operator-projection"],
                "visibility_contract_refs": [
                    "visibility-contract:v74c:self-evidencing:operator-review"
                ],
                "workbench_projection_refs": ["workbench:v74c:self-evidencing:operator-review"],
                "post_projection_handoff_refs": ["handoff:v74c:self-evidencing:v75-review-request"],
                "source_refs": sorted([*eligibility_sources, *context_sources]),
                "required_later_authority_refs": [
                    row.authority_requirement_ref for row in self_authority_rows
                ],
                "required_later_authority_rows": [
                    row.model_dump(mode="json") for row in self_authority_rows
                ],
                "carried_upstream_exception_refs": [
                    "exception:v74b:comparison-axis:operator-legibility-unchecked"
                ],
                "carried_exception_origin": "v74_post_projection_handoff",
                "dispatch_review_posture": "eligible_for_dispatch_review",
                "requested_orchestration_horizon": "multi_worker_orchestration_review",
                "odeu_lanes": ["deontic", "epistemic", "utility"],
                "guardrail_refs": ["guardrail:v75a:self-evidencing:non-execution"],
                "limitation_note": (
                    "Eligible for dispatch-review request only with no worker assignment, "
                    "no command, no runtime permission, no product authority, and no release."
                ),
            },
            {
                "dispatch_request_ref": "dispatch-request:v75a:product-wedge:blocked",
                "candidate_ref": product_candidate,
                "case_view_refs": ["case-view:v74a:product-wedge:future-family"],
                "visibility_contract_refs": [
                    "visibility-contract:v74c:product-wedge:authority-gap"
                ],
                "workbench_projection_refs": ["workbench:v74c:product-wedge:authority-gap"],
                "post_projection_handoff_refs": [
                    "handoff:v74c:product-wedge:future-product-review"
                ],
                "source_refs": sorted([*eligibility_sources, *context_sources]),
                "required_later_authority_refs": [
                    row.authority_requirement_ref for row in product_authority_rows
                ],
                "required_later_authority_rows": [
                    row.model_dump(mode="json") for row in product_authority_rows
                ],
                "carried_upstream_exception_refs": [
                    "blocker:v74a:product-wedge:product-authority-gap"
                ],
                "carried_exception_origin": "v74_post_projection_handoff",
                "dispatch_review_posture": "blocked_by_required_later_authority",
                "requested_orchestration_horizon": "product_review_later",
                "odeu_lanes": ["deontic", "utility"],
                "guardrail_refs": ["guardrail:v75a:product-wedge:non-execution"],
                "limitation_note": (
                    "Product pressure is preserved as blocked review pressure with no product "
                    "authority, no runtime permission, no worker assignment, and no dispatch."
                ),
            },
        ],
        "dispatch_review_boundary_summary": (
            "Dispatch review request is review only: no worker assignment, no command, "
            "no runtime permission, no product authorization, and no release."
        ),
    }
    payload["request_rows"] = sorted(
        payload["request_rows"],
        key=lambda row: row["dispatch_request_ref"],
    )
    payload["dispatch_review_request_id"] = _surface_id(
        "repo_dispatch_review_request",
        REPO_DISPATCH_REVIEW_REQUEST_SCHEMA,
        payload,
        "dispatch_review_request_id",
    )
    return RepoDispatchReviewRequest.model_validate(payload)


def derive_v75a_repo_dispatch_non_execution_guardrail(
    *,
    repo_root: Path | None = None,
    dispatch_review_request: RepoDispatchReviewRequest | None = None,
) -> RepoDispatchNonExecutionGuardrail:
    _ = repo_root
    request = dispatch_review_request or derive_v75a_repo_dispatch_review_request()
    rows = []
    for request_row in request.request_rows:
        rows.append(
            {
                "guardrail_ref": request_row.guardrail_refs[0],
                "candidate_ref": request_row.candidate_ref,
                "dispatch_request_refs": [request_row.dispatch_request_ref],
                "forbidden_action_kinds": sorted(_FORBIDDEN_ACTION_KINDS),
                "allowed_next_review_surfaces": sorted(
                    _NEXT_REVIEW_SURFACES_BY_HORIZON[request_row.requested_orchestration_horizon]
                ),
                "non_execution_guardrail": (
                    "This V75-A row is review only: no worker assignment, no command, "
                    "no runtime permission, no product authorization, no release, and no dispatch."
                ),
                "limitation_note": (
                    "V75-A has no worker assignment, no command run, no PR opening, no commit, "
                    "no merge, no release, no productization, no external contest entry, "
                    "and no self approval."
                ),
            }
        )
    payload = {
        "schema": REPO_DISPATCH_NON_EXECUTION_GUARDRAIL_SCHEMA,
        "dispatch_non_execution_guardrail_id": "",
        "dispatch_review_request_id": request.dispatch_review_request_id,
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
        "guardrail_rows": rows,
        "non_execution_summary": (
            "Dispatch non-execution guardrails preserve review only: no worker assignment, "
            "no command, no runtime permission, no product authorization, no release, "
            "and no dispatch."
        ),
    }
    payload["guardrail_rows"] = sorted(
        payload["guardrail_rows"],
        key=lambda row: row["guardrail_ref"],
    )
    payload["dispatch_non_execution_guardrail_id"] = _surface_id(
        "repo_dispatch_non_execution_guardrail",
        REPO_DISPATCH_NON_EXECUTION_GUARDRAIL_SCHEMA,
        payload,
        "dispatch_non_execution_guardrail_id",
    )
    return RepoDispatchNonExecutionGuardrail.model_validate(payload)


def validate_v75a_dispatch_review_bundle(
    *,
    dispatch_source_index: RepoDispatchSourceIndex,
    dispatch_review_request: RepoDispatchReviewRequest,
    dispatch_non_execution_guardrail: RepoDispatchNonExecutionGuardrail,
) -> None:
    if (
        dispatch_review_request.dispatch_source_index_id
        != dispatch_source_index.dispatch_source_index_id
    ):
        raise ValueError("dispatch request must reference the source index")
    if (
        dispatch_review_request.review_id,
        dispatch_review_request.snapshot_id,
        dispatch_review_request.source_set_id,
    ) != (
        dispatch_source_index.review_id,
        dispatch_source_index.snapshot_id,
        dispatch_source_index.source_set_id,
    ):
        raise ValueError("dispatch request provenance must match the source index")
    if (
        dispatch_non_execution_guardrail.dispatch_review_request_id
        != dispatch_review_request.dispatch_review_request_id
    ):
        raise ValueError("dispatch guardrail must reference the request surface")
    if (
        dispatch_non_execution_guardrail.review_id,
        dispatch_non_execution_guardrail.snapshot_id,
        dispatch_non_execution_guardrail.source_set_id,
    ) != (
        dispatch_review_request.review_id,
        dispatch_review_request.snapshot_id,
        dispatch_review_request.source_set_id,
    ):
        raise ValueError("dispatch guardrail provenance must match the request surface")

    source_roles = {
        row.source_ref: row.dispatch_source_role for row in dispatch_source_index.source_rows
    }
    known_sources = set(source_roles)
    request_rows = {row.dispatch_request_ref: row for row in dispatch_review_request.request_rows}
    guardrail_rows = {
        row.guardrail_ref: row for row in dispatch_non_execution_guardrail.guardrail_rows
    }

    for request_row in dispatch_review_request.request_rows:
        if any(source_ref not in known_sources for source_ref in request_row.source_refs):
            raise ValueError("dispatch request source refs must be known")
        roles = {source_roles[source_ref] for source_ref in request_row.source_refs}
        if request_row.dispatch_review_posture == "eligible_for_dispatch_review":
            if not _ELIGIBILITY_SOURCE_ROLES.issubset(roles):
                raise ValueError(
                    "eligible dispatch-review requests require released V74-C eligibility sources"
                )
            if roles.issubset(_SUPPORT_ONLY_SOURCE_ROLES):
                raise ValueError("support/context sources are not sufficient for eligibility")
        if request_row.requested_orchestration_horizon == "external_branch_review_later" and (
            "v43_branch_posture_source" not in roles
        ):
            raise ValueError("external branch pressure requires V43 branch posture source")
        if (
            request_row.requested_orchestration_horizon
            in {
                "product_review_later",
                "runtime_permission_review_later",
            }
            and request_row.dispatch_review_posture == "eligible_for_dispatch_review"
        ):
            raise ValueError("product/runtime pressure may not be eligible in V75-A")
        for authority_row in request_row.required_later_authority_rows:
            if any(
                source_ref not in known_sources
                and source_ref != "docs/LOCKED_CONTINUATION_vNEXT_PLUS209.md"
                for source_ref in authority_row.source_refs
            ):
                raise ValueError("required later authority source refs must be known or lock-bound")
        if any(guardrail_ref not in guardrail_rows for guardrail_ref in request_row.guardrail_refs):
            raise ValueError("dispatch request guardrail refs must be known")
        for guardrail_ref in request_row.guardrail_refs:
            guardrail_row = guardrail_rows[guardrail_ref]
            if guardrail_row.candidate_ref != request_row.candidate_ref:
                raise ValueError("dispatch request guardrails must match candidate")
            expected_surfaces = set(
                _NEXT_REVIEW_SURFACES_BY_HORIZON[request_row.requested_orchestration_horizon]
            )
            if set(guardrail_row.allowed_next_review_surfaces) != expected_surfaces:
                raise ValueError(
                    "dispatch guardrail next surfaces must match orchestration horizon"
                )

    for guardrail_row in dispatch_non_execution_guardrail.guardrail_rows:
        if any(ref not in request_rows for ref in guardrail_row.dispatch_request_refs):
            raise ValueError("guardrail dispatch request refs must be known")
        for ref in guardrail_row.dispatch_request_refs:
            if request_rows[ref].candidate_ref != guardrail_row.candidate_ref:
                raise ValueError("guardrail request refs must match candidate")


def derive_v75a_dispatch_review_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoDispatchSourceIndex,
    RepoDispatchReviewRequest,
    RepoDispatchNonExecutionGuardrail,
]:
    source_index = derive_v75a_repo_dispatch_source_index(repo_root=repo_root)
    request = derive_v75a_repo_dispatch_review_request(
        repo_root=repo_root,
        dispatch_source_index=source_index,
    )
    guardrail = derive_v75a_repo_dispatch_non_execution_guardrail(
        repo_root=repo_root,
        dispatch_review_request=request,
    )
    validate_v75a_dispatch_review_bundle(
        dispatch_source_index=source_index,
        dispatch_review_request=request,
        dispatch_non_execution_guardrail=guardrail,
    )
    return source_index, request, guardrail


class RepoWorkerRoleCapacityRow(_CartographyBase):
    worker_role_ref: str
    role_kind: WorkerRoleKind
    capability_horizon: str
    allowed_input_kinds: list[str] = Field(min_length=1)
    expected_output_kinds: list[str] = Field(min_length=1)
    allowed_tool_ids: list[str] = Field(default_factory=list)
    tool_use_posture: WorkerToolUsePosture
    forbidden_action_kinds: list[ForbiddenDispatchActionKind] = Field(min_length=1)
    authority_boundary_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_worker_role_capacity_row(self) -> RepoWorkerRoleCapacityRow:
        _non_empty(self.worker_role_ref, field_name="worker_role_ref")
        _non_empty(self.capability_horizon, field_name="capability_horizon")
        for field_name in (
            "allowed_input_kinds",
            "expected_output_kinds",
            "allowed_tool_ids",
            "forbidden_action_kinds",
            "authority_boundary_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        missing = _FORBIDDEN_ACTION_KINDS.difference(self.forbidden_action_kinds)
        if missing:
            raise ValueError(f"worker role profile omits forbidden action kinds: {sorted(missing)}")
        _reject_unnegated_authority_claim(self.capability_horizon, field_name="capability_horizon")
        _reject_unnegated_authority_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("not permission", "no command"),
        )
        return self


class RepoWorkerRoleCapacityProfile(_CartographyBase):
    schema: Literal["repo_worker_role_capacity_profile@1"] = (
        REPO_WORKER_ROLE_CAPACITY_PROFILE_SCHEMA
    )
    worker_role_capacity_profile_id: str
    dispatch_review_request_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    worker_role_rows: list[RepoWorkerRoleCapacityRow] = Field(min_length=1)
    role_capacity_summary: str

    @model_validator(mode="after")
    def _validate_worker_role_capacity_profile(self) -> RepoWorkerRoleCapacityProfile:
        object.__setattr__(
            self,
            "worker_role_rows",
            _sorted_unique_by_ref(
                self.worker_role_rows,
                attr="worker_role_ref",
                field_name="worker_role_rows",
            ),
        )
        _require_terms(
            self.role_capacity_summary,
            field_name="role_capacity_summary",
            terms=("capacity", "not permission", "no command", "no dispatch"),
        )
        expected_id = _surface_id(
            "repo_worker_role_capacity_profile",
            self.schema,
            self.model_dump(mode="json"),
            "worker_role_capacity_profile_id",
        )
        if self.worker_role_capacity_profile_id != expected_id:
            raise ValueError(
                "worker_role_capacity_profile_id does not match canonical payload hash"
            )
        return self


class RepoWorkerIOContractRow(_CartographyBase):
    io_contract_ref: str
    worker_role_refs: list[str] = Field(min_length=1)
    input_source_refs: list[str] = Field(min_length=1)
    input_claim_horizon: str
    expected_output_kind: str
    output_schema_ref: str
    output_authority_posture: WorkerOutputAuthorityPosture
    non_truth_guardrail: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_worker_io_contract_row(self) -> RepoWorkerIOContractRow:
        _non_empty(self.io_contract_ref, field_name="io_contract_ref")
        _non_empty(self.input_claim_horizon, field_name="input_claim_horizon")
        _non_empty(self.expected_output_kind, field_name="expected_output_kind")
        _non_empty(self.output_schema_ref, field_name="output_schema_ref")
        for field_name in ("worker_role_refs", "input_source_refs"):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.input_source_refs:
            _repo_ref(source_ref, field_name="input_source_refs")
        _reject_unnegated_authority_claim(
            self.non_truth_guardrail, field_name="non_truth_guardrail"
        )
        _reject_unnegated_authority_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.non_truth_guardrail,
            field_name="non_truth_guardrail",
            terms=("not truth", "review"),
        )
        return self


class RepoWorkerIOContract(_CartographyBase):
    schema: Literal["repo_worker_io_contract@1"] = REPO_WORKER_IO_CONTRACT_SCHEMA
    worker_io_contract_id: str
    dispatch_review_request_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    io_contract_rows: list[RepoWorkerIOContractRow] = Field(min_length=1)
    io_contract_summary: str

    @model_validator(mode="after")
    def _validate_worker_io_contract(self) -> RepoWorkerIOContract:
        object.__setattr__(
            self,
            "io_contract_rows",
            _sorted_unique_by_ref(
                self.io_contract_rows,
                attr="io_contract_ref",
                field_name="io_contract_rows",
            ),
        )
        _require_terms(
            self.io_contract_summary,
            field_name="io_contract_summary",
            terms=("review", "not truth", "no dispatch"),
        )
        expected_id = _surface_id(
            "repo_worker_io_contract",
            self.schema,
            self.model_dump(mode="json"),
            "worker_io_contract_id",
        )
        if self.worker_io_contract_id != expected_id:
            raise ValueError("worker_io_contract_id does not match canonical payload hash")
        return self


class RepoWorkerToolApplicabilityRow(_CartographyBase):
    tool_matrix_ref: str
    worker_role_refs: list[str] = Field(min_length=1)
    tool_id: str
    target_claim_refs: list[str] = Field(min_length=1)
    target_namespace_kind: TargetNamespaceKind
    claim_horizon: str
    applicability_posture: WorkerToolApplicabilityPosture
    observed_or_required_result_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_worker_tool_applicability_row(self) -> RepoWorkerToolApplicabilityRow:
        _non_empty(self.tool_matrix_ref, field_name="tool_matrix_ref")
        _non_empty(self.tool_id, field_name="tool_id")
        _non_empty(self.claim_horizon, field_name="claim_horizon")
        for field_name in (
            "worker_role_refs",
            "target_claim_refs",
            "observed_or_required_result_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        _reject_unnegated_authority_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("target-bound", "horizon-bound", "no command"),
        )
        return self


class RepoWorkerToolApplicabilityMatrix(_CartographyBase):
    schema: Literal["repo_worker_tool_applicability_matrix@1"] = (
        REPO_WORKER_TOOL_APPLICABILITY_MATRIX_SCHEMA
    )
    worker_tool_applicability_matrix_id: str
    dispatch_review_request_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    tool_matrix_rows: list[RepoWorkerToolApplicabilityRow] = Field(min_length=1)
    tool_applicability_summary: str

    @model_validator(mode="after")
    def _validate_worker_tool_applicability_matrix(self) -> RepoWorkerToolApplicabilityMatrix:
        object.__setattr__(
            self,
            "tool_matrix_rows",
            _sorted_unique_by_ref(
                self.tool_matrix_rows,
                attr="tool_matrix_ref",
                field_name="tool_matrix_rows",
            ),
        )
        _require_terms(
            self.tool_applicability_summary,
            field_name="tool_applicability_summary",
            terms=("target-bound", "horizon-bound", "no command", "no dispatch"),
        )
        expected_id = _surface_id(
            "repo_worker_tool_applicability_matrix",
            self.schema,
            self.model_dump(mode="json"),
            "worker_tool_applicability_matrix_id",
        )
        if self.worker_tool_applicability_matrix_id != expected_id:
            raise ValueError(
                "worker_tool_applicability_matrix_id does not match canonical payload hash"
            )
        return self


class RepoDispatchExceptionRow(_CartographyBase):
    dispatch_exception_ref: str
    dispatch_request_refs: list[str] = Field(default_factory=list)
    assignment_plan_refs: list[str] = Field(default_factory=list)
    worker_role_refs: list[str] = Field(default_factory=list)
    io_contract_refs: list[str] = Field(default_factory=list)
    tool_matrix_refs: list[str] = Field(default_factory=list)
    exception_kind: DispatchExceptionKind
    source_refs: list[str] = Field(min_length=1)
    blocking_posture: DispatchExceptionBlockingPosture
    required_next_surface: DispatchExceptionNextSurface
    limitation_note: str

    @model_validator(mode="after")
    def _validate_dispatch_exception_row(self) -> RepoDispatchExceptionRow:
        _non_empty(self.dispatch_exception_ref, field_name="dispatch_exception_ref")
        for field_name in (
            "dispatch_request_refs",
            "assignment_plan_refs",
            "worker_role_refs",
            "io_contract_refs",
            "tool_matrix_refs",
            "source_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        _reject_unnegated_authority_claim(self.limitation_note, field_name="limitation_note")
        lowered_note = self.limitation_note.lower()
        if any(
            term in lowered_note
            for term in ("marked resolved", "resolved by v75-b", "resolved by v75b")
        ):
            raise ValueError("V75-B exception rows may not mark exceptions resolved")
        return self


class RepoDispatchExceptionRegister(_CartographyBase):
    schema: Literal["repo_dispatch_exception_register@1"] = REPO_DISPATCH_EXCEPTION_REGISTER_SCHEMA
    dispatch_exception_register_id: str
    dispatch_review_request_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    exception_rows: list[RepoDispatchExceptionRow] = Field(min_length=1)
    exception_register_summary: str

    @model_validator(mode="after")
    def _validate_dispatch_exception_register(self) -> RepoDispatchExceptionRegister:
        object.__setattr__(
            self,
            "exception_rows",
            _sorted_unique_by_ref(
                self.exception_rows,
                attr="dispatch_exception_ref",
                field_name="exception_rows",
            ),
        )
        _require_terms(
            self.exception_register_summary,
            field_name="exception_register_summary",
            terms=("visible", "not resolved", "no dispatch"),
        )
        expected_id = _surface_id(
            "repo_dispatch_exception_register",
            self.schema,
            self.model_dump(mode="json"),
            "dispatch_exception_register_id",
        )
        if self.dispatch_exception_register_id != expected_id:
            raise ValueError("dispatch_exception_register_id does not match canonical payload hash")
        return self


class RepoMultiWorkerAssignmentPlanRow(_CartographyBase):
    assignment_plan_ref: str
    dispatch_request_refs: list[str] = Field(min_length=1)
    worker_role_refs: list[str] = Field(min_length=1)
    io_contract_refs: list[str] = Field(min_length=1)
    tool_applicability_refs: list[str] = Field(min_length=1)
    exception_refs: list[str] = Field(min_length=1)
    required_later_authority_refs: list[str] = Field(min_length=1)
    assignment_plan_posture: AssignmentPlanPosture
    assignment_execution_posture: AssignmentExecutionPosture
    non_execution_guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_assignment_plan_row(self) -> RepoMultiWorkerAssignmentPlanRow:
        _non_empty(self.assignment_plan_ref, field_name="assignment_plan_ref")
        for field_name in (
            "dispatch_request_refs",
            "worker_role_refs",
            "io_contract_refs",
            "tool_applicability_refs",
            "exception_refs",
            "required_later_authority_refs",
            "non_execution_guardrail_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        _reject_unnegated_authority_claim(self.limitation_note, field_name="limitation_note")
        if self.assignment_execution_posture != "no_execution_authorized":
            raise ValueError("assignment plans must have no execution authorized")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("plan", "no worker", "no command", "no dispatch"),
        )
        return self


class RepoMultiWorkerAssignmentPlan(_CartographyBase):
    schema: Literal["repo_multi_worker_assignment_plan@1"] = (
        REPO_MULTI_WORKER_ASSIGNMENT_PLAN_SCHEMA
    )
    multi_worker_assignment_plan_id: str
    dispatch_review_request_id: str
    worker_role_capacity_profile_id: str
    worker_io_contract_id: str
    worker_tool_applicability_matrix_id: str
    dispatch_exception_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    assignment_plan_rows: list[RepoMultiWorkerAssignmentPlanRow] = Field(min_length=1)
    assignment_plan_summary: str

    @model_validator(mode="after")
    def _validate_multi_worker_assignment_plan(self) -> RepoMultiWorkerAssignmentPlan:
        object.__setattr__(
            self,
            "assignment_plan_rows",
            _sorted_unique_by_ref(
                self.assignment_plan_rows,
                attr="assignment_plan_ref",
                field_name="assignment_plan_rows",
            ),
        )
        _require_terms(
            self.assignment_plan_summary,
            field_name="assignment_plan_summary",
            terms=("plan", "no worker", "no command", "no dispatch"),
        )
        expected_id = _surface_id(
            "repo_multi_worker_assignment_plan",
            self.schema,
            self.model_dump(mode="json"),
            "multi_worker_assignment_plan_id",
        )
        if self.multi_worker_assignment_plan_id != expected_id:
            raise ValueError(
                "multi_worker_assignment_plan_id does not match canonical payload hash"
            )
        return self


def _v75b_base_payload(
    *,
    schema: str,
    dispatch_review_request: RepoDispatchReviewRequest,
) -> dict[str, str]:
    return {
        "schema": schema,
        "dispatch_review_request_id": dispatch_review_request.dispatch_review_request_id,
        "review_id": "review:v75b:worker-orchestration-planning",
        "snapshot_id": "vNext+209-closed-on-main",
        "source_set_id": "source-set:v75b:released-v75a-dispatch-review",
    }


def derive_v75b_repo_worker_role_capacity_profile(
    *,
    repo_root: Path | None = None,
    dispatch_review_request: RepoDispatchReviewRequest | None = None,
) -> RepoWorkerRoleCapacityProfile:
    _ = repo_root
    request = dispatch_review_request or derive_v75a_repo_dispatch_review_request()
    payload = {
        **_v75b_base_payload(
            schema=REPO_WORKER_ROLE_CAPACITY_PROFILE_SCHEMA,
            dispatch_review_request=request,
        ),
        "worker_role_capacity_profile_id": "",
        "worker_role_rows": [
            {
                "worker_role_ref": "worker-role:v75b:self-evidencing:evidence-review",
                "role_kind": "evidence_review_worker",
                "capability_horizon": (
                    "Review-only evidence and source posture analysis for the selected "
                    "dispatch-review request."
                ),
                "allowed_input_kinds": sorted(
                    [
                        "repo_dispatch_review_request@1",
                        "repo_dispatch_source_index@1",
                        "repo_dispatch_non_execution_guardrail@1",
                    ]
                ),
                "expected_output_kinds": ["worker_review_note_for_reconciliation"],
                "allowed_tool_ids": ["pytest", "schema_validator"],
                "tool_use_posture": "applicability_record_only",
                "forbidden_action_kinds": sorted(_FORBIDDEN_ACTION_KINDS),
                "authority_boundary_refs": sorted(
                    [
                        "guardrail:v75a:self-evidencing:non-execution",
                        "authority:v75a:self-evidencing:dispatch-execution",
                    ]
                ),
                "limitation_note": (
                    "Worker role is a capacity profile, not permission; no command, "
                    "no worker assignment, and no dispatch."
                ),
            },
            {
                "worker_role_ref": "worker-role:v75b:product-wedge:external-branch-review",
                "role_kind": "external_branch_review_worker",
                "capability_horizon": (
                    "Future-family-only external branch review posture for blocked product "
                    "pressure."
                ),
                "allowed_input_kinds": sorted(
                    [
                        "repo_dispatch_review_request@1",
                        "repo_dispatch_non_execution_guardrail@1",
                    ]
                ),
                "expected_output_kinds": ["blocked_external_branch_review_note"],
                "allowed_tool_ids": [],
                "tool_use_posture": "tool_use_not_authorized_by_v75",
                "forbidden_action_kinds": sorted(_FORBIDDEN_ACTION_KINDS),
                "authority_boundary_refs": sorted(
                    [
                        "guardrail:v75a:product-wedge:non-execution",
                        "authority:v75a:product-wedge:product-review",
                    ]
                ),
                "limitation_note": (
                    "External branch role is future-family posture, not permission; "
                    "no command, no contest entry, and no dispatch."
                ),
            },
        ],
        "role_capacity_summary": (
            "Worker role capacity profiles describe capacity, not permission: "
            "no command and no dispatch."
        ),
    }
    payload["worker_role_rows"] = sorted(
        payload["worker_role_rows"],
        key=lambda row: row["worker_role_ref"],
    )
    payload["worker_role_capacity_profile_id"] = _surface_id(
        "repo_worker_role_capacity_profile",
        REPO_WORKER_ROLE_CAPACITY_PROFILE_SCHEMA,
        payload,
        "worker_role_capacity_profile_id",
    )
    return RepoWorkerRoleCapacityProfile.model_validate(payload)


def derive_v75b_repo_worker_io_contract(
    *,
    repo_root: Path | None = None,
    dispatch_review_request: RepoDispatchReviewRequest | None = None,
) -> RepoWorkerIOContract:
    _ = repo_root
    request = dispatch_review_request or derive_v75a_repo_dispatch_review_request()
    payload = {
        **_v75b_base_payload(
            schema=REPO_WORKER_IO_CONTRACT_SCHEMA,
            dispatch_review_request=request,
        ),
        "worker_io_contract_id": "",
        "io_contract_rows": [
            {
                "io_contract_ref": "io-contract:v75b:product-wedge:external-branch-review",
                "worker_role_refs": ["worker-role:v75b:product-wedge:external-branch-review"],
                "input_source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus209/"
                    "repo_dispatch_non_execution_guardrail_v209_reference.json",
                    "apps/api/fixtures/repo_description/vnext_plus209/"
                    "repo_dispatch_review_request_v209_reference.json",
                ],
                "input_claim_horizon": (
                    "Blocked future-family external branch review of V75-A product pressure."
                ),
                "expected_output_kind": "blocked_external_branch_review_note",
                "output_schema_ref": "future:repo_worker_output_reconciliation_plan@1",
                "output_authority_posture": "output_for_review_only",
                "non_truth_guardrail": "Expected worker output is for review and not truth.",
                "limitation_note": (
                    "IO contract describes blocked future-family output only; no command, "
                    "no dispatch, and output is not truth."
                ),
            },
            {
                "io_contract_ref": "io-contract:v75b:self-evidencing:evidence-review",
                "worker_role_refs": ["worker-role:v75b:self-evidencing:evidence-review"],
                "input_source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus209/"
                    "repo_dispatch_review_request_v209_reference.json",
                    "apps/api/fixtures/repo_description/vnext_plus209/"
                    "repo_dispatch_source_index_v209_reference.json",
                ],
                "input_claim_horizon": (
                    "Bounded review of V75-A self-evidencing dispatch-review request."
                ),
                "expected_output_kind": "worker_review_note_for_reconciliation",
                "output_schema_ref": "future:repo_worker_output_reconciliation_plan@1",
                "output_authority_posture": "output_for_review_only",
                "non_truth_guardrail": "Expected worker output is for review and not truth.",
                "limitation_note": (
                    "IO contract describes expected output only; no command, no dispatch, "
                    "and output is not truth."
                ),
            },
        ],
        "io_contract_summary": (
            "Worker IO contracts are review-only and not truth; no dispatch is authorized."
        ),
    }
    payload["io_contract_rows"] = sorted(
        payload["io_contract_rows"],
        key=lambda row: row["io_contract_ref"],
    )
    payload["worker_io_contract_id"] = _surface_id(
        "repo_worker_io_contract",
        REPO_WORKER_IO_CONTRACT_SCHEMA,
        payload,
        "worker_io_contract_id",
    )
    return RepoWorkerIOContract.model_validate(payload)


def derive_v75b_repo_worker_tool_applicability_matrix(
    *,
    repo_root: Path | None = None,
    dispatch_review_request: RepoDispatchReviewRequest | None = None,
) -> RepoWorkerToolApplicabilityMatrix:
    _ = repo_root
    request = dispatch_review_request or derive_v75a_repo_dispatch_review_request()
    payload = {
        **_v75b_base_payload(
            schema=REPO_WORKER_TOOL_APPLICABILITY_MATRIX_SCHEMA,
            dispatch_review_request=request,
        ),
        "worker_tool_applicability_matrix_id": "",
        "tool_matrix_rows": [
            {
                "tool_matrix_ref": "tool-matrix:v75b:product-wedge:external-branch-blocked",
                "worker_role_refs": ["worker-role:v75b:product-wedge:external-branch-review"],
                "tool_id": "not_selected_here",
                "target_claim_refs": [
                    "dispatch-request:v75a:product-wedge:blocked",
                    "guardrail:v75a:product-wedge:non-execution",
                ],
                "target_namespace_kind": "dispatch_request",
                "claim_horizon": (
                    "Target-bound and horizon-bound blocked posture for future external branch "
                    "review only."
                ),
                "applicability_posture": "not_applicable_for_target_horizon",
                "observed_or_required_result_refs": ["docs/LOCKED_CONTINUATION_vNEXT_PLUS210.md"],
                "limitation_note": (
                    "Tool applicability is target-bound and horizon-bound with no command "
                    "permission and no dispatch."
                ),
            },
            {
                "tool_matrix_ref": "tool-matrix:v75b:self-evidencing:pytest-schema",
                "worker_role_refs": ["worker-role:v75b:self-evidencing:evidence-review"],
                "tool_id": "pytest",
                "target_claim_refs": [
                    "dispatch-request:v75a:self-evidencing:review",
                    "guardrail:v75a:self-evidencing:non-execution",
                ],
                "target_namespace_kind": "dispatch_request",
                "claim_horizon": ("Applicability to V75-A fixture and validator tests only."),
                "applicability_posture": "applicable_for_target_horizon",
                "observed_or_required_result_refs": [
                    "packages/adeu_repo_description/tests/test_dispatch_review_v75a.py"
                ],
                "limitation_note": (
                    "Tool applicability is target-bound and horizon-bound with no command "
                    "permission and no dispatch."
                ),
            },
        ],
        "tool_applicability_summary": (
            "Worker tool applicability rows are target-bound and horizon-bound; "
            "no command and no dispatch are authorized."
        ),
    }
    payload["tool_matrix_rows"] = sorted(
        payload["tool_matrix_rows"],
        key=lambda row: row["tool_matrix_ref"],
    )
    payload["worker_tool_applicability_matrix_id"] = _surface_id(
        "repo_worker_tool_applicability_matrix",
        REPO_WORKER_TOOL_APPLICABILITY_MATRIX_SCHEMA,
        payload,
        "worker_tool_applicability_matrix_id",
    )
    return RepoWorkerToolApplicabilityMatrix.model_validate(payload)


def derive_v75b_repo_dispatch_exception_register(
    *,
    repo_root: Path | None = None,
    dispatch_review_request: RepoDispatchReviewRequest | None = None,
) -> RepoDispatchExceptionRegister:
    _ = repo_root
    request = dispatch_review_request or derive_v75a_repo_dispatch_review_request()
    payload = {
        **_v75b_base_payload(
            schema=REPO_DISPATCH_EXCEPTION_REGISTER_SCHEMA,
            dispatch_review_request=request,
        ),
        "dispatch_exception_register_id": "",
        "exception_rows": [
            {
                "dispatch_exception_ref": "dispatch-exception:v75b:self-evidencing:upstream",
                "dispatch_request_refs": ["dispatch-request:v75a:self-evidencing:review"],
                "assignment_plan_refs": ["assignment-plan:v75b:self-evidencing:review-only"],
                "worker_role_refs": ["worker-role:v75b:self-evidencing:evidence-review"],
                "io_contract_refs": ["io-contract:v75b:self-evidencing:evidence-review"],
                "tool_matrix_refs": ["tool-matrix:v75b:self-evidencing:pytest-schema"],
                "exception_kind": "unresolved_projection_exception",
                "source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus209/"
                    "repo_dispatch_review_request_v209_reference.json"
                ],
                "blocking_posture": "carried_forward",
                "required_next_surface": "v75c_reconciliation_review",
                "limitation_note": (
                    "Upstream V74 exception is carried forward and not resolved; no dispatch."
                ),
            },
            {
                "dispatch_exception_ref": "dispatch-exception:v75b:product-wedge:authority",
                "dispatch_request_refs": ["dispatch-request:v75a:product-wedge:blocked"],
                "assignment_plan_refs": ["assignment-plan:v75b:product-wedge:blocked"],
                "worker_role_refs": ["worker-role:v75b:product-wedge:external-branch-review"],
                "io_contract_refs": ["io-contract:v75b:product-wedge:external-branch-review"],
                "tool_matrix_refs": ["tool-matrix:v75b:product-wedge:external-branch-blocked"],
                "exception_kind": "product_authority_gap",
                "source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus209/"
                    "repo_dispatch_review_request_v209_reference.json"
                ],
                "blocking_posture": "blocking",
                "required_next_surface": "future_product_review",
                "limitation_note": (
                    "Product authority gap remains blocking and not resolved; no dispatch."
                ),
            },
        ],
        "exception_register_summary": (
            "Dispatch exceptions remain visible and not resolved; no dispatch."
        ),
    }
    payload["exception_rows"] = sorted(
        payload["exception_rows"],
        key=lambda row: row["dispatch_exception_ref"],
    )
    payload["dispatch_exception_register_id"] = _surface_id(
        "repo_dispatch_exception_register",
        REPO_DISPATCH_EXCEPTION_REGISTER_SCHEMA,
        payload,
        "dispatch_exception_register_id",
    )
    return RepoDispatchExceptionRegister.model_validate(payload)


def derive_v75b_repo_multi_worker_assignment_plan(
    *,
    repo_root: Path | None = None,
    dispatch_review_request: RepoDispatchReviewRequest | None = None,
    worker_role_capacity_profile: RepoWorkerRoleCapacityProfile | None = None,
    worker_io_contract: RepoWorkerIOContract | None = None,
    worker_tool_applicability_matrix: RepoWorkerToolApplicabilityMatrix | None = None,
    dispatch_exception_register: RepoDispatchExceptionRegister | None = None,
) -> RepoMultiWorkerAssignmentPlan:
    _ = repo_root
    request = dispatch_review_request or derive_v75a_repo_dispatch_review_request()
    role_profile = worker_role_capacity_profile or derive_v75b_repo_worker_role_capacity_profile(
        dispatch_review_request=request
    )
    io_contract = worker_io_contract or derive_v75b_repo_worker_io_contract(
        dispatch_review_request=request
    )
    tool_matrix = (
        worker_tool_applicability_matrix
        or derive_v75b_repo_worker_tool_applicability_matrix(dispatch_review_request=request)
    )
    exception_register = (
        dispatch_exception_register
        or derive_v75b_repo_dispatch_exception_register(dispatch_review_request=request)
    )
    payload = {
        **_v75b_base_payload(
            schema=REPO_MULTI_WORKER_ASSIGNMENT_PLAN_SCHEMA,
            dispatch_review_request=request,
        ),
        "multi_worker_assignment_plan_id": "",
        "worker_role_capacity_profile_id": role_profile.worker_role_capacity_profile_id,
        "worker_io_contract_id": io_contract.worker_io_contract_id,
        "worker_tool_applicability_matrix_id": tool_matrix.worker_tool_applicability_matrix_id,
        "dispatch_exception_register_id": exception_register.dispatch_exception_register_id,
        "assignment_plan_rows": [
            {
                "assignment_plan_ref": "assignment-plan:v75b:self-evidencing:review-only",
                "dispatch_request_refs": ["dispatch-request:v75a:self-evidencing:review"],
                "worker_role_refs": ["worker-role:v75b:self-evidencing:evidence-review"],
                "io_contract_refs": ["io-contract:v75b:self-evidencing:evidence-review"],
                "tool_applicability_refs": ["tool-matrix:v75b:self-evidencing:pytest-schema"],
                "exception_refs": ["dispatch-exception:v75b:self-evidencing:upstream"],
                "required_later_authority_refs": [
                    "authority:v75a:self-evidencing:dispatch-execution",
                    "authority:v75a:self-evidencing:human-review",
                ],
                "assignment_plan_posture": "plan_ready_for_review",
                "assignment_execution_posture": "no_execution_authorized",
                "non_execution_guardrail_refs": ["guardrail:v75a:self-evidencing:non-execution"],
                "limitation_note": (
                    "This is an orchestration plan with no worker assignment, no command, "
                    "and no dispatch."
                ),
            },
            {
                "assignment_plan_ref": "assignment-plan:v75b:product-wedge:blocked",
                "dispatch_request_refs": ["dispatch-request:v75a:product-wedge:blocked"],
                "worker_role_refs": ["worker-role:v75b:product-wedge:external-branch-review"],
                "io_contract_refs": ["io-contract:v75b:product-wedge:external-branch-review"],
                "tool_applicability_refs": [
                    "tool-matrix:v75b:product-wedge:external-branch-blocked"
                ],
                "exception_refs": ["dispatch-exception:v75b:product-wedge:authority"],
                "required_later_authority_refs": ["authority:v75a:product-wedge:product-review"],
                "assignment_plan_posture": "blocked_by_later_authority",
                "assignment_execution_posture": "no_execution_authorized",
                "non_execution_guardrail_refs": ["guardrail:v75a:product-wedge:non-execution"],
                "limitation_note": (
                    "External branch/product pressure remains blocked plan posture with "
                    "no worker assignment, no command, and no dispatch."
                ),
            },
        ],
        "assignment_plan_summary": (
            "Multi-worker assignment plans remain plans only: no worker assignment, "
            "no command, and no dispatch."
        ),
    }
    payload["assignment_plan_rows"] = sorted(
        payload["assignment_plan_rows"],
        key=lambda row: row["assignment_plan_ref"],
    )
    payload["multi_worker_assignment_plan_id"] = _surface_id(
        "repo_multi_worker_assignment_plan",
        REPO_MULTI_WORKER_ASSIGNMENT_PLAN_SCHEMA,
        payload,
        "multi_worker_assignment_plan_id",
    )
    return RepoMultiWorkerAssignmentPlan.model_validate(payload)


def validate_v75b_worker_orchestration_bundle(
    *,
    dispatch_source_index: RepoDispatchSourceIndex,
    dispatch_review_request: RepoDispatchReviewRequest,
    dispatch_non_execution_guardrail: RepoDispatchNonExecutionGuardrail,
    worker_role_capacity_profile: RepoWorkerRoleCapacityProfile,
    multi_worker_assignment_plan: RepoMultiWorkerAssignmentPlan,
    worker_io_contract: RepoWorkerIOContract,
    worker_tool_applicability_matrix: RepoWorkerToolApplicabilityMatrix,
    dispatch_exception_register: RepoDispatchExceptionRegister,
) -> None:
    validate_v75a_dispatch_review_bundle(
        dispatch_source_index=dispatch_source_index,
        dispatch_review_request=dispatch_review_request,
        dispatch_non_execution_guardrail=dispatch_non_execution_guardrail,
    )
    surfaces = [
        worker_role_capacity_profile,
        multi_worker_assignment_plan,
        worker_io_contract,
        worker_tool_applicability_matrix,
        dispatch_exception_register,
    ]
    for surface in surfaces:
        if surface.dispatch_review_request_id != dispatch_review_request.dispatch_review_request_id:
            raise ValueError("V75-B surfaces must reference released V75-A request surface")
        if (
            surface.review_id,
            surface.snapshot_id,
            surface.source_set_id,
        ) != (
            "review:v75b:worker-orchestration-planning",
            "vNext+209-closed-on-main",
            "source-set:v75b:released-v75a-dispatch-review",
        ):
            raise ValueError("V75-B surfaces must share worker-planning provenance")

    if (
        multi_worker_assignment_plan.worker_role_capacity_profile_id
        != worker_role_capacity_profile.worker_role_capacity_profile_id
    ):
        raise ValueError("assignment plan must reference worker role profile")
    if (
        multi_worker_assignment_plan.worker_io_contract_id
        != worker_io_contract.worker_io_contract_id
    ):
        raise ValueError("assignment plan must reference worker IO contract")
    if (
        multi_worker_assignment_plan.worker_tool_applicability_matrix_id
        != worker_tool_applicability_matrix.worker_tool_applicability_matrix_id
    ):
        raise ValueError("assignment plan must reference tool applicability matrix")
    if (
        multi_worker_assignment_plan.dispatch_exception_register_id
        != dispatch_exception_register.dispatch_exception_register_id
    ):
        raise ValueError("assignment plan must reference dispatch exception register")

    request_rows = {row.dispatch_request_ref: row for row in dispatch_review_request.request_rows}
    guardrail_rows = {
        row.guardrail_ref: row for row in dispatch_non_execution_guardrail.guardrail_rows
    }
    source_roles = {
        row.source_ref: row.dispatch_source_role for row in dispatch_source_index.source_rows
    }
    role_rows = {row.worker_role_ref: row for row in worker_role_capacity_profile.worker_role_rows}
    io_rows = {row.io_contract_ref: row for row in worker_io_contract.io_contract_rows}
    tool_rows = {
        row.tool_matrix_ref: row for row in worker_tool_applicability_matrix.tool_matrix_rows
    }
    exception_rows = {
        row.dispatch_exception_ref: row for row in dispatch_exception_register.exception_rows
    }

    for io_row in worker_io_contract.io_contract_rows:
        if any(role_ref not in role_rows for role_ref in io_row.worker_role_refs):
            raise ValueError("worker IO contracts must reference known worker roles")

    for tool_row in worker_tool_applicability_matrix.tool_matrix_rows:
        if any(role_ref not in role_rows for role_ref in tool_row.worker_role_refs):
            raise ValueError("tool applicability rows must reference known worker roles")

    for exception_row in dispatch_exception_register.exception_rows:
        if any(ref not in request_rows for ref in exception_row.dispatch_request_refs):
            raise ValueError("dispatch exceptions must reference known V75-A requests")
        if any(ref not in role_rows for ref in exception_row.worker_role_refs):
            raise ValueError("dispatch exceptions must reference known worker roles")
        if any(ref not in io_rows for ref in exception_row.io_contract_refs):
            raise ValueError("dispatch exceptions must reference known IO contracts")
        if any(ref not in tool_rows for ref in exception_row.tool_matrix_refs):
            raise ValueError("dispatch exceptions must reference known tool rows")

    for assignment_row in multi_worker_assignment_plan.assignment_plan_rows:
        if any(ref not in request_rows for ref in assignment_row.dispatch_request_refs):
            raise ValueError("assignment plans must reference released V75-A request rows")
        if any(ref not in role_rows for ref in assignment_row.worker_role_refs):
            raise ValueError("assignment plans must reference known worker roles")
        if any(ref not in io_rows for ref in assignment_row.io_contract_refs):
            raise ValueError("assignment plans must reference known IO contracts")
        if any(ref not in tool_rows for ref in assignment_row.tool_applicability_refs):
            raise ValueError("assignment plans must reference known tool applicability rows")
        if any(ref not in exception_rows for ref in assignment_row.exception_refs):
            raise ValueError("assignment plans must reference known dispatch exceptions")
        if any(ref not in guardrail_rows for ref in assignment_row.non_execution_guardrail_refs):
            raise ValueError("assignment plans must reference V75-A non-execution guardrails")

        assignment_role_refs = set(assignment_row.worker_role_refs)
        assignment_io_role_refs: set[str] = set()
        for io_ref in assignment_row.io_contract_refs:
            assignment_io_role_refs.update(io_rows[io_ref].worker_role_refs)
        if not assignment_role_refs.issubset(assignment_io_role_refs):
            raise ValueError("assignment IO refs must cover assignment worker roles")
        if not assignment_io_role_refs.issubset(assignment_role_refs):
            raise ValueError("assignment IO refs must be scoped to assignment worker roles")

        assignment_tool_role_refs: set[str] = set()
        for tool_ref in assignment_row.tool_applicability_refs:
            assignment_tool_role_refs.update(tool_rows[tool_ref].worker_role_refs)
        if not assignment_role_refs.issubset(assignment_tool_role_refs):
            raise ValueError("assignment tool refs must cover assignment worker roles")
        if not assignment_tool_role_refs.issubset(assignment_role_refs):
            raise ValueError("assignment tool refs must be scoped to assignment worker roles")

        authority_refs: set[str] = set()
        request_source_roles: set[str] = set()
        for request_ref in assignment_row.dispatch_request_refs:
            request_row = request_rows[request_ref]
            authority_refs.update(request_row.required_later_authority_refs)
            request_source_roles.update(
                source_roles[source_ref]
                for source_ref in request_row.source_refs
                if source_ref in source_roles
            )
            if request_row.carried_upstream_exception_refs and not any(
                request_ref in exception_rows[exception_ref].dispatch_request_refs
                for exception_ref in assignment_row.exception_refs
            ):
                raise ValueError("assignment plans must carry upstream exception refs")
        if not authority_refs.issubset(set(assignment_row.required_later_authority_refs)):
            raise ValueError("assignment plans must carry required later authority refs")

        assignment_roles = [role_rows[role_ref] for role_ref in assignment_row.worker_role_refs]
        if any(role.role_kind == "external_branch_review_worker" for role in assignment_roles):
            if "v43_branch_posture_source" not in request_source_roles and (
                assignment_row.assignment_plan_posture
                not in {"blocked_by_later_authority", "future_family_only"}
            ):
                raise ValueError(
                    "external branch worker plans require V43 source or blocked posture"
                )


def derive_v75b_worker_orchestration_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoWorkerRoleCapacityProfile,
    RepoMultiWorkerAssignmentPlan,
    RepoWorkerIOContract,
    RepoWorkerToolApplicabilityMatrix,
    RepoDispatchExceptionRegister,
]:
    source_index, request, guardrail = derive_v75a_dispatch_review_bundle(repo_root=repo_root)
    role_profile = derive_v75b_repo_worker_role_capacity_profile(
        repo_root=repo_root,
        dispatch_review_request=request,
    )
    io_contract = derive_v75b_repo_worker_io_contract(
        repo_root=repo_root,
        dispatch_review_request=request,
    )
    tool_matrix = derive_v75b_repo_worker_tool_applicability_matrix(
        repo_root=repo_root,
        dispatch_review_request=request,
    )
    exception_register = derive_v75b_repo_dispatch_exception_register(
        repo_root=repo_root,
        dispatch_review_request=request,
    )
    assignment_plan = derive_v75b_repo_multi_worker_assignment_plan(
        repo_root=repo_root,
        dispatch_review_request=request,
        worker_role_capacity_profile=role_profile,
        worker_io_contract=io_contract,
        worker_tool_applicability_matrix=tool_matrix,
        dispatch_exception_register=exception_register,
    )
    validate_v75b_worker_orchestration_bundle(
        dispatch_source_index=source_index,
        dispatch_review_request=request,
        dispatch_non_execution_guardrail=guardrail,
        worker_role_capacity_profile=role_profile,
        multi_worker_assignment_plan=assignment_plan,
        worker_io_contract=io_contract,
        worker_tool_applicability_matrix=tool_matrix,
        dispatch_exception_register=exception_register,
    )
    return role_profile, assignment_plan, io_contract, tool_matrix, exception_register


class RepoProjectedWorkerOutputSlotRow(_CartographyBase):
    projected_output_slot_ref: str
    assignment_plan_refs: list[str] = Field(min_length=1)
    io_contract_refs: list[str] = Field(min_length=1)
    expected_output_kind: str
    output_presence_posture: OutputPresencePosture
    source_refs: list[str] = Field(min_length=1)
    non_truth_guardrail: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_projected_output_slot_row(self) -> RepoProjectedWorkerOutputSlotRow:
        _non_empty(self.projected_output_slot_ref, field_name="projected_output_slot_ref")
        _non_empty(self.expected_output_kind, field_name="expected_output_kind")
        for field_name in ("assignment_plan_refs", "io_contract_refs", "source_refs"):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        _reject_unnegated_authority_claim(
            self.non_truth_guardrail, field_name="non_truth_guardrail"
        )
        _reject_unnegated_authority_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.non_truth_guardrail,
            field_name="non_truth_guardrail",
            terms=("not truth", "review"),
        )
        if self.output_presence_posture == "projected_not_observed":
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("projected", "not observed", "no dispatch"),
            )
        return self


class RepoWorkerOutputRelationRow(_CartographyBase):
    relation_ref: str
    left_output_ref: str
    right_output_ref: str
    claim_horizon: str
    relation_kind: WorkerOutputRelationKind
    source_refs: list[str] = Field(min_length=1)
    authority_boundary_posture: str
    required_next_review_surface: ReconciliationRequiredNextReviewSurface
    limitation_note: str

    @model_validator(mode="after")
    def _validate_worker_output_relation_row(self) -> RepoWorkerOutputRelationRow:
        _non_empty(self.relation_ref, field_name="relation_ref")
        _non_empty(self.left_output_ref, field_name="left_output_ref")
        _non_empty(self.right_output_ref, field_name="right_output_ref")
        _non_empty(self.claim_horizon, field_name="claim_horizon")
        object.__setattr__(
            self,
            "source_refs",
            _sorted_unique(self.source_refs, field_name="source_refs"),
        )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        _reject_unnegated_authority_claim(
            self.authority_boundary_posture,
            field_name="authority_boundary_posture",
        )
        _reject_unnegated_authority_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("relation", "not truth"),
        )
        return self


class RepoWorkerOutputReconciliationPlanRow(_CartographyBase):
    reconciliation_plan_ref: str
    dispatch_request_refs: list[str] = Field(min_length=1)
    assignment_plan_refs: list[str] = Field(min_length=1)
    io_contract_refs: list[str] = Field(min_length=1)
    projected_output_slot_refs: list[str] = Field(default_factory=list)
    observed_worker_output_refs: list[str] = Field(default_factory=list)
    output_presence_posture: OutputPresencePosture
    dispatch_execution_posture: V75CDispatchExecutionPosture
    relation_refs: list[str] = Field(min_length=1)
    exception_refs: list[str] = Field(default_factory=list)
    non_truth_guardrail: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_worker_output_reconciliation_plan_row(
        self,
    ) -> RepoWorkerOutputReconciliationPlanRow:
        _non_empty(self.reconciliation_plan_ref, field_name="reconciliation_plan_ref")
        for field_name in (
            "dispatch_request_refs",
            "assignment_plan_refs",
            "io_contract_refs",
            "projected_output_slot_refs",
            "observed_worker_output_refs",
            "relation_refs",
            "exception_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        if self.output_presence_posture == "projected_not_observed":
            if self.observed_worker_output_refs:
                raise ValueError("projected output rows must not carry observed worker outputs")
            if not self.projected_output_slot_refs:
                raise ValueError("projected output rows require projected output slot refs")
        if (
            self.output_presence_posture
            in {
                "observed_from_authorized_prior_run",
                "observed_from_support_artifact",
            }
            and not self.observed_worker_output_refs
        ):
            raise ValueError("observed output posture requires observed worker output refs")
        _reject_unnegated_authority_claim(
            self.non_truth_guardrail, field_name="non_truth_guardrail"
        )
        _reject_unnegated_authority_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.non_truth_guardrail,
            field_name="non_truth_guardrail",
            terms=("not truth", "review"),
        )
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("no dispatch", "no command"),
        )
        return self


class RepoWorkerOutputReconciliationPlan(_CartographyBase):
    schema: Literal["repo_worker_output_reconciliation_plan@1"] = (
        REPO_WORKER_OUTPUT_RECONCILIATION_PLAN_SCHEMA
    )
    worker_output_reconciliation_plan_id: str
    dispatch_review_request_id: str
    multi_worker_assignment_plan_id: str
    worker_io_contract_id: str
    dispatch_exception_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    projected_output_slot_rows: list[RepoProjectedWorkerOutputSlotRow] = Field(min_length=1)
    relation_rows: list[RepoWorkerOutputRelationRow] = Field(min_length=1)
    reconciliation_plan_rows: list[RepoWorkerOutputReconciliationPlanRow] = Field(min_length=1)
    reconciliation_summary: str

    @model_validator(mode="after")
    def _validate_worker_output_reconciliation_plan(
        self,
    ) -> RepoWorkerOutputReconciliationPlan:
        object.__setattr__(
            self,
            "projected_output_slot_rows",
            _sorted_unique_by_ref(
                self.projected_output_slot_rows,
                attr="projected_output_slot_ref",
                field_name="projected_output_slot_rows",
            ),
        )
        object.__setattr__(
            self,
            "relation_rows",
            _sorted_unique_by_ref(
                self.relation_rows,
                attr="relation_ref",
                field_name="relation_rows",
            ),
        )
        object.__setattr__(
            self,
            "reconciliation_plan_rows",
            _sorted_unique_by_ref(
                self.reconciliation_plan_rows,
                attr="reconciliation_plan_ref",
                field_name="reconciliation_plan_rows",
            ),
        )
        _require_terms(
            self.reconciliation_summary,
            field_name="reconciliation_summary",
            terms=("projected", "not truth", "no dispatch"),
        )
        expected_id = _surface_id(
            "repo_worker_output_reconciliation_plan",
            self.schema,
            self.model_dump(mode="json"),
            "worker_output_reconciliation_plan_id",
        )
        if self.worker_output_reconciliation_plan_id != expected_id:
            raise ValueError(
                "worker_output_reconciliation_plan_id does not match canonical payload hash"
            )
        return self


class RepoDispatchReconciliationContractRow(_CartographyBase):
    contract_ref: str
    reconciliation_plan_refs: list[str] = Field(min_length=1)
    required_review_roles: list[WorkerRoleKind] = Field(min_length=1)
    required_authority_refs: list[str] = Field(min_length=1)
    allowed_settlement_postures: list[DispatchSettlementPosture] = Field(min_length=1)
    forbidden_inferences: list[DispatchForbiddenInference] = Field(min_length=1)
    handoff_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_dispatch_reconciliation_contract_row(
        self,
    ) -> RepoDispatchReconciliationContractRow:
        _non_empty(self.contract_ref, field_name="contract_ref")
        for field_name in (
            "reconciliation_plan_refs",
            "required_review_roles",
            "required_authority_refs",
            "allowed_settlement_postures",
            "forbidden_inferences",
            "handoff_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        missing = _REQUIRED_DISPATCH_FORBIDDEN_INFERENCES.difference(self.forbidden_inferences)
        if missing:
            raise ValueError(
                f"dispatch reconciliation contracts omit forbidden inferences: {sorted(missing)}"
            )
        _reject_unnegated_authority_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("contract", "forbidden", "no dispatch"),
        )
        return self


class RepoDispatchReconciliationContract(_CartographyBase):
    schema: Literal["repo_dispatch_reconciliation_contract@1"] = (
        REPO_DISPATCH_RECONCILIATION_CONTRACT_SCHEMA
    )
    dispatch_reconciliation_contract_id: str
    worker_output_reconciliation_plan_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    contract_rows: list[RepoDispatchReconciliationContractRow] = Field(min_length=1)
    contract_summary: str

    @model_validator(mode="after")
    def _validate_dispatch_reconciliation_contract(
        self,
    ) -> RepoDispatchReconciliationContract:
        object.__setattr__(
            self,
            "contract_rows",
            _sorted_unique_by_ref(
                self.contract_rows,
                attr="contract_ref",
                field_name="contract_rows",
            ),
        )
        _require_terms(
            self.contract_summary,
            field_name="contract_summary",
            terms=("forbidden", "not truth", "no dispatch"),
        )
        expected_id = _surface_id(
            "repo_dispatch_reconciliation_contract",
            self.schema,
            self.model_dump(mode="json"),
            "dispatch_reconciliation_contract_id",
        )
        if self.dispatch_reconciliation_contract_id != expected_id:
            raise ValueError(
                "dispatch_reconciliation_contract_id does not match canonical payload hash"
            )
        return self


class RepoPostDispatchReviewHandoffRow(_CartographyBase):
    handoff_ref: str
    dispatch_request_refs: list[str] = Field(min_length=1)
    assignment_plan_refs: list[str] = Field(min_length=1)
    reconciliation_plan_refs: list[str] = Field(min_length=1)
    reconciliation_contract_refs: list[str] = Field(min_length=1)
    handoff_target: PostDispatchReviewHandoffTarget
    handoff_subject_horizon: PostDispatchReviewHandoffSubjectHorizon
    handoff_posture: PostDispatchReviewHandoffPosture
    carried_exception_refs: list[str] = Field(default_factory=list)
    required_later_authority_refs: list[str] = Field(default_factory=list)
    non_execution_guardrail: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_post_dispatch_review_handoff_row(self) -> RepoPostDispatchReviewHandoffRow:
        _non_empty(self.handoff_ref, field_name="handoff_ref")
        for field_name in (
            "dispatch_request_refs",
            "assignment_plan_refs",
            "reconciliation_plan_refs",
            "reconciliation_contract_refs",
            "carried_exception_refs",
            "required_later_authority_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        _reject_unnegated_authority_claim(
            self.non_execution_guardrail, field_name="non_execution_guardrail"
        )
        _reject_unnegated_authority_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.non_execution_guardrail,
            field_name="non_execution_guardrail",
            terms=("no dispatch", "no command", "no runtime", "no product", "no release"),
        )
        if self.handoff_target == "future_outcome_review":
            if self.handoff_subject_horizon not in {
                "dispatch_review_process_outcome",
                "projected_orchestration_plan_review",
                "authorized_prior_worker_run_output",
                "future_runtime_execution_outcome",
            }:
                raise ValueError("future outcome review handoff requires subject horizon")
        return self


class RepoPostDispatchReviewHandoff(_CartographyBase):
    schema: Literal["repo_post_dispatch_review_handoff@1"] = (
        REPO_POST_DISPATCH_REVIEW_HANDOFF_SCHEMA
    )
    post_dispatch_review_handoff_id: str
    worker_output_reconciliation_plan_id: str
    dispatch_reconciliation_contract_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    handoff_rows: list[RepoPostDispatchReviewHandoffRow] = Field(min_length=1)
    handoff_summary: str

    @model_validator(mode="after")
    def _validate_post_dispatch_review_handoff(self) -> RepoPostDispatchReviewHandoff:
        object.__setattr__(
            self,
            "handoff_rows",
            _sorted_unique_by_ref(
                self.handoff_rows,
                attr="handoff_ref",
                field_name="handoff_rows",
            ),
        )
        _require_terms(
            self.handoff_summary,
            field_name="handoff_summary",
            terms=("review", "no dispatch", "no runtime", "no release"),
        )
        expected_id = _surface_id(
            "repo_post_dispatch_review_handoff",
            self.schema,
            self.model_dump(mode="json"),
            "post_dispatch_review_handoff_id",
        )
        if self.post_dispatch_review_handoff_id != expected_id:
            raise ValueError(
                "post_dispatch_review_handoff_id does not match canonical payload hash"
            )
        return self


class RepoDispatchReviewFamilyCloseoutAlignment(_CartographyBase):
    schema: Literal["repo_dispatch_review_family_closeout_alignment@1"] = (
        REPO_DISPATCH_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
    )
    dispatch_review_family_closeout_alignment_id: str
    family: Literal["V75"]
    closed_by_arc: Literal["vNext+211"]
    review_id: str
    snapshot_id: str
    source_set_id: str
    closed_slice_ladder: list[Literal["V75-A", "V75-B", "V75-C"]] = Field(min_length=3)
    shipped_record_shapes: list[str] = Field(min_length=1)
    consumed_source_families: list[str] = Field(min_length=1)
    future_family_authority: list[str] = Field(min_length=1)
    unselected_future_surfaces: list[str] = Field(min_length=1)
    dispatch_review_authority_boundary: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_dispatch_review_family_closeout_alignment(
        self,
    ) -> RepoDispatchReviewFamilyCloseoutAlignment:
        for field_name in (
            "closed_slice_ladder",
            "shipped_record_shapes",
            "consumed_source_families",
            "future_family_authority",
            "unselected_future_surfaces",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        if set(self.closed_slice_ladder) != {"V75-A", "V75-B", "V75-C"}:
            raise ValueError("V75 family closeout alignment must close A/B/C ladder")
        for shape in _V75C_SCHEMA_NAMES:
            if shape not in self.shipped_record_shapes:
                raise ValueError("V75-C family closeout alignment omits shipped C surfaces")
        _reject_unnegated_authority_claim(
            self.dispatch_review_authority_boundary,
            field_name="dispatch_review_authority_boundary",
        )
        _reject_unnegated_authority_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.dispatch_review_authority_boundary,
            field_name="dispatch_review_authority_boundary",
            terms=("dispatch review", "no dispatch", "no runtime", "no release"),
        )
        expected_id = _surface_id(
            "repo_dispatch_review_family_closeout_alignment",
            self.schema,
            self.model_dump(mode="json"),
            "dispatch_review_family_closeout_alignment_id",
        )
        if self.dispatch_review_family_closeout_alignment_id != expected_id:
            raise ValueError(
                "dispatch_review_family_closeout_alignment_id does not match canonical payload hash"
            )
        return self


def _v75c_base_payload(
    *,
    schema: str,
    dispatch_review_request: RepoDispatchReviewRequest,
) -> dict[str, str]:
    return {
        "schema": schema,
        "review_id": "review:v75c:reconciliation-contract-handoff-closeout",
        "snapshot_id": "vNext+210-closed-on-main",
        "source_set_id": "source-set:v75c:released-v75a-v75b-dispatch-review",
        "dispatch_review_request_id": dispatch_review_request.dispatch_review_request_id,
    }


def derive_v75c_repo_worker_output_reconciliation_plan(
    *,
    repo_root: Path | None = None,
    dispatch_review_request: RepoDispatchReviewRequest | None = None,
    multi_worker_assignment_plan: RepoMultiWorkerAssignmentPlan | None = None,
    worker_io_contract: RepoWorkerIOContract | None = None,
    dispatch_exception_register: RepoDispatchExceptionRegister | None = None,
) -> RepoWorkerOutputReconciliationPlan:
    source_index, request, guardrail = derive_v75a_dispatch_review_bundle(repo_root=repo_root)
    role_profile, assignment_plan, io_contract, tool_matrix, exception_register = (
        derive_v75b_worker_orchestration_bundle(repo_root=repo_root)
    )
    _ = source_index, guardrail, role_profile, tool_matrix
    request = dispatch_review_request or request
    assignment_plan = multi_worker_assignment_plan or assignment_plan
    io_contract = worker_io_contract or io_contract
    exception_register = dispatch_exception_register or exception_register
    payload = {
        **_v75c_base_payload(
            schema=REPO_WORKER_OUTPUT_RECONCILIATION_PLAN_SCHEMA,
            dispatch_review_request=request,
        ),
        "worker_output_reconciliation_plan_id": "",
        "multi_worker_assignment_plan_id": assignment_plan.multi_worker_assignment_plan_id,
        "worker_io_contract_id": io_contract.worker_io_contract_id,
        "dispatch_exception_register_id": exception_register.dispatch_exception_register_id,
        "projected_output_slot_rows": [
            {
                "projected_output_slot_ref": "projected-output:v75c:product-wedge:blocked-note",
                "assignment_plan_refs": ["assignment-plan:v75b:product-wedge:blocked"],
                "io_contract_refs": ["io-contract:v75b:product-wedge:external-branch-review"],
                "expected_output_kind": "blocked_external_branch_review_note",
                "output_presence_posture": "projected_not_observed",
                "source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus210/"
                    "repo_worker_io_contract_v210_reference.json"
                ],
                "non_truth_guardrail": "Projected worker output is for review and not truth.",
                "limitation_note": (
                    "Projected not observed output slot only; no dispatch and no command."
                ),
            },
            {
                "projected_output_slot_ref": "projected-output:v75c:self-evidencing:review-note",
                "assignment_plan_refs": ["assignment-plan:v75b:self-evidencing:review-only"],
                "io_contract_refs": ["io-contract:v75b:self-evidencing:evidence-review"],
                "expected_output_kind": "worker_review_note_for_reconciliation",
                "output_presence_posture": "projected_not_observed",
                "source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus210/"
                    "repo_worker_io_contract_v210_reference.json"
                ],
                "non_truth_guardrail": "Projected worker output is for review and not truth.",
                "limitation_note": (
                    "Projected not observed output slot only; no dispatch and no command."
                ),
            },
        ],
        "relation_rows": [
            {
                "relation_ref": "relation:v75c:self-evidencing:single-projected-output",
                "left_output_ref": "projected-output:v75c:self-evidencing:review-note",
                "right_output_ref": "projected-output:v75c:self-evidencing:review-note",
                "claim_horizon": (
                    "Single projected output slot; no observed worker output relation yet."
                ),
                "relation_kind": "single_output_no_relation",
                "source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus210/"
                    "repo_multi_worker_assignment_plan_v210_reference.json"
                ],
                "authority_boundary_posture": (
                    "Relation posture is review-only and not worker output truth."
                ),
                "required_next_review_surface": "future_reconciliation_or_arbiter_review",
                "limitation_note": (
                    "Projected relation is not truth and requires later relation review."
                ),
            },
            {
                "relation_ref": "relation:v75c:product-wedge:blocked-projected-output",
                "left_output_ref": "projected-output:v75c:product-wedge:blocked-note",
                "right_output_ref": "projected-output:v75c:product-wedge:blocked-note",
                "claim_horizon": (
                    "Blocked product/external branch projected output slot; no observed output."
                ),
                "relation_kind": "single_output_no_relation",
                "source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus210/"
                    "repo_dispatch_exception_register_v210_reference.json"
                ],
                "authority_boundary_posture": (
                    "Relation posture carries blocker for review and is not truth."
                ),
                "required_next_review_surface": "future_reconciliation_or_arbiter_review",
                "limitation_note": (
                    "Blocked projected relation is not truth and carries blocker for review."
                ),
            },
        ],
        "reconciliation_plan_rows": [
            {
                "reconciliation_plan_ref": "reconciliation-plan:v75c:product-wedge:blocked",
                "dispatch_request_refs": ["dispatch-request:v75a:product-wedge:blocked"],
                "assignment_plan_refs": ["assignment-plan:v75b:product-wedge:blocked"],
                "io_contract_refs": ["io-contract:v75b:product-wedge:external-branch-review"],
                "projected_output_slot_refs": ["projected-output:v75c:product-wedge:blocked-note"],
                "observed_worker_output_refs": [],
                "output_presence_posture": "projected_not_observed",
                "dispatch_execution_posture": "no_dispatch_executed_by_v75",
                "relation_refs": ["relation:v75c:product-wedge:blocked-projected-output"],
                "exception_refs": ["dispatch-exception:v75b:product-wedge:authority"],
                "non_truth_guardrail": "Projected worker output is for review and not truth.",
                "limitation_note": (
                    "Reconciliation plan is projected with no dispatch, no command, and "
                    "blocking authority carried forward."
                ),
            },
            {
                "reconciliation_plan_ref": "reconciliation-plan:v75c:self-evidencing:projected",
                "dispatch_request_refs": ["dispatch-request:v75a:self-evidencing:review"],
                "assignment_plan_refs": ["assignment-plan:v75b:self-evidencing:review-only"],
                "io_contract_refs": ["io-contract:v75b:self-evidencing:evidence-review"],
                "projected_output_slot_refs": ["projected-output:v75c:self-evidencing:review-note"],
                "observed_worker_output_refs": [],
                "output_presence_posture": "projected_not_observed",
                "dispatch_execution_posture": "no_dispatch_executed_by_v75",
                "relation_refs": ["relation:v75c:self-evidencing:single-projected-output"],
                "exception_refs": ["dispatch-exception:v75b:self-evidencing:upstream"],
                "non_truth_guardrail": "Projected worker output is for review and not truth.",
                "limitation_note": (
                    "Reconciliation plan is projected with no dispatch, no command, and "
                    "no observed worker output."
                ),
            },
        ],
        "reconciliation_summary": (
            "Projected worker output reconciliation is not truth and records no dispatch."
        ),
    }
    payload["projected_output_slot_rows"] = sorted(
        payload["projected_output_slot_rows"],
        key=lambda row: row["projected_output_slot_ref"],
    )
    payload["relation_rows"] = sorted(payload["relation_rows"], key=lambda row: row["relation_ref"])
    payload["reconciliation_plan_rows"] = sorted(
        payload["reconciliation_plan_rows"],
        key=lambda row: row["reconciliation_plan_ref"],
    )
    payload["worker_output_reconciliation_plan_id"] = _surface_id(
        "repo_worker_output_reconciliation_plan",
        REPO_WORKER_OUTPUT_RECONCILIATION_PLAN_SCHEMA,
        payload,
        "worker_output_reconciliation_plan_id",
    )
    return RepoWorkerOutputReconciliationPlan.model_validate(payload)


def derive_v75c_repo_dispatch_reconciliation_contract(
    *,
    repo_root: Path | None = None,
    worker_output_reconciliation_plan: RepoWorkerOutputReconciliationPlan | None = None,
) -> RepoDispatchReconciliationContract:
    plan = (
        worker_output_reconciliation_plan
        or derive_v75c_repo_worker_output_reconciliation_plan(repo_root=repo_root)
    )
    payload = {
        "schema": REPO_DISPATCH_RECONCILIATION_CONTRACT_SCHEMA,
        "dispatch_reconciliation_contract_id": "",
        "worker_output_reconciliation_plan_id": plan.worker_output_reconciliation_plan_id,
        "review_id": plan.review_id,
        "snapshot_id": plan.snapshot_id,
        "source_set_id": plan.source_set_id,
        "contract_rows": [
            {
                "contract_ref": "contract:v75c:dispatch-reconciliation:review-only",
                "reconciliation_plan_refs": [
                    row.reconciliation_plan_ref for row in plan.reconciliation_plan_rows
                ],
                "required_review_roles": ["adversarial_review_worker", "reconciliation_worker"],
                "required_authority_refs": sorted(
                    [
                        "authority:v75a:self-evidencing:dispatch-execution",
                        "authority:v75a:self-evidencing:human-review",
                        "authority:v75a:product-wedge:product-review",
                    ]
                ),
                "allowed_settlement_postures": sorted(
                    [
                        "preserve_for_later_review",
                        "requires_adversarial_review",
                        "requires_human_ratification",
                        "requires_product_review",
                        "deferred_no_selection",
                    ]
                ),
                "forbidden_inferences": sorted(_REQUIRED_DISPATCH_FORBIDDEN_INFERENCES),
                "handoff_refs": ["handoff:v75c:self-evidencing:future-outcome-review"],
                "limitation_note": (
                    "Dispatch reconciliation contract states forbidden inferences with no dispatch."
                ),
            }
        ],
        "contract_summary": ("Forbidden inferences keep worker output not truth with no dispatch."),
    }
    payload["contract_rows"] = sorted(
        payload["contract_rows"],
        key=lambda row: row["contract_ref"],
    )
    payload["dispatch_reconciliation_contract_id"] = _surface_id(
        "repo_dispatch_reconciliation_contract",
        REPO_DISPATCH_RECONCILIATION_CONTRACT_SCHEMA,
        payload,
        "dispatch_reconciliation_contract_id",
    )
    return RepoDispatchReconciliationContract.model_validate(payload)


def derive_v75c_repo_post_dispatch_review_handoff(
    *,
    repo_root: Path | None = None,
    worker_output_reconciliation_plan: RepoWorkerOutputReconciliationPlan | None = None,
    dispatch_reconciliation_contract: RepoDispatchReconciliationContract | None = None,
) -> RepoPostDispatchReviewHandoff:
    plan = (
        worker_output_reconciliation_plan
        or derive_v75c_repo_worker_output_reconciliation_plan(repo_root=repo_root)
    )
    contract = (
        dispatch_reconciliation_contract
        or derive_v75c_repo_dispatch_reconciliation_contract(
            repo_root=repo_root,
            worker_output_reconciliation_plan=plan,
        )
    )
    payload = {
        "schema": REPO_POST_DISPATCH_REVIEW_HANDOFF_SCHEMA,
        "post_dispatch_review_handoff_id": "",
        "worker_output_reconciliation_plan_id": plan.worker_output_reconciliation_plan_id,
        "dispatch_reconciliation_contract_id": contract.dispatch_reconciliation_contract_id,
        "review_id": plan.review_id,
        "snapshot_id": plan.snapshot_id,
        "source_set_id": plan.source_set_id,
        "handoff_rows": [
            {
                "handoff_ref": "handoff:v75c:product-wedge:arbiter-settlement",
                "dispatch_request_refs": ["dispatch-request:v75a:product-wedge:blocked"],
                "assignment_plan_refs": ["assignment-plan:v75b:product-wedge:blocked"],
                "reconciliation_plan_refs": ["reconciliation-plan:v75c:product-wedge:blocked"],
                "reconciliation_contract_refs": [
                    "contract:v75c:dispatch-reconciliation:review-only"
                ],
                "handoff_target": "future_reconciliation_or_arbiter_review",
                "handoff_subject_horizon": "product_review_pressure",
                "handoff_posture": "blocked_by_required_later_authority",
                "carried_exception_refs": ["dispatch-exception:v75b:product-wedge:authority"],
                "required_later_authority_refs": ["authority:v75a:product-wedge:product-review"],
                "non_execution_guardrail": (
                    "Handoff is review-only with no dispatch, no command, no runtime, "
                    "no product authorization, and no release."
                ),
                "limitation_note": (
                    "Product pressure remains blocked and carried for later review with "
                    "no dispatch execution."
                ),
            },
            {
                "handoff_ref": "handoff:v75c:self-evidencing:future-outcome-review",
                "dispatch_request_refs": ["dispatch-request:v75a:self-evidencing:review"],
                "assignment_plan_refs": ["assignment-plan:v75b:self-evidencing:review-only"],
                "reconciliation_plan_refs": ["reconciliation-plan:v75c:self-evidencing:projected"],
                "reconciliation_contract_refs": [
                    "contract:v75c:dispatch-reconciliation:review-only"
                ],
                "handoff_target": "future_outcome_review",
                "handoff_subject_horizon": "dispatch_review_process_outcome",
                "handoff_posture": "ready_for_later_review",
                "carried_exception_refs": ["dispatch-exception:v75b:self-evidencing:upstream"],
                "required_later_authority_refs": [
                    "authority:v75a:self-evidencing:dispatch-execution",
                    "authority:v75a:self-evidencing:human-review",
                ],
                "non_execution_guardrail": (
                    "Handoff is review-only with no dispatch, no command, no runtime, "
                    "no product authorization, and no release."
                ),
                "limitation_note": (
                    "Future outcome review is for the dispatch review process with no dispatch."
                ),
            },
        ],
        "handoff_summary": (
            "Post-dispatch-review handoff means review after dispatch review: "
            "no dispatch, no runtime permission, and no release."
        ),
    }
    payload["handoff_rows"] = sorted(payload["handoff_rows"], key=lambda row: row["handoff_ref"])
    payload["post_dispatch_review_handoff_id"] = _surface_id(
        "repo_post_dispatch_review_handoff",
        REPO_POST_DISPATCH_REVIEW_HANDOFF_SCHEMA,
        payload,
        "post_dispatch_review_handoff_id",
    )
    return RepoPostDispatchReviewHandoff.model_validate(payload)


def derive_v75c_repo_dispatch_review_family_closeout_alignment(
    *,
    repo_root: Path | None = None,
) -> RepoDispatchReviewFamilyCloseoutAlignment:
    _ = repo_root
    payload = {
        "schema": REPO_DISPATCH_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
        "dispatch_review_family_closeout_alignment_id": "",
        "family": "V75",
        "closed_by_arc": "vNext+211",
        "review_id": "review:v75c:reconciliation-contract-handoff-closeout",
        "snapshot_id": "vNext+210-closed-on-main",
        "source_set_id": "source-set:v75c:released-v75a-v75b-dispatch-review",
        "closed_slice_ladder": ["V75-A", "V75-B", "V75-C"],
        "shipped_record_shapes": sorted(
            [
                REPO_DISPATCH_REVIEW_REQUEST_SCHEMA,
                REPO_DISPATCH_SOURCE_INDEX_SCHEMA,
                REPO_DISPATCH_NON_EXECUTION_GUARDRAIL_SCHEMA,
                REPO_WORKER_ROLE_CAPACITY_PROFILE_SCHEMA,
                REPO_MULTI_WORKER_ASSIGNMENT_PLAN_SCHEMA,
                REPO_WORKER_IO_CONTRACT_SCHEMA,
                REPO_WORKER_TOOL_APPLICABILITY_MATRIX_SCHEMA,
                REPO_DISPATCH_EXCEPTION_REGISTER_SCHEMA,
                REPO_WORKER_OUTPUT_RECONCILIATION_PLAN_SCHEMA,
                REPO_DISPATCH_RECONCILIATION_CONTRACT_SCHEMA,
                REPO_POST_DISPATCH_REVIEW_HANDOFF_SCHEMA,
                REPO_DISPATCH_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            ]
        ),
        "consumed_source_families": sorted(
            [
                "V68",
                "V69",
                "V70",
                "V71",
                "V72",
                "V73",
                "V74",
                "V75-A",
                "V75-B",
            ]
        ),
        "future_family_authority": sorted(
            [
                "future_runtime_permission_review",
                "future_product_review",
                "future_external_branch_review",
                "future_reconciliation_or_arbiter_review",
                "future_experiment_review",
            ]
        ),
        "unselected_future_surfaces": [
            "dispatch_execution",
            "external_contest_participation",
            "model_selection",
            "product_authorization",
            "recursive_policy_amendment",
            "release_authority",
            "runtime_permission",
            "worker_assignment",
        ],
        "dispatch_review_authority_boundary": (
            "V75 closes as dispatch review posture with no dispatch, no runtime permission, "
            "no product authorization, and no release."
        ),
        "limitation_note": (
            "Family closeout alignment records dispatch review only; no dispatch execution, "
            "no command, no product launch, no release, no model selection, and no policy "
            "amendment."
        ),
    }
    payload["dispatch_review_family_closeout_alignment_id"] = _surface_id(
        "repo_dispatch_review_family_closeout_alignment",
        REPO_DISPATCH_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
        payload,
        "dispatch_review_family_closeout_alignment_id",
    )
    return RepoDispatchReviewFamilyCloseoutAlignment.model_validate(payload)


def validate_v75c_dispatch_review_closeout_bundle(
    *,
    dispatch_source_index: RepoDispatchSourceIndex,
    dispatch_review_request: RepoDispatchReviewRequest,
    dispatch_non_execution_guardrail: RepoDispatchNonExecutionGuardrail,
    worker_role_capacity_profile: RepoWorkerRoleCapacityProfile,
    multi_worker_assignment_plan: RepoMultiWorkerAssignmentPlan,
    worker_io_contract: RepoWorkerIOContract,
    worker_tool_applicability_matrix: RepoWorkerToolApplicabilityMatrix,
    dispatch_exception_register: RepoDispatchExceptionRegister,
    worker_output_reconciliation_plan: RepoWorkerOutputReconciliationPlan,
    dispatch_reconciliation_contract: RepoDispatchReconciliationContract,
    post_dispatch_review_handoff: RepoPostDispatchReviewHandoff,
    dispatch_review_family_closeout_alignment: RepoDispatchReviewFamilyCloseoutAlignment,
) -> None:
    validate_v75b_worker_orchestration_bundle(
        dispatch_source_index=dispatch_source_index,
        dispatch_review_request=dispatch_review_request,
        dispatch_non_execution_guardrail=dispatch_non_execution_guardrail,
        worker_role_capacity_profile=worker_role_capacity_profile,
        multi_worker_assignment_plan=multi_worker_assignment_plan,
        worker_io_contract=worker_io_contract,
        worker_tool_applicability_matrix=worker_tool_applicability_matrix,
        dispatch_exception_register=dispatch_exception_register,
    )
    surfaces = [
        worker_output_reconciliation_plan,
        dispatch_reconciliation_contract,
        post_dispatch_review_handoff,
        dispatch_review_family_closeout_alignment,
    ]
    for surface in surfaces:
        if (
            surface.review_id,
            surface.snapshot_id,
            surface.source_set_id,
        ) != (
            "review:v75c:reconciliation-contract-handoff-closeout",
            "vNext+210-closed-on-main",
            "source-set:v75c:released-v75a-v75b-dispatch-review",
        ):
            raise ValueError("V75-C surfaces must share reconciliation closeout provenance")

    if (
        worker_output_reconciliation_plan.dispatch_review_request_id
        != dispatch_review_request.dispatch_review_request_id
    ):
        raise ValueError("reconciliation plan must reference released V75-A request surface")
    if (
        worker_output_reconciliation_plan.multi_worker_assignment_plan_id
        != multi_worker_assignment_plan.multi_worker_assignment_plan_id
    ):
        raise ValueError("reconciliation plan must reference released V75-B assignment plan")
    if (
        worker_output_reconciliation_plan.worker_io_contract_id
        != worker_io_contract.worker_io_contract_id
    ):
        raise ValueError("reconciliation plan must reference released V75-B IO contract")
    if (
        worker_output_reconciliation_plan.dispatch_exception_register_id
        != dispatch_exception_register.dispatch_exception_register_id
    ):
        raise ValueError("reconciliation plan must reference released V75-B exception register")
    if (
        dispatch_reconciliation_contract.worker_output_reconciliation_plan_id
        != worker_output_reconciliation_plan.worker_output_reconciliation_plan_id
    ):
        raise ValueError("reconciliation contract must reference the reconciliation plan")
    if (
        post_dispatch_review_handoff.worker_output_reconciliation_plan_id
        != worker_output_reconciliation_plan.worker_output_reconciliation_plan_id
    ):
        raise ValueError("post-dispatch handoff must reference the reconciliation plan")
    if (
        post_dispatch_review_handoff.dispatch_reconciliation_contract_id
        != dispatch_reconciliation_contract.dispatch_reconciliation_contract_id
    ):
        raise ValueError("post-dispatch handoff must reference reconciliation contract")

    request_rows = {row.dispatch_request_ref: row for row in dispatch_review_request.request_rows}
    assignment_rows = {
        row.assignment_plan_ref: row for row in multi_worker_assignment_plan.assignment_plan_rows
    }
    io_rows = {row.io_contract_ref: row for row in worker_io_contract.io_contract_rows}
    exception_rows = {
        row.dispatch_exception_ref: row for row in dispatch_exception_register.exception_rows
    }
    slot_rows = {
        row.projected_output_slot_ref: row
        for row in worker_output_reconciliation_plan.projected_output_slot_rows
    }
    relation_rows = {
        row.relation_ref: row for row in worker_output_reconciliation_plan.relation_rows
    }
    plan_rows = {
        row.reconciliation_plan_ref: row
        for row in worker_output_reconciliation_plan.reconciliation_plan_rows
    }
    contract_rows = {
        row.contract_ref: row for row in dispatch_reconciliation_contract.contract_rows
    }
    handoff_rows = {row.handoff_ref: row for row in post_dispatch_review_handoff.handoff_rows}

    for slot_row in worker_output_reconciliation_plan.projected_output_slot_rows:
        if any(ref not in assignment_rows for ref in slot_row.assignment_plan_refs):
            raise ValueError("projected output slots must reference known assignment rows")
        if any(ref not in io_rows for ref in slot_row.io_contract_refs):
            raise ValueError("projected output slots must reference known IO rows")

    for relation_row in worker_output_reconciliation_plan.relation_rows:
        if relation_row.left_output_ref not in slot_rows:
            raise ValueError("relation rows must reference known projected output refs")
        if relation_row.right_output_ref not in slot_rows:
            raise ValueError("relation rows must reference known projected output refs")

    for plan_row in worker_output_reconciliation_plan.reconciliation_plan_rows:
        if any(ref not in request_rows for ref in plan_row.dispatch_request_refs):
            raise ValueError("reconciliation plans must reference released V75-A requests")
        if any(ref not in assignment_rows for ref in plan_row.assignment_plan_refs):
            raise ValueError("reconciliation plans must reference released V75-B assignments")
        if any(ref not in io_rows for ref in plan_row.io_contract_refs):
            raise ValueError("reconciliation plans must reference released V75-B IO contracts")
        if any(ref not in slot_rows for ref in plan_row.projected_output_slot_refs):
            raise ValueError("reconciliation plans must reference known projected output slots")
        if any(ref not in relation_rows for ref in plan_row.relation_refs):
            raise ValueError("reconciliation plans must reference known relation rows")
        plan_output_refs = set(plan_row.projected_output_slot_refs) | set(
            plan_row.observed_worker_output_refs
        )
        for relation_ref in plan_row.relation_refs:
            relation_row = relation_rows[relation_ref]
            if (
                relation_row.left_output_ref not in plan_output_refs
                or relation_row.right_output_ref not in plan_output_refs
            ):
                raise ValueError(
                    "reconciliation plan relations must be scoped to that plan's outputs"
                )
        if any(ref not in exception_rows for ref in plan_row.exception_refs):
            raise ValueError("reconciliation plans must reference known dispatch exceptions")
        if any(
            exception_rows[ref].blocking_posture == "blocking" for ref in plan_row.exception_refs
        ):
            if plan_row.output_presence_posture != "projected_not_observed":
                raise ValueError("blocking exceptions must remain projected and not observed")

    for contract_row in dispatch_reconciliation_contract.contract_rows:
        if any(ref not in plan_rows for ref in contract_row.reconciliation_plan_refs):
            raise ValueError("reconciliation contracts must reference known reconciliation plans")
        if any(ref not in handoff_rows for ref in contract_row.handoff_refs):
            raise ValueError("reconciliation contracts must reference known handoff rows")

    for handoff_row in post_dispatch_review_handoff.handoff_rows:
        if any(ref not in request_rows for ref in handoff_row.dispatch_request_refs):
            raise ValueError("post-dispatch handoffs must reference released V75-A requests")
        if any(ref not in assignment_rows for ref in handoff_row.assignment_plan_refs):
            raise ValueError("post-dispatch handoffs must reference released V75-B assignments")
        if any(ref not in plan_rows for ref in handoff_row.reconciliation_plan_refs):
            raise ValueError("post-dispatch handoffs must reference reconciliation plans")
        if any(ref not in contract_rows for ref in handoff_row.reconciliation_contract_refs):
            raise ValueError("post-dispatch handoffs must reference reconciliation contracts")
        if any(ref not in exception_rows for ref in handoff_row.carried_exception_refs):
            raise ValueError("post-dispatch handoffs must carry known dispatch exceptions")
        has_blocking_exception = any(
            exception_rows[ref].blocking_posture == "blocking"
            for ref in handoff_row.carried_exception_refs
        )
        if has_blocking_exception and handoff_row.handoff_posture == "ready_for_later_review":
            if handoff_row.handoff_target != "future_reconciliation_or_arbiter_review":
                raise ValueError("blocking exceptions prevent ready handoff outside arbiter review")
            if "settlement" not in handoff_row.limitation_note.lower():
                raise ValueError("blocking ready arbiter handoff must carry blocker for settlement")


def derive_v75c_dispatch_review_closeout_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoWorkerOutputReconciliationPlan,
    RepoDispatchReconciliationContract,
    RepoPostDispatchReviewHandoff,
    RepoDispatchReviewFamilyCloseoutAlignment,
]:
    source_index, request, guardrail = derive_v75a_dispatch_review_bundle(repo_root=repo_root)
    role_profile, assignment_plan, io_contract, tool_matrix, exception_register = (
        derive_v75b_worker_orchestration_bundle(repo_root=repo_root)
    )
    reconciliation_plan = derive_v75c_repo_worker_output_reconciliation_plan(
        repo_root=repo_root,
        dispatch_review_request=request,
        multi_worker_assignment_plan=assignment_plan,
        worker_io_contract=io_contract,
        dispatch_exception_register=exception_register,
    )
    contract = derive_v75c_repo_dispatch_reconciliation_contract(
        repo_root=repo_root,
        worker_output_reconciliation_plan=reconciliation_plan,
    )
    handoff = derive_v75c_repo_post_dispatch_review_handoff(
        repo_root=repo_root,
        worker_output_reconciliation_plan=reconciliation_plan,
        dispatch_reconciliation_contract=contract,
    )
    family_closeout = derive_v75c_repo_dispatch_review_family_closeout_alignment(
        repo_root=repo_root
    )
    validate_v75c_dispatch_review_closeout_bundle(
        dispatch_source_index=source_index,
        dispatch_review_request=request,
        dispatch_non_execution_guardrail=guardrail,
        worker_role_capacity_profile=role_profile,
        multi_worker_assignment_plan=assignment_plan,
        worker_io_contract=io_contract,
        worker_tool_applicability_matrix=tool_matrix,
        dispatch_exception_register=exception_register,
        worker_output_reconciliation_plan=reconciliation_plan,
        dispatch_reconciliation_contract=contract,
        post_dispatch_review_handoff=handoff,
        dispatch_review_family_closeout_alignment=family_closeout,
    )
    return reconciliation_plan, contract, handoff, family_closeout
