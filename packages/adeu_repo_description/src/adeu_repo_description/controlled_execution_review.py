from __future__ import annotations

import re
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

REPO_CONTROLLED_EXECUTION_REVIEW_REQUEST_SCHEMA = (
    "repo_controlled_execution_review_request@1"
)
REPO_CONTROLLED_EXECUTION_SOURCE_INDEX_SCHEMA = "repo_controlled_execution_source_index@1"
REPO_CONTROLLED_EXECUTION_NON_EXECUTION_GUARDRAIL_SCHEMA = (
    "repo_controlled_execution_non_execution_guardrail@1"
)
REPO_EXECUTION_RUN_PLAN_SCHEMA = "repo_execution_run_plan@1"
REPO_TOOL_INVOCATION_PLAN_SCHEMA = "repo_tool_invocation_plan@1"
REPO_EXECUTION_EFFECT_MONITORING_CONTRACT_SCHEMA = (
    "repo_execution_effect_monitoring_contract@1"
)
REPO_CONTROLLED_EXECUTION_EXCEPTION_REGISTER_SCHEMA = (
    "repo_controlled_execution_exception_register@1"
)

ControlledExecutionSourceRole = Literal[
    "v78_readiness_summary_source",
    "v78_pre_execution_authority_review_handoff_source",
    "v78_family_closeout_source",
    "v78_authority_decision_context",
    "v78_tool_permission_context",
    "v78_command_scope_context",
    "v78_exception_context",
    "combined_dogfood_context",
    "support_process_context",
    "absence_marker",
]
ControlledExecutionReviewPosture = Literal[
    "eligible_for_controlled_execution_review",
    "blocked_by_missing_source",
    "blocked_by_missing_authority",
    "blocked_by_product_authority_gap",
    "blocked_by_external_branch_gap",
    "blocked_by_unbounded_target",
    "blocked_by_missing_effect_monitoring",
    "blocked_by_missing_telemetry",
    "blocked_by_missing_rollback",
    "future_family_only",
    "rejected_out_of_scope",
]
RequestedExecutionReviewHorizon = Literal[
    "bounded_command_run_plan_review",
    "bounded_tool_invocation_plan_review",
    "bounded_repo_script_run_plan_review",
    "future_product_review",
    "future_external_branch_review",
    "future_family_review",
]
RequestedRunPlanHorizon = Literal[
    "bounded_run_plan_required_later",
    "run_plan_not_selected_in_v79a",
    "run_plan_blocked_by_missing_source",
    "run_plan_blocked_by_missing_authority",
    "future_family_only",
]
RequestedToolInvocationHorizon = Literal[
    "bounded_tool_invocation_plan_required_later",
    "tool_invocation_plan_not_selected_in_v79a",
    "tool_invocation_plan_blocked_by_missing_source",
    "tool_invocation_plan_blocked_by_missing_authority",
    "future_family_only",
]
ControlledExecutionRequirementPosture = Literal[
    "required_for_later_review",
    "not_selected_in_v79a",
    "not_applicable",
    "blocked_by_missing_source",
    "blocked_by_missing_authority",
    "future_family_only",
]
ControlledExecutionActionPosture = Literal[
    "no_controlled_execution_performed_by_v79",
    "controlled_execution_requires_later_family",
    "controlled_execution_forbidden_by_this_family",
]
ControlledExecutionExecutionPosture = Literal[
    "no_execution_performed_by_v79",
    "execution_requires_later_family",
    "execution_forbidden_by_this_family",
]
ControlledExecutionToolInvocationPosture = Literal[
    "no_tool_invocation_performed_by_v79",
    "tool_invocation_requires_later_family",
    "tool_invocation_forbidden_by_this_family",
]
ControlledExecutionForbiddenAction = Literal[
    "run_command",
    "invoke_tool_for_effect",
    "mutate_target",
    "accept_effect",
    "observe_telemetry_as_success",
    "verify_rollback",
    "assign_worker",
    "dispatch_worker",
    "open_pr",
    "commit",
    "merge",
    "release",
    "external_submission",
]
ControlledExecutionForbiddenDownstreamAuthority = Literal[
    "product_authorization",
    "external_branch_activation",
    "released_truth",
    "benchmark_truth",
    "model_selection",
    "living_memory_authority",
    "recursive_policy_amendment",
    "v80_selection",
]
ExecutionRunPlanPosture = Literal[
    "run_plan_complete_for_review_only",
    "run_plan_incomplete_for_review",
    "blocked_by_missing_source",
    "blocked_by_missing_authority",
    "blocked_by_missing_target_boundary",
    "blocked_by_missing_monitoring",
    "blocked_by_missing_rollback",
    "future_family_only",
]
ExecutionPlanCompletenessPosture = Literal[
    "incomplete_for_review",
    "complete_for_review_only",
    "blocked_by_missing_source",
    "blocked_by_missing_authority",
    "blocked_by_missing_target_boundary",
    "blocked_by_missing_monitoring",
    "blocked_by_missing_rollback",
    "future_family_only",
]
ExecutionRunStatus = Literal[
    "no_run_performed_by_v79",
    "run_requires_later_family",
    "run_forbidden_by_this_family",
]
ExecutionTargetResolutionKind = Literal[
    "concrete_file_ref",
    "concrete_schema_ref",
    "concrete_fixture_ref",
    "concrete_test_ref",
    "concrete_doc_ref",
    "concrete_script_ref",
    "bounded_package_surface_with_child_refs",
    "external_endpoint_ref",
    "no_target_boundary",
]
ToolInvocationPlanPosture = Literal[
    "tool_invocation_plan_complete_for_review_only",
    "tool_invocation_plan_incomplete_for_review",
    "blocked_by_missing_source",
    "blocked_by_missing_authority",
    "blocked_by_missing_target_boundary",
    "blocked_by_missing_monitoring",
    "future_family_only",
]
ToolInvocationStatus = Literal[
    "no_tool_invocation_performed_by_v79",
    "invocation_requires_later_family",
    "invocation_forbidden_by_this_family",
]
ExecutionMonitoringPosture = Literal[
    "monitoring_contract_complete_for_review_only",
    "monitoring_contract_incomplete_for_review",
    "blocked_by_missing_telemetry",
    "blocked_by_missing_rollback",
    "future_family_only",
]
EffectObservationPosture = Literal[
    "no_effect_observed_by_v79",
    "effect_requires_later_review",
    "effect_observed_from_prior_authorized_source",
    "effect_not_applicable",
]
OperatorConfirmationKind = Literal[
    "maintainer_confirmation_required",
    "operator_acknowledgement_required",
    "product_authority_confirmation_required",
    "external_branch_authority_confirmation_required",
]
OperatorConfirmationPosture = Literal[
    "confirmation_required_for_later_review",
    "confirmation_not_authorization",
    "blocked_by_missing_authority",
    "future_family_only",
]
ControlledExecutionExceptionKind = Literal[
    "missing_source",
    "unknown_v79a_request",
    "missing_authority",
    "missing_target_boundary",
    "unbounded_target",
    "missing_monitoring_contract",
    "missing_telemetry_requirement",
    "missing_rollback_requirement",
    "operator_confirmation_authorization_gap",
    "product_authority_gap",
    "external_branch_authority_gap",
    "local_command_output_as_authority",
    "unknown_needs_review",
]
ControlledExecutionExceptionPosture = Literal[
    "blocking",
    "warning_only",
    "carried_forward",
    "not_applicable",
    "future_family_only",
]
ControlledExecutionRequiredNextSurface = Literal[
    "v79c_summary_review",
    "future_product_review",
    "future_external_branch_review",
    "future_family_review",
    "none",
]

_ELIGIBILITY_SOURCE_ROLES = {
    "v78_readiness_summary_source",
    "v78_pre_execution_authority_review_handoff_source",
}
_CONTEXT_SOURCE_ROLES = {
    "v78_authority_decision_context",
    "v78_tool_permission_context",
    "v78_command_scope_context",
    "v78_exception_context",
    "combined_dogfood_context",
    "support_process_context",
}
_FORBIDDEN_EXECUTION_ACTIONS = {
    "run_command",
    "invoke_tool_for_effect",
    "mutate_target",
    "accept_effect",
    "observe_telemetry_as_success",
    "verify_rollback",
    "assign_worker",
    "dispatch_worker",
    "open_pr",
    "commit",
    "merge",
    "release",
    "external_submission",
}
_FORBIDDEN_DOWNSTREAM_AUTHORITIES = {
    "product_authorization",
    "external_branch_activation",
    "released_truth",
    "benchmark_truth",
    "model_selection",
    "living_memory_authority",
    "recursive_policy_amendment",
    "v80_selection",
}


def _reject_v79_action_claim(value: str, *, field_name: str) -> str:
    lowered = value.lower()
    forbidden_patterns = [
        r"controlled execution (?:is |was |has been |gets |got )?performed",
        r"command (?:is |was |has been |gets |got )?executed",
        r"run command",
        r"tool (?:is |was |has been |gets |got )?invoked",
        r"invoke tool",
        r"target (?:is |was |has been |gets |got )?mutated",
        r"effect (?:is |was |has been |gets |got )?accepted",
        r"telemetry (?:is |was |has been |gets |got )?observed",
        r"rollback (?:is |was |has been |gets |got )?verified",
        r"assign worker",
        r"dispatch worker",
        r"open pr",
        r"commit now",
        r"merge now",
        r"release now",
        r"product (?:is |was |has been |gets |got )?authorized",
        r"external branch (?:is |was |has been |gets |got )?activated",
        r"benchmark truth",
        r"model (?:is |was |has been |gets |got )?selected",
        r"v80 (?:is |was |has been |gets |got )?selected",
    ]
    negation_markers = ("no ", "not ", "without ", "forbidden ", "non-")
    for pattern in forbidden_patterns:
        match = re.search(pattern, lowered)
        if match is None:
            continue
        prefix = lowered[max(0, match.start() - 24) : match.start()]
        if not any(marker in prefix for marker in negation_markers):
            raise ValueError(f"{field_name} may not carry controlled execution action")
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


def _reject_glob_ref(value: str, *, field_name: str) -> str:
    if any(marker in value for marker in ("*", "?", "[")):
        raise ValueError(f"{field_name} may not contain glob target boundaries")
    return value


class RepoControlledExecutionSourceRow(_CartographyBase):
    source_ref: str
    source_kind: CandidateSourceKind
    authority_layer: CandidateAuthorityLayer
    source_status: SourceStatus
    source_presence_posture: CandidateSourcePresencePosture
    controlled_execution_source_role: ControlledExecutionSourceRole
    source_horizon: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_controlled_execution_source_row(self) -> RepoControlledExecutionSourceRow:
        _repo_ref(self.source_ref, field_name="source_ref")
        _non_empty(self.source_horizon, field_name="source_horizon")
        _reject_v79_action_claim(self.limitation_note, field_name="limitation_note")
        if (
            self.controlled_execution_source_role != "absence_marker"
            and self.source_presence_posture != "present"
        ):
            raise ValueError("non-absence controlled execution source rows must be present")
        if (
            self.controlled_execution_source_role == "absence_marker"
            and self.source_presence_posture == "present"
        ):
            raise ValueError("absence-marker controlled execution rows must not be present sources")
        if (
            self.controlled_execution_source_role in _CONTEXT_SOURCE_ROLES
            and self.authority_layer == "lock"
            and self.source_kind == "support_doc"
        ):
            raise ValueError("support context may not be marked as lock authority")
        return self


class RepoControlledExecutionSourceIndex(_CartographyBase):
    schema: Literal["repo_controlled_execution_source_index@1"] = (
        REPO_CONTROLLED_EXECUTION_SOURCE_INDEX_SCHEMA
    )
    controlled_execution_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    source_rows: list[RepoControlledExecutionSourceRow] = Field(min_length=1)
    controlled_execution_source_summary: str

    @model_validator(mode="after")
    def _validate_controlled_execution_source_index(self) -> RepoControlledExecutionSourceIndex:
        object.__setattr__(
            self,
            "source_rows",
            _sorted_unique_by_ref(self.source_rows, attr="source_ref", field_name="source_rows"),
        )
        _non_empty(self.review_id, field_name="review_id")
        _non_empty(self.snapshot_id, field_name="snapshot_id")
        _non_empty(self.source_set_id, field_name="source_set_id")
        _require_terms(
            self.controlled_execution_source_summary,
            field_name="controlled_execution_source_summary",
            terms=("eligibility", "context", "no execution"),
        )
        expected_id = _surface_id(
            "repo_controlled_execution_source_index",
            self.schema,
            self.model_dump(mode="json"),
            "controlled_execution_source_index_id",
        )
        if self.controlled_execution_source_index_id != expected_id:
            raise ValueError("controlled_execution_source_index_id does not match canonical hash")
        return self


class RepoControlledExecutionReviewRequestRow(_CartographyBase):
    execution_review_request_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    v78_summary_refs: list[str] = Field(default_factory=list)
    v78_handoff_refs: list[str] = Field(default_factory=list)
    v78_closeout_refs: list[str] = Field(default_factory=list)
    requested_execution_review_horizon: RequestedExecutionReviewHorizon
    execution_review_posture: ControlledExecutionReviewPosture
    requested_run_plan_horizon: RequestedRunPlanHorizon
    requested_tool_invocation_horizon: RequestedToolInvocationHorizon
    required_effect_monitoring_posture: ControlledExecutionRequirementPosture
    required_telemetry_posture: ControlledExecutionRequirementPosture
    required_rollback_posture: ControlledExecutionRequirementPosture
    required_operator_confirmation_posture: ControlledExecutionRequirementPosture
    required_authority_refs: list[str] = Field(default_factory=list)
    target_boundary_refs: list[str] = Field(default_factory=list)
    guardrail_refs: list[str] = Field(min_length=1)
    controlled_execution_action_posture: ControlledExecutionActionPosture
    execution_posture: ControlledExecutionExecutionPosture
    tool_invocation_posture: ControlledExecutionToolInvocationPosture
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_controlled_execution_review_request_row(
        self,
    ) -> RepoControlledExecutionReviewRequestRow:
        _non_empty(self.execution_review_request_ref, field_name="execution_review_request_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "v78_summary_refs",
            "v78_handoff_refs",
            "v78_closeout_refs",
            "required_authority_refs",
            "target_boundary_refs",
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
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        for target_ref in self.target_boundary_refs:
            _reject_glob_ref(target_ref, field_name="target_boundary_refs")
            _repo_ref(target_ref, field_name="target_boundary_refs")
        if self.controlled_execution_action_posture != "no_controlled_execution_performed_by_v79":
            raise ValueError("V79-A request rows must not perform controlled execution")
        if self.execution_posture != "no_execution_performed_by_v79":
            raise ValueError("V79-A request rows must not perform execution")
        if self.tool_invocation_posture != "no_tool_invocation_performed_by_v79":
            raise ValueError("V79-A request rows must not invoke tools")
        _reject_v79_action_claim(self.limitation_note, field_name="limitation_note")
        if self.execution_review_posture == "eligible_for_controlled_execution_review":
            if self.requested_execution_review_horizon in {
                "future_product_review",
                "future_external_branch_review",
            }:
                raise ValueError("product/external pressure is not execution-review-ready")
            if not self.v78_summary_refs and not self.v78_handoff_refs:
                raise ValueError("eligible execution review requests require V78-C refs")
            if not self.required_authority_refs:
                raise ValueError("eligible execution review requests require authority refs")
            for field_name in (
                "required_effect_monitoring_posture",
                "required_telemetry_posture",
                "required_rollback_posture",
                "required_operator_confirmation_posture",
            ):
                if getattr(self, field_name) != "required_for_later_review":
                    raise ValueError("eligible execution review requests require later safeguards")
        if self.requested_execution_review_horizon == "future_product_review":
            if self.execution_review_posture not in {
                "blocked_by_product_authority_gap",
                "future_family_only",
                "rejected_out_of_scope",
            }:
                raise ValueError("product pressure must remain product-blocked in V79-A")
            if not any("product" in ref for ref in self.required_authority_refs):
                raise ValueError("product pressure requires product authority blocker")
        if self.requested_execution_review_horizon == "future_external_branch_review":
            if self.execution_review_posture not in {
                "blocked_by_external_branch_gap",
                "future_family_only",
                "rejected_out_of_scope",
            }:
                raise ValueError("external branch pressure must remain blocked in V79-A")
            has_external_authority = any(
                "external" in ref or "v43" in ref.lower()
                for ref in self.required_authority_refs
            )
            if not has_external_authority:
                raise ValueError("external branch pressure requires external authority blocker")
        return self


class RepoControlledExecutionReviewRequest(_CartographyBase):
    schema: Literal["repo_controlled_execution_review_request@1"] = (
        REPO_CONTROLLED_EXECUTION_REVIEW_REQUEST_SCHEMA
    )
    controlled_execution_review_request_id: str
    controlled_execution_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    request_rows: list[RepoControlledExecutionReviewRequestRow] = Field(min_length=1)
    controlled_execution_boundary_summary: str

    @model_validator(mode="after")
    def _validate_controlled_execution_review_request(
        self,
    ) -> RepoControlledExecutionReviewRequest:
        object.__setattr__(
            self,
            "request_rows",
            _sorted_unique_by_ref(
                self.request_rows,
                attr="execution_review_request_ref",
                field_name="request_rows",
            ),
        )
        _require_terms(
            self.controlled_execution_boundary_summary,
            field_name="controlled_execution_boundary_summary",
            terms=("review", "no execution", "no tool invocation", "no release"),
        )
        expected_id = _surface_id(
            "repo_controlled_execution_review_request",
            self.schema,
            self.model_dump(mode="json"),
            "controlled_execution_review_request_id",
        )
        if self.controlled_execution_review_request_id != expected_id:
            raise ValueError(
                "controlled_execution_review_request_id does not match canonical hash"
            )
        return self


class RepoControlledExecutionNonExecutionGuardrailRow(_CartographyBase):
    guardrail_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    execution_review_request_refs: list[str] = Field(min_length=1)
    forbidden_execution_actions: list[ControlledExecutionForbiddenAction] = Field(min_length=1)
    forbidden_downstream_authority: list[ControlledExecutionForbiddenDownstreamAuthority] = Field(
        min_length=1
    )
    guardrail_posture: Literal["non_execution_guardrail_active"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_controlled_execution_guardrail_row(
        self,
    ) -> RepoControlledExecutionNonExecutionGuardrailRow:
        _non_empty(self.guardrail_ref, field_name="guardrail_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "execution_review_request_refs",
            "forbidden_execution_actions",
            "forbidden_downstream_authority",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        missing_actions = _FORBIDDEN_EXECUTION_ACTIONS.difference(
            self.forbidden_execution_actions
        )
        if missing_actions:
            raise ValueError("controlled execution guardrail omits forbidden execution actions")
        missing_authority = _FORBIDDEN_DOWNSTREAM_AUTHORITIES.difference(
            self.forbidden_downstream_authority
        )
        if missing_authority:
            raise ValueError("controlled execution guardrail omits forbidden downstream authority")
        _reject_v79_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("no controlled execution", "no execution", "no tool invocation", "no release"),
        )
        return self


class RepoControlledExecutionNonExecutionGuardrail(_CartographyBase):
    schema: Literal["repo_controlled_execution_non_execution_guardrail@1"] = (
        REPO_CONTROLLED_EXECUTION_NON_EXECUTION_GUARDRAIL_SCHEMA
    )
    controlled_execution_non_execution_guardrail_id: str
    controlled_execution_review_request_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    guardrail_rows: list[RepoControlledExecutionNonExecutionGuardrailRow] = Field(min_length=1)
    non_execution_summary: str

    @model_validator(mode="after")
    def _validate_controlled_execution_guardrail(
        self,
    ) -> RepoControlledExecutionNonExecutionGuardrail:
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
            terms=("no controlled execution", "no execution", "no tool invocation", "no release"),
        )
        expected_id = _surface_id(
            "repo_controlled_execution_non_execution_guardrail",
            self.schema,
            self.model_dump(mode="json"),
            "controlled_execution_non_execution_guardrail_id",
        )
        if self.controlled_execution_non_execution_guardrail_id != expected_id:
            raise ValueError(
                "controlled_execution_non_execution_guardrail_id does not match canonical hash"
            )
        return self


class RepoExecutionRunPlanRow(_CartographyBase):
    run_plan_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    execution_review_request_refs: list[str] = Field(min_length=1)
    non_execution_guardrail_refs: list[str] = Field(min_length=1)
    command_intent_kind: RequestedExecutionReviewHorizon
    target_boundary_refs: list[str] = Field(default_factory=list)
    target_resolution_kind: ExecutionTargetResolutionKind
    authority_refs: list[str] = Field(min_length=1)
    tool_invocation_plan_refs: list[str] = Field(default_factory=list)
    effect_monitoring_contract_refs: list[str] = Field(default_factory=list)
    telemetry_requirement_refs: list[str] = Field(min_length=1)
    rollback_requirement_refs: list[str] = Field(min_length=1)
    operator_confirmation_requirement_refs: list[str] = Field(min_length=1)
    exception_refs: list[str] = Field(default_factory=list)
    run_plan_posture: ExecutionRunPlanPosture
    plan_completeness_posture: ExecutionPlanCompletenessPosture
    run_execution_status: ExecutionRunStatus
    execution_posture: ControlledExecutionExecutionPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_execution_run_plan_row(self) -> RepoExecutionRunPlanRow:
        _non_empty(self.run_plan_ref, field_name="run_plan_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "execution_review_request_refs",
            "non_execution_guardrail_refs",
            "target_boundary_refs",
            "authority_refs",
            "tool_invocation_plan_refs",
            "effect_monitoring_contract_refs",
            "telemetry_requirement_refs",
            "rollback_requirement_refs",
            "operator_confirmation_requirement_refs",
            "exception_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        for target_ref in self.target_boundary_refs:
            if self.target_resolution_kind == "external_endpoint_ref":
                _non_empty(target_ref, field_name="target_boundary_refs")
                if any(marker in target_ref for marker in ("*", "[")):
                    raise ValueError("target_boundary_refs may not contain glob target boundaries")
            else:
                _reject_glob_ref(target_ref, field_name="target_boundary_refs")
                _repo_ref(target_ref, field_name="target_boundary_refs")
        if self.run_execution_status != "no_run_performed_by_v79":
            raise ValueError("V79-B run plans must not perform runs")
        if self.execution_posture != "no_execution_performed_by_v79":
            raise ValueError("V79-B run plans must not execute commands")
        if self.plan_completeness_posture == "complete_for_review_only" and (
            self.run_plan_posture != "run_plan_complete_for_review_only"
        ):
            raise ValueError("complete run plans must remain complete for review only")
        if self.target_resolution_kind == "bounded_package_surface_with_child_refs":
            if not self.target_boundary_refs:
                raise ValueError("bounded package targets require concrete child refs")
        elif self.target_resolution_kind != "no_target_boundary" and not self.target_boundary_refs:
            raise ValueError("concrete run target boundaries require target refs")
        _reject_v79_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("review only", "no run", "no execution"),
        )
        return self


class RepoExecutionRunPlan(_CartographyBase):
    schema: Literal["repo_execution_run_plan@1"] = REPO_EXECUTION_RUN_PLAN_SCHEMA
    execution_run_plan_id: str
    controlled_execution_review_request_id: str
    controlled_execution_source_index_id: str
    controlled_execution_non_execution_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    run_plan_rows: list[RepoExecutionRunPlanRow] = Field(min_length=1)
    run_plan_summary: str

    @model_validator(mode="after")
    def _validate_execution_run_plan(self) -> RepoExecutionRunPlan:
        object.__setattr__(
            self,
            "run_plan_rows",
            _sorted_unique_by_ref(
                self.run_plan_rows,
                attr="run_plan_ref",
                field_name="run_plan_rows",
            ),
        )
        _require_terms(
            self.run_plan_summary,
            field_name="run_plan_summary",
            terms=("review only", "no run", "no execution", "no tool invocation"),
        )
        expected_id = _surface_id(
            "repo_execution_run_plan",
            self.schema,
            self.model_dump(mode="json"),
            "execution_run_plan_id",
        )
        if self.execution_run_plan_id != expected_id:
            raise ValueError("execution_run_plan_id does not match canonical hash")
        return self


class RepoToolInvocationPlanRow(_CartographyBase):
    tool_invocation_plan_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    execution_review_request_refs: list[str] = Field(min_length=1)
    non_execution_guardrail_refs: list[str] = Field(min_length=1)
    tool_id: str
    tool_target_refs: list[str] = Field(min_length=1)
    tool_target_horizon: str
    permission_refs: list[str] = Field(min_length=1)
    authority_refs: list[str] = Field(min_length=1)
    effect_monitoring_contract_refs: list[str] = Field(default_factory=list)
    exception_refs: list[str] = Field(default_factory=list)
    tool_invocation_plan_posture: ToolInvocationPlanPosture
    plan_completeness_posture: ExecutionPlanCompletenessPosture
    tool_invocation_status: ToolInvocationStatus
    tool_invocation_posture: ControlledExecutionToolInvocationPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_tool_invocation_plan_row(self) -> RepoToolInvocationPlanRow:
        _non_empty(self.tool_invocation_plan_ref, field_name="tool_invocation_plan_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        _non_empty(self.tool_id, field_name="tool_id")
        _non_empty(self.tool_target_horizon, field_name="tool_target_horizon")
        for field_name in (
            "source_refs",
            "execution_review_request_refs",
            "non_execution_guardrail_refs",
            "tool_target_refs",
            "permission_refs",
            "authority_refs",
            "effect_monitoring_contract_refs",
            "exception_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        for target_ref in self.tool_target_refs:
            _reject_glob_ref(target_ref, field_name="tool_target_refs")
            _repo_ref(target_ref, field_name="tool_target_refs")
        if "global" in self.tool_target_horizon.lower():
            raise ValueError("tool-invocation plans may not claim global tool permission")
        if self.tool_invocation_status != "no_tool_invocation_performed_by_v79":
            raise ValueError("V79-B tool plans must not invoke tools")
        if self.tool_invocation_posture != "no_tool_invocation_performed_by_v79":
            raise ValueError("V79-B tool plans must not invoke tools")
        if self.plan_completeness_posture == "complete_for_review_only" and (
            self.tool_invocation_plan_posture
            != "tool_invocation_plan_complete_for_review_only"
        ):
            raise ValueError("complete tool plans must remain complete for review only")
        _reject_v79_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("review only", "no tool invocation", "no execution"),
        )
        return self


class RepoToolInvocationPlan(_CartographyBase):
    schema: Literal["repo_tool_invocation_plan@1"] = REPO_TOOL_INVOCATION_PLAN_SCHEMA
    tool_invocation_plan_id: str
    controlled_execution_review_request_id: str
    controlled_execution_source_index_id: str
    controlled_execution_non_execution_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    tool_invocation_plan_rows: list[RepoToolInvocationPlanRow] = Field(min_length=1)
    tool_invocation_plan_summary: str

    @model_validator(mode="after")
    def _validate_tool_invocation_plan(self) -> RepoToolInvocationPlan:
        object.__setattr__(
            self,
            "tool_invocation_plan_rows",
            _sorted_unique_by_ref(
                self.tool_invocation_plan_rows,
                attr="tool_invocation_plan_ref",
                field_name="tool_invocation_plan_rows",
            ),
        )
        _require_terms(
            self.tool_invocation_plan_summary,
            field_name="tool_invocation_plan_summary",
            terms=("review only", "no tool invocation", "no execution"),
        )
        expected_id = _surface_id(
            "repo_tool_invocation_plan",
            self.schema,
            self.model_dump(mode="json"),
            "tool_invocation_plan_id",
        )
        if self.tool_invocation_plan_id != expected_id:
            raise ValueError("tool_invocation_plan_id does not match canonical hash")
        return self


class RepoOperatorConfirmationRequirementRow(_CartographyBase):
    confirmation_requirement_ref: str
    candidate_ref: str
    required_confirmation_kind: OperatorConfirmationKind
    source_refs: list[str] = Field(min_length=1)
    authority_refs: list[str] = Field(min_length=1)
    confirmation_posture: OperatorConfirmationPosture
    non_authorization_guardrail: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_operator_confirmation_requirement(
        self,
    ) -> RepoOperatorConfirmationRequirementRow:
        _non_empty(self.confirmation_requirement_ref, field_name="confirmation_requirement_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        object.__setattr__(
            self,
            "source_refs",
            _sorted_unique(self.source_refs, field_name="source_refs"),
        )
        object.__setattr__(
            self,
            "authority_refs",
            _sorted_unique(self.authority_refs, field_name="authority_refs"),
        )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        _require_terms(
            self.non_authorization_guardrail,
            field_name="non_authorization_guardrail",
            terms=("not authorization", "no execution", "no tool invocation"),
        )
        _reject_v79_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("requirement", "not authorization"),
        )
        return self


class RepoExecutionEffectMonitoringContractRow(_CartographyBase):
    effect_monitoring_contract_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    run_plan_refs: list[str] = Field(min_length=1)
    tool_invocation_plan_refs: list[str] = Field(min_length=1)
    non_execution_guardrail_refs: list[str] = Field(min_length=1)
    expected_effect_surface_refs: list[str] = Field(min_length=1)
    forbidden_effect_surface_refs: list[str] = Field(min_length=1)
    telemetry_requirement_refs: list[str] = Field(min_length=1)
    rollback_requirement_refs: list[str] = Field(min_length=1)
    operator_confirmation_requirement_refs: list[str] = Field(min_length=1)
    operator_confirmation_requirement_rows: list[RepoOperatorConfirmationRequirementRow] = Field(
        min_length=1
    )
    monitoring_posture: ExecutionMonitoringPosture
    effect_observation_posture: EffectObservationPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_effect_monitoring_contract_row(
        self,
    ) -> RepoExecutionEffectMonitoringContractRow:
        _non_empty(
            self.effect_monitoring_contract_ref,
            field_name="effect_monitoring_contract_ref",
        )
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "run_plan_refs",
            "tool_invocation_plan_refs",
            "non_execution_guardrail_refs",
            "expected_effect_surface_refs",
            "forbidden_effect_surface_refs",
            "telemetry_requirement_refs",
            "rollback_requirement_refs",
            "operator_confirmation_requirement_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "operator_confirmation_requirement_rows",
            _sorted_unique_by_ref(
                self.operator_confirmation_requirement_rows,
                attr="confirmation_requirement_ref",
                field_name="operator_confirmation_requirement_rows",
            ),
        )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        if self.effect_observation_posture == "effect_observed_from_prior_authorized_source":
            if not any("prior-authorized" in source_ref for source_ref in self.source_refs):
                raise ValueError("observed effects require prior authorized source evidence")
        elif self.effect_observation_posture != "no_effect_observed_by_v79":
            raise ValueError("V79-B monitoring contracts must not claim observed effects")
        row_refs = set()
        for row in self.operator_confirmation_requirement_rows:
            if row.candidate_ref != self.candidate_ref:
                raise ValueError("monitoring confirmation rows must match candidate")
            row_refs.add(row.confirmation_requirement_ref)
        if set(self.operator_confirmation_requirement_refs) != row_refs:
            raise ValueError("operator confirmation requirement refs must match embedded rows")
        _reject_v79_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("review only", "no observed effect", "no execution"),
        )
        return self


class RepoExecutionEffectMonitoringContract(_CartographyBase):
    schema: Literal["repo_execution_effect_monitoring_contract@1"] = (
        REPO_EXECUTION_EFFECT_MONITORING_CONTRACT_SCHEMA
    )
    execution_effect_monitoring_contract_id: str
    controlled_execution_review_request_id: str
    controlled_execution_source_index_id: str
    controlled_execution_non_execution_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    effect_monitoring_contract_rows: list[RepoExecutionEffectMonitoringContractRow] = Field(
        min_length=1
    )
    effect_monitoring_summary: str

    @model_validator(mode="after")
    def _validate_effect_monitoring_contract(self) -> RepoExecutionEffectMonitoringContract:
        object.__setattr__(
            self,
            "effect_monitoring_contract_rows",
            _sorted_unique_by_ref(
                self.effect_monitoring_contract_rows,
                attr="effect_monitoring_contract_ref",
                field_name="effect_monitoring_contract_rows",
            ),
        )
        _require_terms(
            self.effect_monitoring_summary,
            field_name="effect_monitoring_summary",
            terms=("review only", "no observed effect", "no execution", "no rollback"),
        )
        expected_id = _surface_id(
            "repo_execution_effect_monitoring_contract",
            self.schema,
            self.model_dump(mode="json"),
            "execution_effect_monitoring_contract_id",
        )
        if self.execution_effect_monitoring_contract_id != expected_id:
            raise ValueError(
                "execution_effect_monitoring_contract_id does not match canonical hash"
            )
        return self


class RepoControlledExecutionExceptionRow(_CartographyBase):
    exception_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    execution_review_request_refs: list[str] = Field(default_factory=list)
    run_plan_refs: list[str] = Field(default_factory=list)
    tool_invocation_plan_refs: list[str] = Field(default_factory=list)
    effect_monitoring_contract_refs: list[str] = Field(default_factory=list)
    exception_kind: ControlledExecutionExceptionKind
    exception_posture: ControlledExecutionExceptionPosture
    blocking_surface_refs: list[str] = Field(default_factory=list)
    required_next_surface: ControlledExecutionRequiredNextSurface
    limitation_note: str

    @model_validator(mode="after")
    def _validate_controlled_execution_exception_row(
        self,
    ) -> RepoControlledExecutionExceptionRow:
        _non_empty(self.exception_ref, field_name="exception_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "execution_review_request_refs",
            "run_plan_refs",
            "tool_invocation_plan_refs",
            "effect_monitoring_contract_refs",
            "blocking_surface_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        if self.exception_posture == "blocking" and not self.blocking_surface_refs:
            raise ValueError("blocking controlled execution exceptions require blockers")
        if self.exception_kind == "local_command_output_as_authority":
            raise ValueError("local command output cannot be authority evidence")
        if self.exception_kind in {"product_authority_gap", "external_branch_authority_gap"}:
            if self.exception_posture not in {"blocking", "future_family_only"}:
                raise ValueError("product/external exceptions must remain blocked or deferred")
        if "resolved" in self.limitation_note.lower():
            raise ValueError("controlled execution exceptions cannot be resolved by prose")
        _reject_v79_action_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoControlledExecutionExceptionRegister(_CartographyBase):
    schema: Literal["repo_controlled_execution_exception_register@1"] = (
        REPO_CONTROLLED_EXECUTION_EXCEPTION_REGISTER_SCHEMA
    )
    controlled_execution_exception_register_id: str
    controlled_execution_review_request_id: str
    controlled_execution_source_index_id: str
    controlled_execution_non_execution_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    exception_rows: list[RepoControlledExecutionExceptionRow] = Field(min_length=1)
    exception_summary: str

    @model_validator(mode="after")
    def _validate_controlled_execution_exception_register(
        self,
    ) -> RepoControlledExecutionExceptionRegister:
        object.__setattr__(
            self,
            "exception_rows",
            _sorted_unique_by_ref(
                self.exception_rows,
                attr="exception_ref",
                field_name="exception_rows",
            ),
        )
        _require_terms(
            self.exception_summary,
            field_name="exception_summary",
            terms=("review only", "blocking", "no execution"),
        )
        expected_id = _surface_id(
            "repo_controlled_execution_exception_register",
            self.schema,
            self.model_dump(mode="json"),
            "controlled_execution_exception_register_id",
        )
        if self.controlled_execution_exception_register_id != expected_id:
            raise ValueError(
                "controlled_execution_exception_register_id does not match canonical hash"
            )
        return self


def derive_v79a_repo_controlled_execution_source_index(
    *, repo_root: Path | None = None
) -> RepoControlledExecutionSourceIndex:
    _ = repo_root
    payload = {
        "schema": REPO_CONTROLLED_EXECUTION_SOURCE_INDEX_SCHEMA,
        "controlled_execution_source_index_id": "",
        "review_id": "review:v79a:controlled-execution-review",
        "snapshot_id": "vNext+220-runtime-authority-closeout",
        "source_set_id": "source-set:v79a:released-v78c-controlled-execution-pressure",
        "source_rows": [
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus220/"
                    "repo_runtime_authority_readiness_summary_v220_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "controlled_execution_source_role": "v78_readiness_summary_source",
                "source_horizon": "Released V78-C runtime authority readiness summary rows.",
                "limitation_note": (
                    "Eligibility source for controlled execution review only; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus220/"
                    "repo_pre_execution_authority_review_handoff_v220_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "controlled_execution_source_role": (
                    "v78_pre_execution_authority_review_handoff_source"
                ),
                "source_horizon": "Released V78-C pre-execution-authority-review handoff rows.",
                "limitation_note": (
                    "Eligibility source for controlled execution review only; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus220/"
                    "repo_runtime_execution_authority_family_closeout_alignment_v220_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "controlled_execution_source_role": "v78_family_closeout_source",
                "source_horizon": "Released V78 family closeout alignment rows.",
                "limitation_note": "Family closeout source for review boundary only; no execution.",
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus219/"
                    "repo_runtime_execution_authority_decision_v219_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "controlled_execution_source_role": "v78_authority_decision_context",
                "source_horizon": "Released V78-B authority decision context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus219/"
                    "repo_tool_use_permission_envelope_v219_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "controlled_execution_source_role": "v78_tool_permission_context",
                "source_horizon": "Released V78-B tool-use permission context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; "
                    "no tool invocation."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus219/"
                    "repo_command_scope_authorization_boundary_v219_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "controlled_execution_source_role": "v78_command_scope_context",
                "source_horizon": "Released V78-B command-scope context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus219/"
                    "repo_runtime_authority_exception_register_v219_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "controlled_execution_source_role": "v78_exception_context",
                "source_horizon": "Released V78-B exception context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "docs/support/arc_series_mapping/"
                    "V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_COMBINED_DOGFOOD_TEST_v0.json"
                ),
                "source_kind": "support_doc",
                "authority_layer": "support",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "controlled_execution_source_role": "combined_dogfood_context",
                "source_horizon": "Combined V68-V78 dogfood context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
            {
                "source_ref": _source_path("docs/LOCKED_CONTINUATION_vNEXT_PLUS221.md"),
                "source_kind": "planning_doc",
                "authority_layer": "lock",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "controlled_execution_source_role": "support_process_context",
                "source_horizon": "Active V79-A starter lock context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
        ],
        "controlled_execution_source_summary": (
            "Controlled execution source rows separate eligibility from context "
            "with no execution and no prose memory."
        ),
    }
    payload["source_rows"] = sorted(payload["source_rows"], key=lambda row: row["source_ref"])
    payload["controlled_execution_source_index_id"] = _surface_id(
        "repo_controlled_execution_source_index",
        REPO_CONTROLLED_EXECUTION_SOURCE_INDEX_SCHEMA,
        payload,
        "controlled_execution_source_index_id",
    )
    return RepoControlledExecutionSourceIndex.model_validate(payload)


def derive_v79a_repo_controlled_execution_review_request(
    *,
    repo_root: Path | None = None,
    controlled_execution_source_index: RepoControlledExecutionSourceIndex | None = None,
) -> RepoControlledExecutionReviewRequest:
    _ = repo_root
    source_index = (
        controlled_execution_source_index or derive_v79a_repo_controlled_execution_source_index()
    )
    source_refs = [row.source_ref for row in source_index.source_rows]
    self_candidate = "candidate:internal:self_evidencing_workflow_type_emergence"
    product_candidate = "candidate:internal:typed_adjudication_product_wedge"
    payload = {
        "schema": REPO_CONTROLLED_EXECUTION_REVIEW_REQUEST_SCHEMA,
        "controlled_execution_review_request_id": "",
        "controlled_execution_source_index_id": (
            source_index.controlled_execution_source_index_id
        ),
        "review_id": source_index.review_id,
        "snapshot_id": source_index.snapshot_id,
        "source_set_id": source_index.source_set_id,
        "request_rows": [
            {
                "execution_review_request_ref": (
                    "execution-review:v79a:self-evidencing:controlled-execution"
                ),
                "candidate_ref": self_candidate,
                "source_refs": sorted(source_refs),
                "v78_summary_refs": [
                    "runtime-authority-summary:v78c:self-evidencing:later-execution-review"
                ],
                "v78_handoff_refs": [
                    "handoff:v78c:self-evidencing:later-execution-review"
                ],
                "v78_closeout_refs": [
                    "repo_runtime_execution_authority_family_closeout_alignment_120526ecd5ba85ec60335490"
                ],
                "requested_execution_review_horizon": "bounded_repo_script_run_plan_review",
                "execution_review_posture": "eligible_for_controlled_execution_review",
                "requested_run_plan_horizon": "bounded_run_plan_required_later",
                "requested_tool_invocation_horizon": (
                    "bounded_tool_invocation_plan_required_later"
                ),
                "required_effect_monitoring_posture": "required_for_later_review",
                "required_telemetry_posture": "required_for_later_review",
                "required_rollback_posture": "required_for_later_review",
                "required_operator_confirmation_posture": "required_for_later_review",
                "required_authority_refs": [
                    "authority:v78a:self-evidencing:runtime-review",
                    "authority:v78a:self-evidencing:tool-use-review",
                ],
                "target_boundary_refs": [
                    "packages/adeu_repo_description/src/adeu_repo_description/"
                    "controlled_execution_review.py"
                ],
                "guardrail_refs": ["guardrail:v79a:self-evidencing:non-execution"],
                "controlled_execution_action_posture": (
                    "no_controlled_execution_performed_by_v79"
                ),
                "execution_posture": "no_execution_performed_by_v79",
                "tool_invocation_posture": "no_tool_invocation_performed_by_v79",
                "odeu_lanes": ["deontic", "epistemic", "utility"],
                "limitation_note": (
                    "Eligible for controlled execution review only with no controlled "
                    "execution, no execution, no tool invocation, and no release."
                ),
            },
            {
                "execution_review_request_ref": "execution-review:v79a:product-wedge:blocked",
                "candidate_ref": product_candidate,
                "source_refs": sorted(source_refs),
                "v78_summary_refs": [
                    "runtime-authority-summary:v78c:product-wedge:future-family-only"
                ],
                "v78_handoff_refs": ["handoff:v78c:product-wedge:future-family-only"],
                "v78_closeout_refs": [
                    "repo_runtime_execution_authority_family_closeout_alignment_120526ecd5ba85ec60335490"
                ],
                "requested_execution_review_horizon": "future_product_review",
                "execution_review_posture": "blocked_by_product_authority_gap",
                "requested_run_plan_horizon": "future_family_only",
                "requested_tool_invocation_horizon": "future_family_only",
                "required_effect_monitoring_posture": "not_applicable",
                "required_telemetry_posture": "not_applicable",
                "required_rollback_posture": "not_applicable",
                "required_operator_confirmation_posture": "future_family_only",
                "required_authority_refs": ["authority:v78a:product-wedge:product-review"],
                "target_boundary_refs": [],
                "guardrail_refs": ["guardrail:v79a:product-wedge:non-execution"],
                "controlled_execution_action_posture": (
                    "no_controlled_execution_performed_by_v79"
                ),
                "execution_posture": "no_execution_performed_by_v79",
                "tool_invocation_posture": "no_tool_invocation_performed_by_v79",
                "odeu_lanes": ["deontic", "utility"],
                "limitation_note": (
                    "Product pressure remains blocked by later product authority with "
                    "no controlled execution, no execution, no tool invocation, and no release."
                ),
            },
        ],
        "controlled_execution_boundary_summary": (
            "Controlled execution review request is review only: no execution, "
            "no tool invocation, no product authorization, and no release."
        ),
    }
    payload["request_rows"] = sorted(
        payload["request_rows"],
        key=lambda row: row["execution_review_request_ref"],
    )
    payload["controlled_execution_review_request_id"] = _surface_id(
        "repo_controlled_execution_review_request",
        REPO_CONTROLLED_EXECUTION_REVIEW_REQUEST_SCHEMA,
        payload,
        "controlled_execution_review_request_id",
    )
    return RepoControlledExecutionReviewRequest.model_validate(payload)


def derive_v79a_repo_controlled_execution_non_execution_guardrail(
    *,
    repo_root: Path | None = None,
    controlled_execution_review_request: RepoControlledExecutionReviewRequest | None = None,
) -> RepoControlledExecutionNonExecutionGuardrail:
    _ = repo_root
    request = (
        controlled_execution_review_request
        or derive_v79a_repo_controlled_execution_review_request()
    )
    grouped_rows: dict[str, dict[str, object]] = {}
    for request_row in request.request_rows:
        for guardrail_ref in request_row.guardrail_refs:
            existing = grouped_rows.setdefault(
                guardrail_ref,
                {
                    "guardrail_ref": guardrail_ref,
                    "candidate_ref": request_row.candidate_ref,
                    "source_refs": [],
                    "execution_review_request_refs": [],
                    "forbidden_execution_actions": sorted(_FORBIDDEN_EXECUTION_ACTIONS),
                    "forbidden_downstream_authority": sorted(
                        _FORBIDDEN_DOWNSTREAM_AUTHORITIES
                    ),
                    "guardrail_posture": "non_execution_guardrail_active",
                    "limitation_note": (
                        "This V79-A row is review only: no controlled execution, "
                        "no execution, no tool invocation, no product authorization, "
                        "no external branch activation, and no release."
                    ),
                },
            )
            if existing["candidate_ref"] != request_row.candidate_ref:
                raise ValueError("controlled execution guardrail cannot merge candidates")
            existing["execution_review_request_refs"] = sorted(
                {
                    *existing["execution_review_request_refs"],
                    request_row.execution_review_request_ref,
                }
            )
            existing["source_refs"] = sorted({*existing["source_refs"], *request_row.source_refs})
    payload = {
        "schema": REPO_CONTROLLED_EXECUTION_NON_EXECUTION_GUARDRAIL_SCHEMA,
        "controlled_execution_non_execution_guardrail_id": "",
        "controlled_execution_review_request_id": (
            request.controlled_execution_review_request_id
        ),
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
        "guardrail_rows": sorted(grouped_rows.values(), key=lambda row: row["guardrail_ref"]),
        "non_execution_summary": (
            "Controlled execution non-execution guardrails preserve review only: "
            "no controlled execution, no execution, no tool invocation, and no release."
        ),
    }
    payload["controlled_execution_non_execution_guardrail_id"] = _surface_id(
        "repo_controlled_execution_non_execution_guardrail",
        REPO_CONTROLLED_EXECUTION_NON_EXECUTION_GUARDRAIL_SCHEMA,
        payload,
        "controlled_execution_non_execution_guardrail_id",
    )
    return RepoControlledExecutionNonExecutionGuardrail.model_validate(payload)


def validate_v79a_controlled_execution_review_bundle(
    *,
    controlled_execution_source_index: RepoControlledExecutionSourceIndex,
    controlled_execution_review_request: RepoControlledExecutionReviewRequest,
    controlled_execution_non_execution_guardrail: RepoControlledExecutionNonExecutionGuardrail,
) -> None:
    if (
        controlled_execution_review_request.controlled_execution_source_index_id
        != controlled_execution_source_index.controlled_execution_source_index_id
    ):
        raise ValueError("controlled execution request must reference the source index")
    if (
        controlled_execution_review_request.review_id,
        controlled_execution_review_request.snapshot_id,
        controlled_execution_review_request.source_set_id,
    ) != (
        controlled_execution_source_index.review_id,
        controlled_execution_source_index.snapshot_id,
        controlled_execution_source_index.source_set_id,
    ):
        raise ValueError("controlled execution request provenance must match source index")
    if (
        controlled_execution_non_execution_guardrail.controlled_execution_review_request_id
        != controlled_execution_review_request.controlled_execution_review_request_id
    ):
        raise ValueError("controlled execution guardrail must reference the request surface")
    if (
        controlled_execution_non_execution_guardrail.review_id,
        controlled_execution_non_execution_guardrail.snapshot_id,
        controlled_execution_non_execution_guardrail.source_set_id,
    ) != (
        controlled_execution_review_request.review_id,
        controlled_execution_review_request.snapshot_id,
        controlled_execution_review_request.source_set_id,
    ):
        raise ValueError("controlled execution guardrail provenance must match request")

    source_roles = {
        row.source_ref: row.controlled_execution_source_role
        for row in controlled_execution_source_index.source_rows
    }
    known_sources = set(source_roles)
    request_rows = {
        row.execution_review_request_ref: row
        for row in controlled_execution_review_request.request_rows
    }
    guardrail_rows = {
        row.guardrail_ref: row
        for row in controlled_execution_non_execution_guardrail.guardrail_rows
    }
    for request_row in controlled_execution_review_request.request_rows:
        if any(source_ref not in known_sources for source_ref in request_row.source_refs):
            raise ValueError("controlled execution request source refs must be known")
        roles = {source_roles[source_ref] for source_ref in request_row.source_refs}
        if request_row.execution_review_posture == "eligible_for_controlled_execution_review":
            if not roles.intersection(_ELIGIBILITY_SOURCE_ROLES):
                raise ValueError(
                    "eligible controlled execution requests require released V78-C sources"
                )
        if (
            request_row.v78_summary_refs
            and "v78_readiness_summary_source" not in roles
        ):
            raise ValueError("V78-C summary refs require a readiness-summary source")
        if (
            request_row.v78_handoff_refs
            and "v78_pre_execution_authority_review_handoff_source" not in roles
        ):
            raise ValueError("V78-C handoff refs require a pre-execution handoff source")
        if any(guardrail_ref not in guardrail_rows for guardrail_ref in request_row.guardrail_refs):
            raise ValueError("controlled execution request guardrail refs must be known")
        for guardrail_ref in request_row.guardrail_refs:
            guardrail_row = guardrail_rows[guardrail_ref]
            if guardrail_row.candidate_ref != request_row.candidate_ref:
                raise ValueError("controlled execution guardrails must match candidate")
            if (
                request_row.execution_review_request_ref
                not in guardrail_row.execution_review_request_refs
            ):
                raise ValueError("controlled execution guardrails must reference request rows")

    for guardrail_row in controlled_execution_non_execution_guardrail.guardrail_rows:
        if any(source_ref not in known_sources for source_ref in guardrail_row.source_refs):
            raise ValueError("controlled execution guardrail source refs must be known")
        if any(ref not in request_rows for ref in guardrail_row.execution_review_request_refs):
            raise ValueError("guardrail execution review request refs must be known")
        for ref in guardrail_row.execution_review_request_refs:
            if request_rows[ref].candidate_ref != guardrail_row.candidate_ref:
                raise ValueError("guardrail request refs must match candidate")


def derive_v79a_controlled_execution_review_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoControlledExecutionSourceIndex,
    RepoControlledExecutionReviewRequest,
    RepoControlledExecutionNonExecutionGuardrail,
]:
    source_index = derive_v79a_repo_controlled_execution_source_index(repo_root=repo_root)
    request = derive_v79a_repo_controlled_execution_review_request(
        repo_root=repo_root,
        controlled_execution_source_index=source_index,
    )
    guardrail = derive_v79a_repo_controlled_execution_non_execution_guardrail(
        repo_root=repo_root,
        controlled_execution_review_request=request,
    )
    validate_v79a_controlled_execution_review_bundle(
        controlled_execution_source_index=source_index,
        controlled_execution_review_request=request,
        controlled_execution_non_execution_guardrail=guardrail,
    )
    return source_index, request, guardrail


def _v79b_base_surfaces(
    *,
    repo_root: Path | None = None,
    controlled_execution_source_index: RepoControlledExecutionSourceIndex | None = None,
    controlled_execution_review_request: RepoControlledExecutionReviewRequest | None = None,
    controlled_execution_non_execution_guardrail: (
        RepoControlledExecutionNonExecutionGuardrail | None
    ) = None,
) -> tuple[
    RepoControlledExecutionSourceIndex,
    RepoControlledExecutionReviewRequest,
    RepoControlledExecutionNonExecutionGuardrail,
]:
    if (
        controlled_execution_source_index is None
        or controlled_execution_review_request is None
        or controlled_execution_non_execution_guardrail is None
    ):
        (
            source_index,
            request,
            guardrail,
        ) = derive_v79a_controlled_execution_review_bundle(repo_root=repo_root)
        return (
            controlled_execution_source_index or source_index,
            controlled_execution_review_request or request,
            controlled_execution_non_execution_guardrail or guardrail,
        )
    return (
        controlled_execution_source_index,
        controlled_execution_review_request,
        controlled_execution_non_execution_guardrail,
    )


def _v79b_eligible_request_row(
    request: RepoControlledExecutionReviewRequest,
) -> RepoControlledExecutionReviewRequestRow:
    for row in request.request_rows:
        if row.execution_review_posture == "eligible_for_controlled_execution_review":
            return row
    raise ValueError("V79-B derivation requires an eligible V79-A request row")


def _v79b_reference_refs(
    request: RepoControlledExecutionReviewRequest,
) -> dict[str, object]:
    row = _v79b_eligible_request_row(request)
    return {
        "candidate_ref": row.candidate_ref,
        "source_refs": row.source_refs,
        "execution_review_request_refs": [row.execution_review_request_ref],
        "non_execution_guardrail_refs": row.guardrail_refs,
        "authority_refs": row.required_authority_refs,
        "target_boundary_refs": row.target_boundary_refs,
        "telemetry_requirement_refs": [
            "telemetry-requirement:v79b:self-evidencing:required-later"
        ],
        "rollback_requirement_refs": [
            "rollback-requirement:v79b:self-evidencing:required-later"
        ],
        "operator_confirmation_requirement_refs": [
            "operator-confirmation:v79b:self-evidencing:required-later"
        ],
        "run_plan_refs": ["run-plan:v79b:self-evidencing:repo-script-review"],
        "tool_invocation_plan_refs": [
            "tool-plan:v79b:self-evidencing:repo-description-check-review"
        ],
        "effect_monitoring_contract_refs": [
            "monitoring-contract:v79b:self-evidencing:review-only"
        ],
    }


def derive_v79b_repo_execution_run_plan(
    *,
    repo_root: Path | None = None,
    controlled_execution_source_index: RepoControlledExecutionSourceIndex | None = None,
    controlled_execution_review_request: RepoControlledExecutionReviewRequest | None = None,
    controlled_execution_non_execution_guardrail: (
        RepoControlledExecutionNonExecutionGuardrail | None
    ) = None,
) -> RepoExecutionRunPlan:
    _ = repo_root
    source_index, request, guardrail = _v79b_base_surfaces(
        repo_root=repo_root,
        controlled_execution_source_index=controlled_execution_source_index,
        controlled_execution_review_request=controlled_execution_review_request,
        controlled_execution_non_execution_guardrail=controlled_execution_non_execution_guardrail,
    )
    refs = _v79b_reference_refs(request)
    payload = {
        "schema": REPO_EXECUTION_RUN_PLAN_SCHEMA,
        "execution_run_plan_id": "",
        "controlled_execution_review_request_id": request.controlled_execution_review_request_id,
        "controlled_execution_source_index_id": source_index.controlled_execution_source_index_id,
        "controlled_execution_non_execution_guardrail_id": (
            guardrail.controlled_execution_non_execution_guardrail_id
        ),
        "review_id": request.review_id,
        "snapshot_id": "vNext+221-controlled-execution-review-closeout",
        "source_set_id": "source-set:v79b:released-v79a-run-plan-pressure",
        "run_plan_rows": [
            {
                "run_plan_ref": refs["run_plan_refs"][0],
                "candidate_ref": refs["candidate_ref"],
                "source_refs": refs["source_refs"],
                "execution_review_request_refs": refs["execution_review_request_refs"],
                "non_execution_guardrail_refs": refs["non_execution_guardrail_refs"],
                "command_intent_kind": "bounded_repo_script_run_plan_review",
                "target_boundary_refs": refs["target_boundary_refs"],
                "target_resolution_kind": "concrete_file_ref",
                "authority_refs": refs["authority_refs"],
                "tool_invocation_plan_refs": refs["tool_invocation_plan_refs"],
                "effect_monitoring_contract_refs": refs["effect_monitoring_contract_refs"],
                "telemetry_requirement_refs": refs["telemetry_requirement_refs"],
                "rollback_requirement_refs": refs["rollback_requirement_refs"],
                "operator_confirmation_requirement_refs": (
                    refs["operator_confirmation_requirement_refs"]
                ),
                "exception_refs": [],
                "run_plan_posture": "run_plan_complete_for_review_only",
                "plan_completeness_posture": "complete_for_review_only",
                "run_execution_status": "no_run_performed_by_v79",
                "execution_posture": "no_execution_performed_by_v79",
                "limitation_note": (
                    "Run plan is complete for review only with no run, no execution, "
                    "and no tool invocation."
                ),
            }
        ],
        "run_plan_summary": (
            "Execution run plans are review only with no run, no execution, "
            "and no tool invocation."
        ),
    }
    payload["execution_run_plan_id"] = _surface_id(
        "repo_execution_run_plan",
        REPO_EXECUTION_RUN_PLAN_SCHEMA,
        payload,
        "execution_run_plan_id",
    )
    return RepoExecutionRunPlan.model_validate(payload)


def derive_v79b_repo_tool_invocation_plan(
    *,
    repo_root: Path | None = None,
    controlled_execution_source_index: RepoControlledExecutionSourceIndex | None = None,
    controlled_execution_review_request: RepoControlledExecutionReviewRequest | None = None,
    controlled_execution_non_execution_guardrail: (
        RepoControlledExecutionNonExecutionGuardrail | None
    ) = None,
) -> RepoToolInvocationPlan:
    _ = repo_root
    source_index, request, guardrail = _v79b_base_surfaces(
        repo_root=repo_root,
        controlled_execution_source_index=controlled_execution_source_index,
        controlled_execution_review_request=controlled_execution_review_request,
        controlled_execution_non_execution_guardrail=controlled_execution_non_execution_guardrail,
    )
    refs = _v79b_reference_refs(request)
    payload = {
        "schema": REPO_TOOL_INVOCATION_PLAN_SCHEMA,
        "tool_invocation_plan_id": "",
        "controlled_execution_review_request_id": request.controlled_execution_review_request_id,
        "controlled_execution_source_index_id": source_index.controlled_execution_source_index_id,
        "controlled_execution_non_execution_guardrail_id": (
            guardrail.controlled_execution_non_execution_guardrail_id
        ),
        "review_id": request.review_id,
        "snapshot_id": "vNext+221-controlled-execution-review-closeout",
        "source_set_id": "source-set:v79b:released-v79a-tool-plan-pressure",
        "tool_invocation_plan_rows": [
            {
                "tool_invocation_plan_ref": refs["tool_invocation_plan_refs"][0],
                "candidate_ref": refs["candidate_ref"],
                "source_refs": refs["source_refs"],
                "execution_review_request_refs": refs["execution_review_request_refs"],
                "non_execution_guardrail_refs": refs["non_execution_guardrail_refs"],
                "tool_id": "make",
                "tool_target_refs": [
                    "packages/adeu_repo_description/tests/"
                    "test_controlled_execution_review_v79b.py"
                ],
                "tool_target_horizon": "repo-description controlled-execution review tests",
                "permission_refs": ["permission:v78b:self-evidencing:tool-use-review"],
                "authority_refs": refs["authority_refs"],
                "effect_monitoring_contract_refs": refs["effect_monitoring_contract_refs"],
                "exception_refs": [],
                "tool_invocation_plan_posture": (
                    "tool_invocation_plan_complete_for_review_only"
                ),
                "plan_completeness_posture": "complete_for_review_only",
                "tool_invocation_status": "no_tool_invocation_performed_by_v79",
                "tool_invocation_posture": "no_tool_invocation_performed_by_v79",
                "limitation_note": (
                    "Tool invocation plan is complete for review only with no tool "
                    "invocation and no execution."
                ),
            }
        ],
        "tool_invocation_plan_summary": (
            "Tool invocation plans are review only with no tool invocation and no execution."
        ),
    }
    payload["tool_invocation_plan_id"] = _surface_id(
        "repo_tool_invocation_plan",
        REPO_TOOL_INVOCATION_PLAN_SCHEMA,
        payload,
        "tool_invocation_plan_id",
    )
    return RepoToolInvocationPlan.model_validate(payload)


def derive_v79b_repo_execution_effect_monitoring_contract(
    *,
    repo_root: Path | None = None,
    controlled_execution_source_index: RepoControlledExecutionSourceIndex | None = None,
    controlled_execution_review_request: RepoControlledExecutionReviewRequest | None = None,
    controlled_execution_non_execution_guardrail: (
        RepoControlledExecutionNonExecutionGuardrail | None
    ) = None,
) -> RepoExecutionEffectMonitoringContract:
    _ = repo_root
    source_index, request, guardrail = _v79b_base_surfaces(
        repo_root=repo_root,
        controlled_execution_source_index=controlled_execution_source_index,
        controlled_execution_review_request=controlled_execution_review_request,
        controlled_execution_non_execution_guardrail=controlled_execution_non_execution_guardrail,
    )
    refs = _v79b_reference_refs(request)
    confirmation_ref = refs["operator_confirmation_requirement_refs"][0]
    payload = {
        "schema": REPO_EXECUTION_EFFECT_MONITORING_CONTRACT_SCHEMA,
        "execution_effect_monitoring_contract_id": "",
        "controlled_execution_review_request_id": request.controlled_execution_review_request_id,
        "controlled_execution_source_index_id": source_index.controlled_execution_source_index_id,
        "controlled_execution_non_execution_guardrail_id": (
            guardrail.controlled_execution_non_execution_guardrail_id
        ),
        "review_id": request.review_id,
        "snapshot_id": "vNext+221-controlled-execution-review-closeout",
        "source_set_id": "source-set:v79b:released-v79a-monitoring-pressure",
        "effect_monitoring_contract_rows": [
            {
                "effect_monitoring_contract_ref": refs["effect_monitoring_contract_refs"][0],
                "candidate_ref": refs["candidate_ref"],
                "source_refs": refs["source_refs"],
                "run_plan_refs": refs["run_plan_refs"],
                "tool_invocation_plan_refs": refs["tool_invocation_plan_refs"],
                "non_execution_guardrail_refs": refs["non_execution_guardrail_refs"],
                "expected_effect_surface_refs": [
                    "effect-surface:v79b:self-evidencing:planned-test-observation"
                ],
                "forbidden_effect_surface_refs": [
                    "effect-surface:v79b:self-evidencing:accepted-effect",
                    "effect-surface:v79b:self-evidencing:target-mutation",
                ],
                "telemetry_requirement_refs": refs["telemetry_requirement_refs"],
                "rollback_requirement_refs": refs["rollback_requirement_refs"],
                "operator_confirmation_requirement_refs": [confirmation_ref],
                "operator_confirmation_requirement_rows": [
                    {
                        "confirmation_requirement_ref": confirmation_ref,
                        "candidate_ref": refs["candidate_ref"],
                        "required_confirmation_kind": "maintainer_confirmation_required",
                        "source_refs": refs["source_refs"],
                        "authority_refs": refs["authority_refs"],
                        "confirmation_posture": "confirmation_required_for_later_review",
                        "non_authorization_guardrail": (
                            "Operator confirmation requirement is not authorization; "
                            "no execution and no tool invocation."
                        ),
                        "limitation_note": (
                            "Operator confirmation requirement remains a requirement, "
                            "not authorization."
                        ),
                    }
                ],
                "monitoring_posture": "monitoring_contract_complete_for_review_only",
                "effect_observation_posture": "no_effect_observed_by_v79",
                "limitation_note": (
                    "Effect monitoring contract is review only with no observed effect, "
                    "no execution, and no rollback verification."
                ),
            }
        ],
        "effect_monitoring_summary": (
            "Effect monitoring contracts are review only with no observed effect, "
            "no execution, and no rollback verification."
        ),
    }
    payload["execution_effect_monitoring_contract_id"] = _surface_id(
        "repo_execution_effect_monitoring_contract",
        REPO_EXECUTION_EFFECT_MONITORING_CONTRACT_SCHEMA,
        payload,
        "execution_effect_monitoring_contract_id",
    )
    return RepoExecutionEffectMonitoringContract.model_validate(payload)


def derive_v79b_repo_controlled_execution_exception_register(
    *,
    repo_root: Path | None = None,
    controlled_execution_source_index: RepoControlledExecutionSourceIndex | None = None,
    controlled_execution_review_request: RepoControlledExecutionReviewRequest | None = None,
    controlled_execution_non_execution_guardrail: (
        RepoControlledExecutionNonExecutionGuardrail | None
    ) = None,
) -> RepoControlledExecutionExceptionRegister:
    _ = repo_root
    source_index, request, guardrail = _v79b_base_surfaces(
        repo_root=repo_root,
        controlled_execution_source_index=controlled_execution_source_index,
        controlled_execution_review_request=controlled_execution_review_request,
        controlled_execution_non_execution_guardrail=controlled_execution_non_execution_guardrail,
    )
    refs = _v79b_reference_refs(request)
    payload = {
        "schema": REPO_CONTROLLED_EXECUTION_EXCEPTION_REGISTER_SCHEMA,
        "controlled_execution_exception_register_id": "",
        "controlled_execution_review_request_id": request.controlled_execution_review_request_id,
        "controlled_execution_source_index_id": source_index.controlled_execution_source_index_id,
        "controlled_execution_non_execution_guardrail_id": (
            guardrail.controlled_execution_non_execution_guardrail_id
        ),
        "review_id": request.review_id,
        "snapshot_id": "vNext+221-controlled-execution-review-closeout",
        "source_set_id": "source-set:v79b:released-v79a-exception-pressure",
        "exception_rows": [
            {
                "exception_ref": "exception:v79b:self-evidencing:external-branch-blocked",
                "candidate_ref": refs["candidate_ref"],
                "source_refs": refs["source_refs"],
                "execution_review_request_refs": refs["execution_review_request_refs"],
                "run_plan_refs": refs["run_plan_refs"],
                "tool_invocation_plan_refs": refs["tool_invocation_plan_refs"],
                "effect_monitoring_contract_refs": refs["effect_monitoring_contract_refs"],
                "exception_kind": "unknown_needs_review",
                "exception_posture": "warning_only",
                "blocking_surface_refs": [],
                "required_next_surface": "future_external_branch_review",
                "limitation_note": (
                    "External branch pressure remains visible as unknown later-review "
                    "context; it is unsettled and no execution occurs."
                ),
            },
            {
                "exception_ref": "exception:v79b:product-wedge:product-authority-blocked",
                "candidate_ref": "candidate:internal:typed_adjudication_product_wedge",
                "source_refs": refs["source_refs"],
                "execution_review_request_refs": [
                    "execution-review:v79a:product-wedge:blocked"
                ],
                "run_plan_refs": [],
                "tool_invocation_plan_refs": [],
                "effect_monitoring_contract_refs": [],
                "exception_kind": "product_authority_gap",
                "exception_posture": "blocking",
                "blocking_surface_refs": [
                    "authority:v78a:product-wedge:product-review"
                ],
                "required_next_surface": "future_product_review",
                "limitation_note": (
                    "Product pressure remains blocked for later product review "
                    "with no execution."
                ),
            },
        ],
        "exception_summary": (
            "Controlled execution exceptions are review only: blocking and warning "
            "states remain visible with no execution."
        ),
    }
    payload["exception_rows"] = sorted(
        payload["exception_rows"],
        key=lambda row: row["exception_ref"],
    )
    payload["controlled_execution_exception_register_id"] = _surface_id(
        "repo_controlled_execution_exception_register",
        REPO_CONTROLLED_EXECUTION_EXCEPTION_REGISTER_SCHEMA,
        payload,
        "controlled_execution_exception_register_id",
    )
    return RepoControlledExecutionExceptionRegister.model_validate(payload)


def validate_v79b_controlled_execution_review_bundle(
    *,
    controlled_execution_source_index: RepoControlledExecutionSourceIndex,
    controlled_execution_review_request: RepoControlledExecutionReviewRequest,
    controlled_execution_non_execution_guardrail: RepoControlledExecutionNonExecutionGuardrail,
    execution_run_plan: RepoExecutionRunPlan,
    tool_invocation_plan: RepoToolInvocationPlan,
    execution_effect_monitoring_contract: RepoExecutionEffectMonitoringContract,
    controlled_execution_exception_register: RepoControlledExecutionExceptionRegister,
) -> None:
    validate_v79a_controlled_execution_review_bundle(
        controlled_execution_source_index=controlled_execution_source_index,
        controlled_execution_review_request=controlled_execution_review_request,
        controlled_execution_non_execution_guardrail=controlled_execution_non_execution_guardrail,
    )
    expected_surface_refs = (
        controlled_execution_review_request.controlled_execution_review_request_id,
        controlled_execution_source_index.controlled_execution_source_index_id,
        controlled_execution_non_execution_guardrail.controlled_execution_non_execution_guardrail_id,
    )
    for surface in (
        execution_run_plan,
        tool_invocation_plan,
        execution_effect_monitoring_contract,
        controlled_execution_exception_register,
    ):
        if (
            surface.controlled_execution_review_request_id,
            surface.controlled_execution_source_index_id,
            surface.controlled_execution_non_execution_guardrail_id,
        ) != expected_surface_refs:
            raise ValueError("V79-B surfaces must reference released V79-A surfaces")

    known_sources = {row.source_ref for row in controlled_execution_source_index.source_rows}
    known_requests = {
        row.execution_review_request_ref: row
        for row in controlled_execution_review_request.request_rows
    }
    known_guardrails = {
        row.guardrail_ref: row
        for row in controlled_execution_non_execution_guardrail.guardrail_rows
    }
    run_rows = {row.run_plan_ref: row for row in execution_run_plan.run_plan_rows}
    tool_rows = {
        row.tool_invocation_plan_ref: row
        for row in tool_invocation_plan.tool_invocation_plan_rows
    }
    monitoring_rows = {
        row.effect_monitoring_contract_ref: row
        for row in execution_effect_monitoring_contract.effect_monitoring_contract_rows
    }
    exception_rows = {
        row.exception_ref: row
        for row in controlled_execution_exception_register.exception_rows
    }

    def _require_known_refs(refs: list[str], known: set[str], message: str) -> None:
        if any(ref not in known for ref in refs):
            raise ValueError(message)

    def _require_matching_candidate(
        refs: list[str],
        rows_by_ref: dict[str, _CartographyBase],
        *,
        candidate_ref: str,
        message: str,
    ) -> None:
        for ref in refs:
            if rows_by_ref[ref].candidate_ref != candidate_ref:
                raise ValueError(message)

    for row in execution_run_plan.run_plan_rows:
        _require_known_refs(row.source_refs, known_sources, "run plan source refs must be known")
        _require_known_refs(
            row.execution_review_request_refs,
            set(known_requests),
            "run plan request refs must be known",
        )
        _require_known_refs(
            row.non_execution_guardrail_refs,
            set(known_guardrails),
            "run plan guardrail refs must be known",
        )
        _require_known_refs(
            row.tool_invocation_plan_refs,
            set(tool_rows),
            "run plan tool-plan refs must be known",
        )
        _require_known_refs(
            row.effect_monitoring_contract_refs,
            set(monitoring_rows),
            "run plan monitoring refs must be known",
        )
        _require_known_refs(
            row.exception_refs,
            set(exception_rows),
            "run plan exception refs must be known",
        )
        for request_ref in row.execution_review_request_refs:
            if known_requests[request_ref].candidate_ref != row.candidate_ref:
                raise ValueError("run plan request refs must match candidate")
        _require_matching_candidate(
            row.tool_invocation_plan_refs,
            tool_rows,
            candidate_ref=row.candidate_ref,
            message="run plan tool-plan refs must match candidate",
        )
        _require_matching_candidate(
            row.effect_monitoring_contract_refs,
            monitoring_rows,
            candidate_ref=row.candidate_ref,
            message="run plan monitoring refs must match candidate",
        )

    for row in tool_invocation_plan.tool_invocation_plan_rows:
        _require_known_refs(row.source_refs, known_sources, "tool plan source refs must be known")
        _require_known_refs(
            row.execution_review_request_refs,
            set(known_requests),
            "tool plan request refs must be known",
        )
        _require_known_refs(
            row.non_execution_guardrail_refs,
            set(known_guardrails),
            "tool plan guardrail refs must be known",
        )
        _require_known_refs(
            row.effect_monitoring_contract_refs,
            set(monitoring_rows),
            "tool plan monitoring refs must be known",
        )
        _require_known_refs(
            row.exception_refs,
            set(exception_rows),
            "tool plan exception refs must be known",
        )
        for request_ref in row.execution_review_request_refs:
            if known_requests[request_ref].candidate_ref != row.candidate_ref:
                raise ValueError("tool plan request refs must match candidate")
        _require_matching_candidate(
            row.effect_monitoring_contract_refs,
            monitoring_rows,
            candidate_ref=row.candidate_ref,
            message="tool plan monitoring refs must match candidate",
        )

    for row in execution_effect_monitoring_contract.effect_monitoring_contract_rows:
        _require_known_refs(
            row.source_refs,
            known_sources,
            "monitoring contract source refs must be known",
        )
        _require_known_refs(row.run_plan_refs, set(run_rows), "monitoring run refs must be known")
        _require_known_refs(
            row.tool_invocation_plan_refs,
            set(tool_rows),
            "monitoring tool-plan refs must be known",
        )
        _require_known_refs(
            row.non_execution_guardrail_refs,
            set(known_guardrails),
            "monitoring guardrail refs must be known",
        )
        for run_ref in row.run_plan_refs:
            if run_rows[run_ref].candidate_ref != row.candidate_ref:
                raise ValueError("monitoring run refs must match candidate")
        for tool_ref in row.tool_invocation_plan_refs:
            if tool_rows[tool_ref].candidate_ref != row.candidate_ref:
                raise ValueError("monitoring tool-plan refs must match candidate")

    for row in controlled_execution_exception_register.exception_rows:
        _require_known_refs(row.source_refs, known_sources, "exception source refs must be known")
        _require_known_refs(
            row.execution_review_request_refs,
            set(known_requests),
            "exception request refs must be known",
        )
        _require_known_refs(row.run_plan_refs, set(run_rows), "exception run refs must be known")
        _require_known_refs(
            row.tool_invocation_plan_refs,
            set(tool_rows),
            "exception tool-plan refs must be known",
        )
        _require_known_refs(
            row.effect_monitoring_contract_refs,
            set(monitoring_rows),
            "exception monitoring refs must be known",
        )
        _require_matching_candidate(
            row.execution_review_request_refs,
            known_requests,
            candidate_ref=row.candidate_ref,
            message="exception request refs must match candidate",
        )
        _require_matching_candidate(
            row.run_plan_refs,
            run_rows,
            candidate_ref=row.candidate_ref,
            message="exception run refs must match candidate",
        )
        _require_matching_candidate(
            row.tool_invocation_plan_refs,
            tool_rows,
            candidate_ref=row.candidate_ref,
            message="exception tool-plan refs must match candidate",
        )
        _require_matching_candidate(
            row.effect_monitoring_contract_refs,
            monitoring_rows,
            candidate_ref=row.candidate_ref,
            message="exception monitoring refs must match candidate",
        )
        if row.exception_kind in {"product_authority_gap", "external_branch_authority_gap"}:
            if row.exception_posture not in {"blocking", "future_family_only"}:
                raise ValueError("product/external exceptions must remain blocked or deferred")


def derive_v79b_controlled_execution_review_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoControlledExecutionSourceIndex,
    RepoControlledExecutionReviewRequest,
    RepoControlledExecutionNonExecutionGuardrail,
    RepoExecutionRunPlan,
    RepoToolInvocationPlan,
    RepoExecutionEffectMonitoringContract,
    RepoControlledExecutionExceptionRegister,
]:
    source_index, request, guardrail = derive_v79a_controlled_execution_review_bundle(
        repo_root=repo_root
    )
    run_plan = derive_v79b_repo_execution_run_plan(
        repo_root=repo_root,
        controlled_execution_source_index=source_index,
        controlled_execution_review_request=request,
        controlled_execution_non_execution_guardrail=guardrail,
    )
    tool_plan = derive_v79b_repo_tool_invocation_plan(
        repo_root=repo_root,
        controlled_execution_source_index=source_index,
        controlled_execution_review_request=request,
        controlled_execution_non_execution_guardrail=guardrail,
    )
    monitoring = derive_v79b_repo_execution_effect_monitoring_contract(
        repo_root=repo_root,
        controlled_execution_source_index=source_index,
        controlled_execution_review_request=request,
        controlled_execution_non_execution_guardrail=guardrail,
    )
    exceptions = derive_v79b_repo_controlled_execution_exception_register(
        repo_root=repo_root,
        controlled_execution_source_index=source_index,
        controlled_execution_review_request=request,
        controlled_execution_non_execution_guardrail=guardrail,
    )
    validate_v79b_controlled_execution_review_bundle(
        controlled_execution_source_index=source_index,
        controlled_execution_review_request=request,
        controlled_execution_non_execution_guardrail=guardrail,
        execution_run_plan=run_plan,
        tool_invocation_plan=tool_plan,
        execution_effect_monitoring_contract=monitoring,
        controlled_execution_exception_register=exceptions,
    )
    return source_index, request, guardrail, run_plan, tool_plan, monitoring, exceptions
