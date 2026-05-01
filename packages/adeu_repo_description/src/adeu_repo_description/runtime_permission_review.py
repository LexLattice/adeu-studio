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

REPO_RUNTIME_PERMISSION_REVIEW_REQUEST_SCHEMA = "repo_runtime_permission_review_request@1"
REPO_RUNTIME_PERMISSION_SOURCE_INDEX_SCHEMA = "repo_runtime_permission_source_index@1"
REPO_RUNTIME_NON_EXECUTION_GUARDRAIL_SCHEMA = "repo_runtime_non_execution_guardrail@1"
REPO_COMMAND_PREFLIGHT_CONTRACT_SCHEMA = "repo_command_preflight_contract@1"
REPO_ACTION_EFFECT_ENVELOPE_SCHEMA = "repo_action_effect_envelope@1"
REPO_RUNTIME_TELEMETRY_REQUIREMENT_SCHEMA = "repo_runtime_telemetry_requirement@1"
REPO_RUNTIME_ROLLBACK_CONTRACT_SCHEMA = "repo_runtime_rollback_contract@1"
REPO_RUNTIME_PERMISSION_AUTHORITY_POSTURE_SCHEMA = (
    "repo_runtime_permission_authority_posture@1"
)
REPO_RUNTIME_PERMISSION_REVIEW_SUMMARY_SCHEMA = (
    "repo_runtime_permission_review_summary@1"
)
REPO_POST_RUNTIME_PERMISSION_REVIEW_HANDOFF_SCHEMA = (
    "repo_post_runtime_permission_review_handoff@1"
)
REPO_RUNTIME_PERMISSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA = (
    "repo_runtime_permission_family_closeout_alignment@1"
)

RuntimeSourceRole = Literal[
    "v76_summary_source",
    "v76_post_reconciliation_handoff_source",
    "v76_family_closeout_source",
    "v72_effect_surface_context",
    "v72_rollback_context",
    "combined_dogfood_source",
    "support_roadmap_context",
    "absence_marker",
]
RuntimeReviewPosture = Literal[
    "eligible_for_runtime_permission_review",
    "blocked_by_missing_source",
    "blocked_by_missing_authority",
    "blocked_by_non_runtime_handoff",
    "blocked_by_product_authority_gap",
    "blocked_by_external_branch_gap",
    "future_family_only",
    "rejected_out_of_scope",
]
RequestedPermissionHorizon = Literal[
    "command_preflight_review",
    "tool_use_permission_review",
    "bounded_runtime_action_review",
    "effect_telemetry_review",
    "rollback_readiness_review",
    "future_product_review",
    "future_external_branch_review",
    "future_family_review",
]
CommandIntentKind = Literal[
    "no_command_intent",
    "shell_command_pressure",
    "python_tool_pressure",
    "repo_script_pressure",
    "api_call_pressure",
    "external_tool_pressure",
    "future_family_only",
]
CommandExecutionPosture = Literal[
    "no_execution_authorized",
    "execution_requires_later_authority",
    "execution_forbidden_by_this_family",
]
TargetBoundaryPosture = Literal[
    "target_boundary_known",
    "target_boundary_missing",
    "target_boundary_blocked",
    "no_target_boundary",
    "future_family_only",
]
RuntimeAuthorityKind = Literal[
    "runtime_execution_authority",
    "tool_use_authority",
    "product_authorization",
    "external_branch_activation",
    "release_authority",
    "human_or_maintainer_review",
    "recursive_policy_authority",
]
RuntimeAuthorityGapPosture = Literal[
    "authority_gap_present",
    "authority_checked_absent",
    "authority_not_applicable",
    "unknown_needs_review",
]
RuntimeRequiredBeforeSurface = Literal[
    "before_runtime_permission_review",
    "before_tool_use_permission_review",
    "before_command_preflight_review",
    "before_product_review",
    "before_external_branch_review",
    "before_release_review",
    "before_human_or_maintainer_review",
    "before_recursive_policy_review",
    "not_selected_here",
]
ForbiddenRuntimeAction = Literal[
    "run_command",
    "invoke_tool_for_effect",
    "assign_worker",
    "dispatch_worker",
    "open_pr",
    "commit",
    "merge",
    "release",
    "external_submission",
]
ForbiddenDownstreamAuthority = Literal[
    "runtime_permission_grant",
    "product_authorization",
    "external_branch_activation",
    "released_truth",
    "benchmark_truth",
    "model_selection",
    "living_memory_authority",
    "recursive_policy_amendment",
]
RuntimeToolUsePosture = Literal[
    "tool_use_not_authorized_by_v77",
    "tool_use_requires_later_authority",
    "tool_applicability_context_only",
]
V77BCommandIntentKind = Literal[
    "no_command_intent",
    "shell_command_later_review",
    "python_tool_later_review",
    "repo_script_later_review",
    "api_call_later_review",
    "external_tool_later_review",
    "future_family_only",
]
CommandRefPosture = Literal[
    "command_reference_absent_review_only",
    "command_label_review_only",
    "script_label_review_only",
    "future_family_only",
]
TargetResolutionKind = Literal[
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
CommandPreflightPosture = Literal[
    "preflight_contract_for_review_only",
    "preflight_blocked_by_missing_source",
    "preflight_blocked_by_missing_authority",
    "preflight_blocked_by_target_boundary",
    "preflight_blocked_by_missing_telemetry",
    "preflight_blocked_by_missing_rollback",
    "preflight_future_family_only",
    "preflight_rejected_out_of_scope",
]
ForbiddenRuntimeInference = Literal[
    "command_execution",
    "runtime_permission_grant",
    "tool_use_permission",
    "target_change_authority",
    "accepted_effect",
    "observed_telemetry",
    "rollback_verification",
    "product_authorization",
    "external_branch_activation",
    "release_authority",
    "v77c_surface_emission",
]
EffectEnvelopePosture = Literal[
    "effect_envelope_for_review_only",
    "effect_envelope_blocked_by_missing_target",
    "effect_envelope_blocked_by_missing_telemetry",
    "effect_envelope_blocked_by_missing_rollback",
    "effect_envelope_future_family_only",
    "effect_envelope_rejected_out_of_scope",
]
EffectAcceptancePosture = Literal[
    "no_effect_accepted",
    "effect_requires_later_review",
    "effect_not_observed",
    "effect_observed_from_prior_authorized_artifact",
]
TelemetrySurfaceKind = Literal[
    "test_result_telemetry",
    "runtime_event_stream_telemetry",
    "schema_validation_telemetry",
    "not_applicable",
]
TelemetryPosture = Literal[
    "telemetry_required_later",
    "telemetry_source_present_for_prior_artifact",
    "telemetry_missing_expected_source",
    "telemetry_not_applicable",
    "telemetry_future_family_only",
]
RollbackSurfaceKind = Literal[
    "source_revert_plan",
    "fixture_revert_plan",
    "schema_revert_plan",
    "not_applicable",
]
RollbackPosture = Literal[
    "rollback_required_later",
    "rollback_source_present_for_prior_artifact",
    "rollback_missing_expected_source",
    "rollback_blocked",
    "rollback_not_applicable",
    "rollback_future_family_only",
]
RuntimePermissionAuthorityRequirementKind = Literal[
    "human_or_maintainer_runtime_review",
    "runtime_permission_authority",
    "tool_use_authority",
    "product_authorization",
    "external_branch_activation",
    "release_authority",
    "recursive_policy_authority",
    "future_family_authority",
]
RuntimePermissionAuthorityGapPosture = Literal[
    "authority_gap_present",
    "authority_checked_absent",
    "authority_not_applicable",
    "unknown_needs_review",
]
RuntimePermissionAuthorityDecisionPosture = Literal[
    "authority_required_later",
    "authority_missing",
    "authority_not_applicable",
    "authority_future_family_only",
    "authority_rejected_out_of_scope",
]
RuntimePermissionSummaryPosture = Literal[
    "review_ready_no_blockers",
    "review_ready_with_nonblocking_warnings",
    "blocked_by_missing_source",
    "blocked_by_missing_authority",
    "blocked_by_missing_telemetry",
    "blocked_by_missing_rollback",
    "blocked_by_target_boundary",
    "future_family_only",
    "rejected_out_of_scope",
]
RuntimePermissionReadyBasisPosture = Literal[
    "ready_no_blockers",
    "ready_with_carried_nonblocking_warnings",
    "not_ready_blockers_remain",
    "future_family_only",
]
PostRuntimePermissionReviewHandoffTarget = Literal[
    "future_runtime_execution_authority_review",
    "future_tool_use_permission_review",
    "future_product_review",
    "future_external_branch_review",
    "future_outcome_review",
    "future_experiment_review",
    "future_family_review",
    "deferred_no_selection",
]
PostRuntimePermissionReviewHandoffPosture = Literal[
    "ready_for_later_review",
    "blocked_by_required_later_authority",
    "blocked_by_missing_telemetry",
    "blocked_by_missing_rollback",
    "blocked_by_target_boundary",
    "deferred_to_future_family",
    "rejected_out_of_scope",
]
RuntimePermissionExecutionPosture = Literal["no_runtime_permission_granted_by_v77"]
ForbiddenV77CAuthorityInference = Literal[
    "command_execution",
    "runtime_permission_grant",
    "tool_use_permission",
    "worker_assignment",
    "dispatch_execution",
    "product_authorization",
    "external_branch_activation",
    "release_authority",
    "benchmark_truth",
    "model_selection",
    "living_memory_authority",
    "recursive_policy_amendment",
]

_ELIGIBILITY_SOURCE_ROLES = {
    "v76_summary_source",
    "v76_post_reconciliation_handoff_source",
    "v76_family_closeout_source",
}
_CONTEXT_SOURCE_ROLES = {
    "v72_effect_surface_context",
    "v72_rollback_context",
    "combined_dogfood_source",
    "support_roadmap_context",
}
_FORBIDDEN_RUNTIME_ACTIONS = {
    "run_command",
    "invoke_tool_for_effect",
    "assign_worker",
    "dispatch_worker",
    "open_pr",
    "commit",
    "merge",
    "release",
    "external_submission",
}
_FORBIDDEN_DOWNSTREAM_AUTHORITIES = {
    "runtime_permission_grant",
    "product_authorization",
    "external_branch_activation",
    "released_truth",
    "benchmark_truth",
    "model_selection",
    "living_memory_authority",
    "recursive_policy_amendment",
}
_FORBIDDEN_RUNTIME_INFERENCES = {
    "command_execution",
    "runtime_permission_grant",
    "tool_use_permission",
    "target_change_authority",
    "accepted_effect",
    "observed_telemetry",
    "rollback_verification",
    "product_authorization",
    "external_branch_activation",
    "release_authority",
    "v77c_surface_emission",
}
_FORBIDDEN_V77C_AUTHORITY_INFERENCES = {
    "command_execution",
    "runtime_permission_grant",
    "tool_use_permission",
    "worker_assignment",
    "dispatch_execution",
    "product_authorization",
    "external_branch_activation",
    "release_authority",
    "benchmark_truth",
    "model_selection",
    "living_memory_authority",
    "recursive_policy_amendment",
}


def _reject_runtime_authority_claim(value: str, *, field_name: str) -> str:
    lowered = value.lower()
    forbidden_patterns = [
        r"runtime permission (?:is |was |has been |gets |got )?granted",
        r"grants runtime",
        r"permission to run",
        r"command (?:is |was |has been |gets |got )?executed",
        r"command output proves",
        r"tool use (?:is |was |has been |gets |got )?authorized",
        r"assign worker",
        r"dispatch worker",
        r"open pr",
        r"commit now",
        r"merge now",
        r"release now",
        r"product (?:is |was |has been |gets |got )?authorized",
        r"external branch (?:is |was |has been |gets |got )?activated",
        r"external submission",
        r"benchmark truth",
        r"model (?:is |was |has been |gets |got )?selected",
        r"policy (?:is |was |has been |gets |got )?amended",
    ]
    negation_markers = ("no ", "not ", "without ", "forbidden ", "non-")
    for pattern in forbidden_patterns:
        match = re.search(pattern, lowered)
        if match is None:
            continue
        prefix = lowered[max(0, match.start() - 18) : match.start()]
        if not any(marker in prefix for marker in negation_markers):
            raise ValueError(f"{field_name} may not carry runtime or downstream authority")
    return value


def _reject_v77b_authority_claim(value: str, *, field_name: str) -> str:
    _reject_runtime_authority_claim(value, field_name=field_name)
    lowered = value.lower()
    forbidden_patterns = [
        r"effect (?:is |was |has been |gets |got )?accepted",
        r"accepted effect",
        r"telemetry (?:is |was |has been |gets |got )?successful",
        r"telemetry success",
        r"rollback (?:is |was |has been |gets |got )?verified",
        r"verified rollback",
        r"preflight (?:is |was |has been |gets |got )?authorized",
    ]
    negation_markers = ("no ", "not ", "without ", "forbidden ", "non-")
    for pattern in forbidden_patterns:
        match = re.search(pattern, lowered)
        if match is None:
            continue
        prefix = lowered[max(0, match.start() - 18) : match.start()]
        if not any(marker in prefix for marker in negation_markers):
            raise ValueError(f"{field_name} may not carry runtime or downstream authority")
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


class RepoRuntimePermissionSourceRow(_CartographyBase):
    source_ref: str
    source_kind: CandidateSourceKind
    authority_layer: CandidateAuthorityLayer
    source_status: SourceStatus
    source_presence_posture: CandidateSourcePresencePosture
    runtime_source_role: RuntimeSourceRole
    source_horizon: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_runtime_source_row(self) -> RepoRuntimePermissionSourceRow:
        _repo_ref(self.source_ref, field_name="source_ref")
        _non_empty(self.source_horizon, field_name="source_horizon")
        _reject_runtime_authority_claim(self.limitation_note, field_name="limitation_note")
        if (
            self.runtime_source_role != "absence_marker"
            and self.source_presence_posture != "present"
        ):
            raise ValueError("non-absence runtime source rows must be present")
        if (
            self.runtime_source_role == "absence_marker"
            and self.source_presence_posture == "present"
        ):
            raise ValueError("absence-marker runtime source rows must not be present sources")
        if self.runtime_source_role in _CONTEXT_SOURCE_ROLES and self.authority_layer == "lock":
            raise ValueError("context runtime source roles may not be lock authority")
        return self


class RepoRuntimePermissionSourceIndex(_CartographyBase):
    schema: Literal["repo_runtime_permission_source_index@1"] = (
        REPO_RUNTIME_PERMISSION_SOURCE_INDEX_SCHEMA
    )
    runtime_permission_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    source_rows: list[RepoRuntimePermissionSourceRow] = Field(min_length=1)
    runtime_source_summary: str

    @model_validator(mode="after")
    def _validate_runtime_source_index(self) -> RepoRuntimePermissionSourceIndex:
        object.__setattr__(
            self,
            "source_rows",
            _sorted_unique_by_ref(self.source_rows, attr="source_ref", field_name="source_rows"),
        )
        _non_empty(self.review_id, field_name="review_id")
        _non_empty(self.snapshot_id, field_name="snapshot_id")
        _non_empty(self.source_set_id, field_name="source_set_id")
        _require_terms(
            self.runtime_source_summary,
            field_name="runtime_source_summary",
            terms=("eligibility", "context", "no prose memory", "no runtime permission"),
        )
        expected_id = _surface_id(
            "repo_runtime_permission_source_index",
            self.schema,
            self.model_dump(mode="json"),
            "runtime_permission_source_index_id",
        )
        if self.runtime_permission_source_index_id != expected_id:
            raise ValueError(
                "runtime_permission_source_index_id does not match canonical payload hash"
            )
        return self


class RepoRuntimeRequiredLaterAuthorityRow(_CartographyBase):
    authority_requirement_ref: str
    candidate_ref: str
    authority_kind: RuntimeAuthorityKind
    required_before_surface: RuntimeRequiredBeforeSurface
    source_refs: list[str] = Field(min_length=1)
    source_presence_posture: CandidateSourcePresencePosture
    authority_gap_posture: RuntimeAuthorityGapPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_runtime_authority_row(self) -> RepoRuntimeRequiredLaterAuthorityRow:
        _non_empty(self.authority_requirement_ref, field_name="authority_requirement_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        object.__setattr__(
            self,
            "source_refs",
            _sorted_unique(self.source_refs, field_name="source_refs"),
        )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        _reject_runtime_authority_claim(self.limitation_note, field_name="limitation_note")
        if (
            self.source_presence_posture != "present"
            and self.authority_gap_posture != "unknown_needs_review"
        ):
            raise ValueError("missing runtime authority sources must remain unknown-needs-review")
        return self


class RepoRuntimePermissionReviewRequestRow(_CartographyBase):
    runtime_review_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    v76_summary_refs: list[str] = Field(default_factory=list)
    v76_handoff_refs: list[str] = Field(default_factory=list)
    v76_closeout_refs: list[str] = Field(default_factory=list)
    requested_permission_horizon: RequestedPermissionHorizon
    runtime_review_posture: RuntimeReviewPosture
    command_intent_kind: CommandIntentKind
    command_execution_posture: CommandExecutionPosture
    target_boundary_posture: TargetBoundaryPosture
    target_boundary_refs: list[str] = Field(default_factory=list)
    effect_envelope_needed: bool
    telemetry_needed: bool
    rollback_needed: bool
    required_later_authority_refs: list[str] = Field(default_factory=list)
    required_later_authority_rows: list[RepoRuntimeRequiredLaterAuthorityRow] = Field(
        default_factory=list
    )
    guardrail_refs: list[str] = Field(min_length=1)
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_runtime_request_row(self) -> RepoRuntimePermissionReviewRequestRow:
        _non_empty(self.runtime_review_ref, field_name="runtime_review_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "v76_summary_refs",
            "v76_handoff_refs",
            "v76_closeout_refs",
            "target_boundary_refs",
            "required_later_authority_refs",
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
        if self.command_execution_posture != "no_execution_authorized":
            raise ValueError("V77-A runtime request rows must not authorize command execution")
        if self.required_later_authority_refs and not self.required_later_authority_rows:
            raise ValueError("required later authority refs must resolve to row-shaped records")
        row_refs = {row.authority_requirement_ref for row in self.required_later_authority_rows}
        if set(self.required_later_authority_refs) != row_refs:
            raise ValueError("required later authority refs must match authority rows")
        for row in self.required_later_authority_rows:
            if row.candidate_ref != self.candidate_ref:
                raise ValueError("required later authority rows must match request candidate")
        _reject_runtime_authority_claim(self.limitation_note, field_name="limitation_note")
        if self.runtime_review_posture == "eligible_for_runtime_permission_review":
            if self.requested_permission_horizon in {
                "future_product_review",
                "future_external_branch_review",
            }:
                raise ValueError("product/external pressure is not runtime-ready in V77-A")
            if not self.v76_summary_refs:
                raise ValueError("eligible runtime-review requests require V76 summary refs")
            if not self.v76_handoff_refs:
                raise ValueError("eligible runtime-review requests require V76 handoff refs")
            if not self.v76_closeout_refs:
                raise ValueError("eligible runtime-review requests require V76 closeout refs")
            authority_kinds = {row.authority_kind for row in self.required_later_authority_rows}
            if "runtime_execution_authority" not in authority_kinds:
                raise ValueError(
                    "eligible runtime-review requests require runtime execution authority gap"
                )
        if self.requested_permission_horizon == "future_product_review":
            if self.runtime_review_posture not in {
                "blocked_by_product_authority_gap",
                "future_family_only",
                "rejected_out_of_scope",
            }:
                raise ValueError("product pressure must remain product-blocked in V77-A")
            if not any(
                row.authority_kind == "product_authorization"
                for row in self.required_later_authority_rows
            ):
                raise ValueError("product pressure requires product authority blocker")
        if self.requested_permission_horizon == "future_external_branch_review":
            if self.runtime_review_posture not in {
                "blocked_by_external_branch_gap",
                "future_family_only",
                "rejected_out_of_scope",
            }:
                raise ValueError("external branch pressure must remain blocked in V77-A")
            if not any(
                row.authority_kind == "external_branch_activation"
                for row in self.required_later_authority_rows
            ):
                raise ValueError("external branch pressure requires external authority blocker")
        if (
            self.command_intent_kind != "no_command_intent"
            and self.target_boundary_posture == "target_boundary_missing"
            and not self.target_boundary_refs
        ):
            raise ValueError("command pressure requires target boundary refs or blocker posture")
        return self


class RepoRuntimePermissionReviewRequest(_CartographyBase):
    schema: Literal["repo_runtime_permission_review_request@1"] = (
        REPO_RUNTIME_PERMISSION_REVIEW_REQUEST_SCHEMA
    )
    runtime_permission_review_request_id: str
    runtime_permission_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    request_rows: list[RepoRuntimePermissionReviewRequestRow] = Field(min_length=1)
    runtime_review_boundary_summary: str

    @model_validator(mode="after")
    def _validate_runtime_request(self) -> RepoRuntimePermissionReviewRequest:
        object.__setattr__(
            self,
            "request_rows",
            _sorted_unique_by_ref(
                self.request_rows,
                attr="runtime_review_ref",
                field_name="request_rows",
            ),
        )
        _require_terms(
            self.runtime_review_boundary_summary,
            field_name="runtime_review_boundary_summary",
            terms=("review", "no command", "no runtime permission", "no tool-use", "no release"),
        )
        expected_id = _surface_id(
            "repo_runtime_permission_review_request",
            self.schema,
            self.model_dump(mode="json"),
            "runtime_permission_review_request_id",
        )
        if self.runtime_permission_review_request_id != expected_id:
            raise ValueError(
                "runtime_permission_review_request_id does not match canonical payload hash"
            )
        return self


class RepoRuntimeNonExecutionGuardrailRow(_CartographyBase):
    guardrail_ref: str
    candidate_ref: str
    runtime_review_refs: list[str] = Field(min_length=1)
    forbidden_runtime_actions: list[ForbiddenRuntimeAction] = Field(min_length=1)
    forbidden_downstream_authority: list[ForbiddenDownstreamAuthority] = Field(min_length=1)
    execution_posture: CommandExecutionPosture
    tool_use_posture: RuntimeToolUsePosture
    authority_gap_refs: list[str] = Field(default_factory=list)
    source_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_runtime_guardrail_row(self) -> RepoRuntimeNonExecutionGuardrailRow:
        _non_empty(self.guardrail_ref, field_name="guardrail_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "runtime_review_refs",
            "forbidden_runtime_actions",
            "forbidden_downstream_authority",
            "authority_gap_refs",
            "source_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        missing_actions = _FORBIDDEN_RUNTIME_ACTIONS.difference(self.forbidden_runtime_actions)
        if missing_actions:
            raise ValueError("runtime non-execution guardrail omits forbidden runtime actions")
        missing_authority = _FORBIDDEN_DOWNSTREAM_AUTHORITIES.difference(
            self.forbidden_downstream_authority
        )
        if missing_authority:
            raise ValueError(
                "runtime non-execution guardrail omits forbidden downstream authority"
            )
        if self.execution_posture != "no_execution_authorized":
            raise ValueError("runtime guardrail rows must preserve no-execution posture")
        if self.tool_use_posture != "tool_use_not_authorized_by_v77":
            raise ValueError("V77-A guardrails may not authorize tool use")
        _reject_runtime_authority_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("no command", "no runtime permission", "no tool-use", "no release"),
        )
        return self


class RepoRuntimeNonExecutionGuardrail(_CartographyBase):
    schema: Literal["repo_runtime_non_execution_guardrail@1"] = (
        REPO_RUNTIME_NON_EXECUTION_GUARDRAIL_SCHEMA
    )
    runtime_non_execution_guardrail_id: str
    runtime_permission_review_request_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    guardrail_rows: list[RepoRuntimeNonExecutionGuardrailRow] = Field(min_length=1)
    non_execution_summary: str

    @model_validator(mode="after")
    def _validate_runtime_guardrail(self) -> RepoRuntimeNonExecutionGuardrail:
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
            terms=("no command", "no runtime permission", "no tool-use", "no release"),
        )
        expected_id = _surface_id(
            "repo_runtime_non_execution_guardrail",
            self.schema,
            self.model_dump(mode="json"),
            "runtime_non_execution_guardrail_id",
        )
        if self.runtime_non_execution_guardrail_id != expected_id:
            raise ValueError(
                "runtime_non_execution_guardrail_id does not match canonical payload hash"
            )
        return self


def derive_v77a_repo_runtime_permission_source_index(
    *, repo_root: Path | None = None
) -> RepoRuntimePermissionSourceIndex:
    _ = repo_root
    payload = {
        "schema": REPO_RUNTIME_PERMISSION_SOURCE_INDEX_SCHEMA,
        "runtime_permission_source_index_id": "",
        "review_id": "review:v77a:runtime-permission-review-request",
        "snapshot_id": "vNext+214-closed-on-main",
        "source_set_id": "source-set:v77a:released-v76c-runtime-pressure",
        "source_rows": [
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus214/"
                    "repo_reconciliation_review_summary_v214_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_source_role": "v76_summary_source",
                "source_horizon": "Released V76-C reconciliation review summary rows.",
                "limitation_note": (
                    "Eligibility source for runtime-permission review only; no runtime "
                    "permission is granted."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus214/"
                    "repo_post_reconciliation_handoff_v214_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_source_role": "v76_post_reconciliation_handoff_source",
                "source_horizon": "Released V76-C post-reconciliation handoff rows.",
                "limitation_note": (
                    "Eligibility source for later review requests only; no runtime "
                    "permission is granted."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus214/"
                    "repo_reconciliation_family_closeout_alignment_v214_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_source_role": "v76_family_closeout_source",
                "source_horizon": "Released V76 family closeout alignment rows.",
                "limitation_note": (
                    "Eligibility source for family boundary only; no runtime permission "
                    "is granted."
                ),
            },
            {
                "source_ref": _source_path(
                    "artifacts/agent_harness/v214/evidence_inputs/"
                    "v76c_reconciliation_arbiter_closeout_evidence_v214.json"
                ),
                "source_kind": "evidence_artifact",
                "authority_layer": "support",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_source_role": "support_roadmap_context",
                "source_horizon": "V76-C closeout evidence context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no runtime "
                    "permission is granted."
                ),
            },
            {
                "source_ref": _source_path(
                    "docs/support/arc_series_mapping/"
                    "V68_V69_V70_V71_V72_V73_V74_V75_V76_COMBINED_DOGFOOD_TEST_v0.json"
                ),
                "source_kind": "support_doc",
                "authority_layer": "support",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_source_role": "combined_dogfood_source",
                "source_horizon": "Combined V68-V76 dogfood context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no runtime "
                    "permission is granted."
                ),
            },
        ],
        "runtime_source_summary": (
            "Runtime source rows separate eligibility from context with no prose memory "
            "and no runtime permission."
        ),
    }
    payload["source_rows"] = sorted(payload["source_rows"], key=lambda row: row["source_ref"])
    payload["runtime_permission_source_index_id"] = _surface_id(
        "repo_runtime_permission_source_index",
        REPO_RUNTIME_PERMISSION_SOURCE_INDEX_SCHEMA,
        payload,
        "runtime_permission_source_index_id",
    )
    return RepoRuntimePermissionSourceIndex.model_validate(payload)


def _runtime_authority_rows_for_candidate(
    candidate_ref: str,
) -> list[RepoRuntimeRequiredLaterAuthorityRow]:
    if candidate_ref == "candidate:internal:self_evidencing_workflow_type_emergence":
        rows = [
            {
                "authority_requirement_ref": "authority:v77a:self-evidencing:runtime-execution",
                "candidate_ref": candidate_ref,
                "authority_kind": "runtime_execution_authority",
                "required_before_surface": "before_runtime_permission_review",
                "source_refs": ["docs/LOCKED_CONTINUATION_vNEXT_PLUS215.md"],
                "source_presence_posture": "present",
                "authority_gap_posture": "authority_gap_present",
                "limitation_note": (
                    "Runtime execution authority remains missing before any later review."
                ),
            },
            {
                "authority_requirement_ref": "authority:v77a:self-evidencing:tool-use",
                "candidate_ref": candidate_ref,
                "authority_kind": "tool_use_authority",
                "required_before_surface": "before_tool_use_permission_review",
                "source_refs": ["docs/LOCKED_CONTINUATION_vNEXT_PLUS215.md"],
                "source_presence_posture": "present",
                "authority_gap_posture": "authority_gap_present",
                "limitation_note": "Tool-use authority remains missing before any later review.",
            },
        ]
    elif candidate_ref == "candidate:internal:typed_adjudication_product_wedge":
        rows = [
            {
                "authority_requirement_ref": "authority:v77a:product-wedge:product-review",
                "candidate_ref": candidate_ref,
                "authority_kind": "product_authorization",
                "required_before_surface": "before_product_review",
                "source_refs": ["docs/LOCKED_CONTINUATION_vNEXT_PLUS215.md"],
                "source_presence_posture": "present",
                "authority_gap_posture": "authority_gap_present",
                "limitation_note": (
                    "Product authorization remains missing before any future product review."
                ),
            }
        ]
    elif candidate_ref == "candidate:conditional:v43_external_branch":
        rows = [
            {
                "authority_requirement_ref": "authority:v77a:v43:external-branch",
                "candidate_ref": candidate_ref,
                "authority_kind": "external_branch_activation",
                "required_before_surface": "before_external_branch_review",
                "source_refs": ["docs/LOCKED_CONTINUATION_vNEXT_PLUS215.md"],
                "source_presence_posture": "present",
                "authority_gap_posture": "authority_gap_present",
                "limitation_note": (
                    "External branch activation remains missing before any external review."
                ),
            }
        ]
    else:
        rows = []
    return [RepoRuntimeRequiredLaterAuthorityRow.model_validate(row) for row in rows]


def derive_v77a_repo_runtime_permission_review_request(
    *,
    repo_root: Path | None = None,
    runtime_permission_source_index: RepoRuntimePermissionSourceIndex | None = None,
) -> RepoRuntimePermissionReviewRequest:
    _ = repo_root
    source_index = (
        runtime_permission_source_index or derive_v77a_repo_runtime_permission_source_index()
    )
    eligibility_sources = [
        row.source_ref
        for row in source_index.source_rows
        if row.runtime_source_role in _ELIGIBILITY_SOURCE_ROLES
    ]
    context_sources = [
        row.source_ref
        for row in source_index.source_rows
        if row.runtime_source_role in _CONTEXT_SOURCE_ROLES
    ]
    self_candidate = "candidate:internal:self_evidencing_workflow_type_emergence"
    product_candidate = "candidate:internal:typed_adjudication_product_wedge"
    self_authority_rows = _runtime_authority_rows_for_candidate(self_candidate)
    product_authority_rows = _runtime_authority_rows_for_candidate(product_candidate)
    payload = {
        "schema": REPO_RUNTIME_PERMISSION_REVIEW_REQUEST_SCHEMA,
        "runtime_permission_review_request_id": "",
        "runtime_permission_source_index_id": (
            source_index.runtime_permission_source_index_id
        ),
        "review_id": source_index.review_id,
        "snapshot_id": source_index.snapshot_id,
        "source_set_id": source_index.source_set_id,
        "request_rows": [
            {
                "runtime_review_ref": "runtime-review:v77a:self-evidencing:preflight",
                "candidate_ref": self_candidate,
                "source_refs": sorted([*eligibility_sources, *context_sources]),
                "v76_summary_refs": ["summary:v76c:self-evidencing:later-review"],
                "v76_handoff_refs": [
                    "handoff:v76c:self-evidencing:future-arbiter-review"
                ],
                "v76_closeout_refs": [
                    "repo_reconciliation_family_closeout_alignment_9efc7012032c7b29c3829862"
                ],
                "requested_permission_horizon": "command_preflight_review",
                "runtime_review_posture": "eligible_for_runtime_permission_review",
                "command_intent_kind": "repo_script_pressure",
                "command_execution_posture": "no_execution_authorized",
                "target_boundary_posture": "target_boundary_known",
                "target_boundary_refs": [
                    "packages/adeu_repo_description/src/adeu_repo_description/"
                    "runtime_permission_review.py"
                ],
                "effect_envelope_needed": True,
                "telemetry_needed": True,
                "rollback_needed": True,
                "required_later_authority_refs": [
                    row.authority_requirement_ref for row in self_authority_rows
                ],
                "required_later_authority_rows": [
                    row.model_dump(mode="json") for row in self_authority_rows
                ],
                "guardrail_refs": ["guardrail:v77a:self-evidencing:non-execution"],
                "odeu_lanes": ["deontic", "epistemic", "utility"],
                "limitation_note": (
                    "Eligible for runtime-permission review request only with no command "
                    "execution, no runtime permission, no tool-use permission, and no release."
                ),
            },
            {
                "runtime_review_ref": "runtime-review:v77a:product-wedge:blocked",
                "candidate_ref": product_candidate,
                "source_refs": sorted([*eligibility_sources, *context_sources]),
                "v76_summary_refs": ["summary:v76c:product-wedge:blocked"],
                "v76_handoff_refs": [
                    "handoff:v76c:product-wedge:future-product-review"
                ],
                "v76_closeout_refs": [
                    "repo_reconciliation_family_closeout_alignment_9efc7012032c7b29c3829862"
                ],
                "requested_permission_horizon": "future_product_review",
                "runtime_review_posture": "blocked_by_product_authority_gap",
                "command_intent_kind": "future_family_only",
                "command_execution_posture": "no_execution_authorized",
                "target_boundary_posture": "future_family_only",
                "target_boundary_refs": [],
                "effect_envelope_needed": False,
                "telemetry_needed": False,
                "rollback_needed": False,
                "required_later_authority_refs": [
                    row.authority_requirement_ref for row in product_authority_rows
                ],
                "required_later_authority_rows": [
                    row.model_dump(mode="json") for row in product_authority_rows
                ],
                "guardrail_refs": ["guardrail:v77a:product-wedge:non-execution"],
                "odeu_lanes": ["deontic", "utility"],
                "limitation_note": (
                    "Product pressure remains blocked by later product authority with no "
                    "command execution, no runtime permission, no tool-use, and no release."
                ),
            },
        ],
        "runtime_review_boundary_summary": (
            "Runtime permission review is review only: no command execution, no runtime "
            "permission, no tool-use permission, no product authorization, and no release."
        ),
    }
    payload["request_rows"] = sorted(
        payload["request_rows"],
        key=lambda row: row["runtime_review_ref"],
    )
    payload["runtime_permission_review_request_id"] = _surface_id(
        "repo_runtime_permission_review_request",
        REPO_RUNTIME_PERMISSION_REVIEW_REQUEST_SCHEMA,
        payload,
        "runtime_permission_review_request_id",
    )
    return RepoRuntimePermissionReviewRequest.model_validate(payload)


def derive_v77a_repo_runtime_non_execution_guardrail(
    *,
    repo_root: Path | None = None,
    runtime_permission_review_request: RepoRuntimePermissionReviewRequest | None = None,
) -> RepoRuntimeNonExecutionGuardrail:
    _ = repo_root
    request = (
        runtime_permission_review_request
        or derive_v77a_repo_runtime_permission_review_request()
    )
    grouped_rows: dict[str, dict[str, object]] = {}
    for request_row in request.request_rows:
        guardrail_ref = request_row.guardrail_refs[0]
        existing = grouped_rows.setdefault(
            guardrail_ref,
            {
                "guardrail_ref": guardrail_ref,
                "candidate_ref": request_row.candidate_ref,
                "runtime_review_refs": [],
                "forbidden_runtime_actions": sorted(_FORBIDDEN_RUNTIME_ACTIONS),
                "forbidden_downstream_authority": sorted(_FORBIDDEN_DOWNSTREAM_AUTHORITIES),
                "execution_posture": "no_execution_authorized",
                "tool_use_posture": "tool_use_not_authorized_by_v77",
                "authority_gap_refs": [],
                "source_refs": [],
                "limitation_note": (
                    "This V77-A row is review only: no command execution, no runtime "
                    "permission, no tool-use permission, no product authorization, "
                    "no external branch activation, and no release."
                ),
            },
        )
        if existing["candidate_ref"] != request_row.candidate_ref:
            raise ValueError("runtime guardrail derivation cannot merge multiple candidates")
        existing["runtime_review_refs"] = sorted(
            {
                *existing["runtime_review_refs"],
                request_row.runtime_review_ref,
            }
        )
        existing["authority_gap_refs"] = sorted(
            {
                *existing["authority_gap_refs"],
                *request_row.required_later_authority_refs,
            }
        )
        existing["source_refs"] = sorted({*existing["source_refs"], *request_row.source_refs})
    rows = list(grouped_rows.values())
    payload = {
        "schema": REPO_RUNTIME_NON_EXECUTION_GUARDRAIL_SCHEMA,
        "runtime_non_execution_guardrail_id": "",
        "runtime_permission_review_request_id": (
            request.runtime_permission_review_request_id
        ),
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
        "guardrail_rows": rows,
        "non_execution_summary": (
            "Runtime non-execution guardrails preserve review only: no command execution, "
            "no runtime permission, no tool-use permission, no product authorization, "
            "and no release."
        ),
    }
    payload["guardrail_rows"] = sorted(
        payload["guardrail_rows"],
        key=lambda row: row["guardrail_ref"],
    )
    payload["runtime_non_execution_guardrail_id"] = _surface_id(
        "repo_runtime_non_execution_guardrail",
        REPO_RUNTIME_NON_EXECUTION_GUARDRAIL_SCHEMA,
        payload,
        "runtime_non_execution_guardrail_id",
    )
    return RepoRuntimeNonExecutionGuardrail.model_validate(payload)


def validate_v77a_runtime_permission_review_bundle(
    *,
    runtime_permission_source_index: RepoRuntimePermissionSourceIndex,
    runtime_permission_review_request: RepoRuntimePermissionReviewRequest,
    runtime_non_execution_guardrail: RepoRuntimeNonExecutionGuardrail,
) -> None:
    if (
        runtime_permission_review_request.runtime_permission_source_index_id
        != runtime_permission_source_index.runtime_permission_source_index_id
    ):
        raise ValueError("runtime request must reference the source index")
    if (
        runtime_permission_review_request.review_id,
        runtime_permission_review_request.snapshot_id,
        runtime_permission_review_request.source_set_id,
    ) != (
        runtime_permission_source_index.review_id,
        runtime_permission_source_index.snapshot_id,
        runtime_permission_source_index.source_set_id,
    ):
        raise ValueError("runtime request provenance must match the source index")
    if (
        runtime_non_execution_guardrail.runtime_permission_review_request_id
        != runtime_permission_review_request.runtime_permission_review_request_id
    ):
        raise ValueError("runtime guardrail must reference the request surface")
    if (
        runtime_non_execution_guardrail.review_id,
        runtime_non_execution_guardrail.snapshot_id,
        runtime_non_execution_guardrail.source_set_id,
    ) != (
        runtime_permission_review_request.review_id,
        runtime_permission_review_request.snapshot_id,
        runtime_permission_review_request.source_set_id,
    ):
        raise ValueError("runtime guardrail provenance must match the request surface")

    source_roles = {
        row.source_ref: row.runtime_source_role
        for row in runtime_permission_source_index.source_rows
    }
    known_sources = set(source_roles)
    request_rows = {
        row.runtime_review_ref: row for row in runtime_permission_review_request.request_rows
    }
    guardrail_rows = {
        row.guardrail_ref: row for row in runtime_non_execution_guardrail.guardrail_rows
    }
    for request_row in runtime_permission_review_request.request_rows:
        if any(source_ref not in known_sources for source_ref in request_row.source_refs):
            raise ValueError("runtime request source refs must be known")
        roles = {source_roles[source_ref] for source_ref in request_row.source_refs}
        if request_row.runtime_review_posture == "eligible_for_runtime_permission_review":
            if not _ELIGIBILITY_SOURCE_ROLES.issubset(roles):
                raise ValueError(
                    "eligible runtime-review requests require released V76-C eligibility sources"
                )
            if roles.issubset(_CONTEXT_SOURCE_ROLES):
                raise ValueError("support/context sources are not sufficient for eligibility")
        if request_row.requested_permission_horizon == "future_external_branch_review" and (
            "support_roadmap_context" not in roles
        ):
            raise ValueError("external branch pressure requires explicit context or V43 posture")
        for authority_row in request_row.required_later_authority_rows:
            if any(
                source_ref not in known_sources
                and source_ref != "docs/LOCKED_CONTINUATION_vNEXT_PLUS215.md"
                for source_ref in authority_row.source_refs
            ):
                raise ValueError("runtime authority source refs must be known or lock-bound")
        if any(guardrail_ref not in guardrail_rows for guardrail_ref in request_row.guardrail_refs):
            raise ValueError("runtime request guardrail refs must be known")
        for guardrail_ref in request_row.guardrail_refs:
            guardrail_row = guardrail_rows[guardrail_ref]
            if guardrail_row.candidate_ref != request_row.candidate_ref:
                raise ValueError("runtime request guardrails must match candidate")
            if request_row.runtime_review_ref not in guardrail_row.runtime_review_refs:
                raise ValueError("runtime guardrail rows must reference request rows")
            if set(request_row.required_later_authority_refs) - set(
                guardrail_row.authority_gap_refs
            ):
                raise ValueError("runtime guardrail rows must carry authority gap refs")

    for guardrail_row in runtime_non_execution_guardrail.guardrail_rows:
        if any(source_ref not in known_sources for source_ref in guardrail_row.source_refs):
            raise ValueError("runtime guardrail source refs must be known")
        if any(ref not in request_rows for ref in guardrail_row.runtime_review_refs):
            raise ValueError("guardrail runtime review refs must be known")
        for ref in guardrail_row.runtime_review_refs:
            if request_rows[ref].candidate_ref != guardrail_row.candidate_ref:
                raise ValueError("guardrail runtime refs must match candidate")


def derive_v77a_runtime_permission_review_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoRuntimePermissionSourceIndex,
    RepoRuntimePermissionReviewRequest,
    RepoRuntimeNonExecutionGuardrail,
]:
    source_index = derive_v77a_repo_runtime_permission_source_index(repo_root=repo_root)
    request = derive_v77a_repo_runtime_permission_review_request(
        repo_root=repo_root,
        runtime_permission_source_index=source_index,
    )
    guardrail = derive_v77a_repo_runtime_non_execution_guardrail(
        repo_root=repo_root,
        runtime_permission_review_request=request,
    )
    validate_v77a_runtime_permission_review_bundle(
        runtime_permission_source_index=source_index,
        runtime_permission_review_request=request,
        runtime_non_execution_guardrail=guardrail,
    )
    return source_index, request, guardrail


class RepoCommandPreflightRow(_CartographyBase):
    preflight_ref: str
    runtime_review_refs: list[str] = Field(min_length=1)
    candidate_ref: str
    command_intent_kind: V77BCommandIntentKind
    command_intent_label: str
    command_ref_posture: CommandRefPosture
    target_boundary_refs: list[str] = Field(default_factory=list)
    target_resolution_kind: TargetResolutionKind
    required_source_refs: list[str] = Field(min_length=1)
    required_authority_refs: list[str] = Field(default_factory=list)
    required_telemetry_refs: list[str] = Field(default_factory=list)
    required_rollback_refs: list[str] = Field(default_factory=list)
    non_execution_guardrail_refs: list[str] = Field(min_length=1)
    preflight_posture: CommandPreflightPosture
    execution_posture: CommandExecutionPosture
    forbidden_inferences: list[ForbiddenRuntimeInference] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_command_preflight_row(self) -> RepoCommandPreflightRow:
        _non_empty(self.preflight_ref, field_name="preflight_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        _reject_v77b_authority_claim(
            self.command_intent_label,
            field_name="command_intent_label",
        )
        _reject_v77b_authority_claim(self.limitation_note, field_name="limitation_note")
        for field_name in (
            "runtime_review_refs",
            "target_boundary_refs",
            "required_source_refs",
            "required_authority_refs",
            "required_telemetry_refs",
            "required_rollback_refs",
            "non_execution_guardrail_refs",
            "forbidden_inferences",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.required_source_refs:
            _repo_ref(source_ref, field_name="required_source_refs")
        for target_ref in self.target_boundary_refs:
            _reject_glob_ref(target_ref, field_name="target_boundary_refs")
            if self.target_resolution_kind != "external_endpoint_ref":
                _repo_ref(target_ref, field_name="target_boundary_refs")
        if self.execution_posture != "no_execution_authorized":
            raise ValueError("V77-B preflight rows must not authorize execution")
        missing = _FORBIDDEN_RUNTIME_INFERENCES.difference(self.forbidden_inferences)
        if missing:
            raise ValueError("command preflight rows must carry all forbidden inferences")
        if (
            self.command_intent_kind != "no_command_intent"
            and self.target_resolution_kind != "no_target_boundary"
            and not self.target_boundary_refs
        ):
            raise ValueError("command preflight target refs are required for command pressure")
        if (
            self.command_intent_kind != "no_command_intent"
            and self.target_resolution_kind == "no_target_boundary"
            and self.preflight_posture
            not in {
                "preflight_blocked_by_target_boundary",
                "preflight_future_family_only",
                "preflight_rejected_out_of_scope",
            }
        ):
            raise ValueError("command pressure without targets must remain blocked or deferred")
        if (
            self.target_resolution_kind == "bounded_package_surface_with_child_refs"
            and not self.target_boundary_refs
        ):
            raise ValueError("bounded package targets require concrete child refs")
        if self.preflight_posture == "preflight_contract_for_review_only":
            if not self.required_telemetry_refs:
                raise ValueError("review-only preflight rows require telemetry refs")
            if not self.required_rollback_refs:
                raise ValueError("review-only preflight rows require rollback refs")
            if not self.required_authority_refs:
                raise ValueError("review-only preflight rows require authority refs")
        return self


class RepoCommandPreflightContract(_CartographyBase):
    schema: Literal["repo_command_preflight_contract@1"] = REPO_COMMAND_PREFLIGHT_CONTRACT_SCHEMA
    command_preflight_contract_id: str
    runtime_permission_review_request_id: str
    runtime_non_execution_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    preflight_rows: list[RepoCommandPreflightRow] = Field(min_length=1)
    preflight_boundary_summary: str

    @model_validator(mode="after")
    def _validate_command_preflight_contract(self) -> RepoCommandPreflightContract:
        object.__setattr__(
            self,
            "preflight_rows",
            _sorted_unique_by_ref(
                self.preflight_rows,
                attr="preflight_ref",
                field_name="preflight_rows",
            ),
        )
        _require_terms(
            self.preflight_boundary_summary,
            field_name="preflight_boundary_summary",
            terms=("review", "no command execution", "no runtime permission"),
        )
        expected_id = _surface_id(
            "repo_command_preflight_contract",
            self.schema,
            self.model_dump(mode="json"),
            "command_preflight_contract_id",
        )
        if self.command_preflight_contract_id != expected_id:
            raise ValueError("command_preflight_contract_id does not match canonical payload hash")
        return self


class RepoActionEffectEnvelopeRow(_CartographyBase):
    effect_envelope_ref: str
    runtime_review_refs: list[str] = Field(min_length=1)
    preflight_refs: list[str] = Field(min_length=1)
    candidate_ref: str
    target_boundary_refs: list[str] = Field(default_factory=list)
    allowed_effect_surface_refs: list[str] = Field(default_factory=list)
    forbidden_effect_surface_refs: list[str] = Field(min_length=1)
    effect_horizon: str
    effect_envelope_posture: EffectEnvelopePosture
    effect_acceptance_posture: EffectAcceptancePosture
    source_refs: list[str] = Field(min_length=1)
    non_execution_guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_action_effect_envelope_row(self) -> RepoActionEffectEnvelopeRow:
        _non_empty(self.effect_envelope_ref, field_name="effect_envelope_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        _non_empty(self.effect_horizon, field_name="effect_horizon")
        _reject_v77b_authority_claim(self.effect_horizon, field_name="effect_horizon")
        _reject_v77b_authority_claim(self.limitation_note, field_name="limitation_note")
        for field_name in (
            "runtime_review_refs",
            "preflight_refs",
            "target_boundary_refs",
            "allowed_effect_surface_refs",
            "forbidden_effect_surface_refs",
            "source_refs",
            "non_execution_guardrail_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        for target_ref in self.target_boundary_refs:
            _reject_glob_ref(target_ref, field_name="target_boundary_refs")
            _repo_ref(target_ref, field_name="target_boundary_refs")
        if (
            self.effect_envelope_posture == "effect_envelope_for_review_only"
            and not self.target_boundary_refs
        ):
            raise ValueError("review-only effect envelopes require target boundary refs")
        if (
            self.effect_acceptance_posture == "effect_observed_from_prior_authorized_artifact"
            and "prior authorized" not in self.limitation_note.lower()
        ):
            raise ValueError("observed effect posture requires prior authorized source note")
        if (
            self.effect_acceptance_posture == "effect_observed_from_prior_authorized_artifact"
            and not self.source_refs
        ):
            raise ValueError("observed effect posture requires source refs")
        return self


class RepoActionEffectEnvelope(_CartographyBase):
    schema: Literal["repo_action_effect_envelope@1"] = REPO_ACTION_EFFECT_ENVELOPE_SCHEMA
    action_effect_envelope_id: str
    command_preflight_contract_id: str
    runtime_permission_review_request_id: str
    runtime_non_execution_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    effect_envelope_rows: list[RepoActionEffectEnvelopeRow] = Field(min_length=1)
    effect_boundary_summary: str

    @model_validator(mode="after")
    def _validate_action_effect_envelope(self) -> RepoActionEffectEnvelope:
        object.__setattr__(
            self,
            "effect_envelope_rows",
            _sorted_unique_by_ref(
                self.effect_envelope_rows,
                attr="effect_envelope_ref",
                field_name="effect_envelope_rows",
            ),
        )
        _require_terms(
            self.effect_boundary_summary,
            field_name="effect_boundary_summary",
            terms=("review", "no accepted effect", "no runtime permission"),
        )
        expected_id = _surface_id(
            "repo_action_effect_envelope",
            self.schema,
            self.model_dump(mode="json"),
            "action_effect_envelope_id",
        )
        if self.action_effect_envelope_id != expected_id:
            raise ValueError("action_effect_envelope_id does not match canonical payload hash")
        return self


class RepoRuntimeTelemetryRequirementRow(_CartographyBase):
    telemetry_requirement_ref: str
    runtime_review_refs: list[str] = Field(min_length=1)
    preflight_refs: list[str] = Field(min_length=1)
    effect_envelope_refs: list[str] = Field(min_length=1)
    candidate_ref: str
    telemetry_surface_kind: TelemetrySurfaceKind
    required_telemetry_source_refs: list[str] = Field(default_factory=list)
    checked_source_refs: list[str] = Field(default_factory=list)
    missing_source_refs: list[str] = Field(default_factory=list)
    telemetry_posture: TelemetryPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_runtime_telemetry_requirement_row(self) -> RepoRuntimeTelemetryRequirementRow:
        _non_empty(self.telemetry_requirement_ref, field_name="telemetry_requirement_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        _reject_v77b_authority_claim(self.limitation_note, field_name="limitation_note")
        for field_name in (
            "runtime_review_refs",
            "preflight_refs",
            "effect_envelope_refs",
            "required_telemetry_source_refs",
            "checked_source_refs",
            "missing_source_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.checked_source_refs:
            _repo_ref(source_ref, field_name="checked_source_refs")
        if self.telemetry_posture == "telemetry_required_later" and (
            not self.required_telemetry_source_refs
        ):
            raise ValueError("telemetry required-later rows require telemetry source refs")
        if self.telemetry_posture == "telemetry_source_present_for_prior_artifact" and (
            not self.checked_source_refs
        ):
            raise ValueError("telemetry source-present rows require checked source refs")
        if self.telemetry_posture == "telemetry_missing_expected_source" and (
            not self.missing_source_refs
        ):
            raise ValueError("missing telemetry rows require missing source refs")
        return self


class RepoRuntimeTelemetryRequirement(_CartographyBase):
    schema: Literal["repo_runtime_telemetry_requirement@1"] = (
        REPO_RUNTIME_TELEMETRY_REQUIREMENT_SCHEMA
    )
    runtime_telemetry_requirement_id: str
    command_preflight_contract_id: str
    action_effect_envelope_id: str
    runtime_permission_review_request_id: str
    runtime_non_execution_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    telemetry_requirement_rows: list[RepoRuntimeTelemetryRequirementRow] = Field(min_length=1)
    telemetry_boundary_summary: str

    @model_validator(mode="after")
    def _validate_runtime_telemetry_requirement(self) -> RepoRuntimeTelemetryRequirement:
        object.__setattr__(
            self,
            "telemetry_requirement_rows",
            _sorted_unique_by_ref(
                self.telemetry_requirement_rows,
                attr="telemetry_requirement_ref",
                field_name="telemetry_requirement_rows",
            ),
        )
        _require_terms(
            self.telemetry_boundary_summary,
            field_name="telemetry_boundary_summary",
            terms=("requirement", "not observed telemetry", "no runtime permission"),
        )
        expected_id = _surface_id(
            "repo_runtime_telemetry_requirement",
            self.schema,
            self.model_dump(mode="json"),
            "runtime_telemetry_requirement_id",
        )
        if self.runtime_telemetry_requirement_id != expected_id:
            raise ValueError(
                "runtime_telemetry_requirement_id does not match canonical payload hash"
            )
        return self


class RepoRuntimeRollbackContractRow(_CartographyBase):
    rollback_contract_ref: str
    runtime_review_refs: list[str] = Field(min_length=1)
    preflight_refs: list[str] = Field(min_length=1)
    effect_envelope_refs: list[str] = Field(min_length=1)
    candidate_ref: str
    rollback_surface_kind: RollbackSurfaceKind
    required_rollback_source_refs: list[str] = Field(default_factory=list)
    rollback_posture: RollbackPosture
    blocking_gap_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_runtime_rollback_contract_row(self) -> RepoRuntimeRollbackContractRow:
        _non_empty(self.rollback_contract_ref, field_name="rollback_contract_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        _reject_v77b_authority_claim(self.limitation_note, field_name="limitation_note")
        for field_name in (
            "runtime_review_refs",
            "preflight_refs",
            "effect_envelope_refs",
            "required_rollback_source_refs",
            "blocking_gap_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        if self.rollback_posture == "rollback_required_later" and (
            not self.required_rollback_source_refs
        ):
            raise ValueError("rollback required-later rows require rollback source refs")
        if self.rollback_posture == "rollback_source_present_for_prior_artifact" and (
            not self.required_rollback_source_refs
        ):
            raise ValueError("rollback source-present rows require rollback source refs")
        if self.rollback_posture == "rollback_blocked" and not self.blocking_gap_refs:
            raise ValueError("rollback blocked rows require blocking gap refs")
        return self


class RepoRuntimeRollbackContract(_CartographyBase):
    schema: Literal["repo_runtime_rollback_contract@1"] = REPO_RUNTIME_ROLLBACK_CONTRACT_SCHEMA
    runtime_rollback_contract_id: str
    command_preflight_contract_id: str
    action_effect_envelope_id: str
    runtime_permission_review_request_id: str
    runtime_non_execution_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    rollback_contract_rows: list[RepoRuntimeRollbackContractRow] = Field(min_length=1)
    rollback_boundary_summary: str

    @model_validator(mode="after")
    def _validate_runtime_rollback_contract(self) -> RepoRuntimeRollbackContract:
        object.__setattr__(
            self,
            "rollback_contract_rows",
            _sorted_unique_by_ref(
                self.rollback_contract_rows,
                attr="rollback_contract_ref",
                field_name="rollback_contract_rows",
            ),
        )
        _require_terms(
            self.rollback_boundary_summary,
            field_name="rollback_boundary_summary",
            terms=("requirement", "not rollback verification", "no runtime permission"),
        )
        expected_id = _surface_id(
            "repo_runtime_rollback_contract",
            self.schema,
            self.model_dump(mode="json"),
            "runtime_rollback_contract_id",
        )
        if self.runtime_rollback_contract_id != expected_id:
            raise ValueError("runtime_rollback_contract_id does not match canonical payload hash")
        return self


def _v77b_command_kind_from_v77a(kind: CommandIntentKind) -> V77BCommandIntentKind:
    mapping: dict[str, V77BCommandIntentKind] = {
        "no_command_intent": "no_command_intent",
        "shell_command_pressure": "shell_command_later_review",
        "python_tool_pressure": "python_tool_later_review",
        "repo_script_pressure": "repo_script_later_review",
        "api_call_pressure": "api_call_later_review",
        "external_tool_pressure": "external_tool_later_review",
        "future_family_only": "future_family_only",
    }
    return mapping[kind]


def derive_v77b_repo_command_preflight_contract(
    *,
    repo_root: Path | None = None,
    runtime_permission_review_request: RepoRuntimePermissionReviewRequest | None = None,
    runtime_non_execution_guardrail: RepoRuntimeNonExecutionGuardrail | None = None,
) -> RepoCommandPreflightContract:
    _ = repo_root
    request = (
        runtime_permission_review_request
        or derive_v77a_repo_runtime_permission_review_request()
    )
    guardrail = (
        runtime_non_execution_guardrail
        or derive_v77a_repo_runtime_non_execution_guardrail(
            runtime_permission_review_request=request
        )
    )
    rows = []
    for request_row in request.request_rows:
        review_only = (
            request_row.runtime_review_posture == "eligible_for_runtime_permission_review"
        )
        rows.append(
            {
                "preflight_ref": request_row.runtime_review_ref.replace(
                    "runtime-review:v77a",
                    "preflight:v77b",
                ),
                "runtime_review_refs": [request_row.runtime_review_ref],
                "candidate_ref": request_row.candidate_ref,
                "command_intent_kind": _v77b_command_kind_from_v77a(
                    request_row.command_intent_kind
                ),
                "command_intent_label": (
                    "Repo-description implementation review pressure only"
                    if review_only
                    else "Future-family product review pressure only"
                ),
                "command_ref_posture": (
                    "script_label_review_only" if review_only else "future_family_only"
                ),
                "target_boundary_refs": request_row.target_boundary_refs,
                "target_resolution_kind": (
                    "concrete_file_ref"
                    if request_row.target_boundary_refs
                    else "no_target_boundary"
                ),
                "required_source_refs": request_row.source_refs,
                "required_authority_refs": request_row.required_later_authority_refs,
                "required_telemetry_refs": (
                    ["telemetry:v77b:self-evidencing:required"] if review_only else []
                ),
                "required_rollback_refs": (
                    ["rollback:v77b:self-evidencing:required"] if review_only else []
                ),
                "non_execution_guardrail_refs": request_row.guardrail_refs,
                "preflight_posture": (
                    "preflight_contract_for_review_only"
                    if review_only
                    else "preflight_future_family_only"
                ),
                "execution_posture": "no_execution_authorized",
                "forbidden_inferences": sorted(_FORBIDDEN_RUNTIME_INFERENCES),
                "limitation_note": (
                    "Preflight contract is review only with no command execution, "
                    "no runtime permission, no tool-use permission, and no release."
                ),
            }
        )
    payload = {
        "schema": REPO_COMMAND_PREFLIGHT_CONTRACT_SCHEMA,
        "command_preflight_contract_id": "",
        "runtime_permission_review_request_id": (
            request.runtime_permission_review_request_id
        ),
        "runtime_non_execution_guardrail_id": (
            guardrail.runtime_non_execution_guardrail_id
        ),
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
        "preflight_rows": sorted(rows, key=lambda row: row["preflight_ref"]),
        "preflight_boundary_summary": (
            "Command preflight is review only with no command execution and no runtime "
            "permission."
        ),
    }
    payload["command_preflight_contract_id"] = _surface_id(
        "repo_command_preflight_contract",
        REPO_COMMAND_PREFLIGHT_CONTRACT_SCHEMA,
        payload,
        "command_preflight_contract_id",
    )
    return RepoCommandPreflightContract.model_validate(payload)


def derive_v77b_repo_action_effect_envelope(
    *,
    repo_root: Path | None = None,
    command_preflight_contract: RepoCommandPreflightContract | None = None,
) -> RepoActionEffectEnvelope:
    _ = repo_root
    preflight = command_preflight_contract or derive_v77b_repo_command_preflight_contract()
    rows = []
    for preflight_row in preflight.preflight_rows:
        review_only = preflight_row.preflight_posture == "preflight_contract_for_review_only"
        rows.append(
            {
                "effect_envelope_ref": preflight_row.preflight_ref.replace(
                    "preflight:v77b",
                    "effect-envelope:v77b",
                ),
                "runtime_review_refs": preflight_row.runtime_review_refs,
                "preflight_refs": [preflight_row.preflight_ref],
                "candidate_ref": preflight_row.candidate_ref,
                "target_boundary_refs": preflight_row.target_boundary_refs,
                "allowed_effect_surface_refs": (
                    ["effect:v77b:self-evidencing:schema-review-only"] if review_only else []
                ),
                "forbidden_effect_surface_refs": [
                    "effect:v77b:accepted-repository-truth",
                    "effect:v77b:command-execution",
                    "effect:v77b:runtime-permission-grant",
                ],
                "effect_horizon": (
                    "Review-only schema, fixture, and test effect horizon"
                    if review_only
                    else "Future-family product effect horizon"
                ),
                "effect_envelope_posture": (
                    "effect_envelope_for_review_only"
                    if review_only
                    else "effect_envelope_future_family_only"
                ),
                "effect_acceptance_posture": "no_effect_accepted",
                "source_refs": preflight_row.required_source_refs,
                "non_execution_guardrail_refs": preflight_row.non_execution_guardrail_refs,
                "limitation_note": (
                    "Action-effect envelope is review only with no accepted effect, "
                    "no command execution, and no runtime permission."
                ),
            }
        )
    payload = {
        "schema": REPO_ACTION_EFFECT_ENVELOPE_SCHEMA,
        "action_effect_envelope_id": "",
        "command_preflight_contract_id": preflight.command_preflight_contract_id,
        "runtime_permission_review_request_id": (
            preflight.runtime_permission_review_request_id
        ),
        "runtime_non_execution_guardrail_id": (
            preflight.runtime_non_execution_guardrail_id
        ),
        "review_id": preflight.review_id,
        "snapshot_id": preflight.snapshot_id,
        "source_set_id": preflight.source_set_id,
        "effect_envelope_rows": sorted(rows, key=lambda row: row["effect_envelope_ref"]),
        "effect_boundary_summary": (
            "Action-effect envelopes are review objects with no accepted effect and no "
            "runtime permission."
        ),
    }
    payload["action_effect_envelope_id"] = _surface_id(
        "repo_action_effect_envelope",
        REPO_ACTION_EFFECT_ENVELOPE_SCHEMA,
        payload,
        "action_effect_envelope_id",
    )
    return RepoActionEffectEnvelope.model_validate(payload)


def derive_v77b_repo_runtime_telemetry_requirement(
    *,
    repo_root: Path | None = None,
    command_preflight_contract: RepoCommandPreflightContract | None = None,
    action_effect_envelope: RepoActionEffectEnvelope | None = None,
) -> RepoRuntimeTelemetryRequirement:
    _ = repo_root
    preflight = command_preflight_contract or derive_v77b_repo_command_preflight_contract()
    envelope = action_effect_envelope or derive_v77b_repo_action_effect_envelope(
        command_preflight_contract=preflight
    )
    envelope_by_preflight = {
        row.preflight_refs[0]: row for row in envelope.effect_envelope_rows
    }
    rows = []
    for preflight_row in preflight.preflight_rows:
        review_only = preflight_row.preflight_posture == "preflight_contract_for_review_only"
        rows.append(
            {
                "telemetry_requirement_ref": (
                    preflight_row.required_telemetry_refs[0]
                    if preflight_row.required_telemetry_refs
                    else preflight_row.preflight_ref.replace(
                        "preflight:v77b",
                        "telemetry:v77b",
                    )
                ),
                "runtime_review_refs": preflight_row.runtime_review_refs,
                "preflight_refs": [preflight_row.preflight_ref],
                "effect_envelope_refs": [
                    envelope_by_preflight[preflight_row.preflight_ref].effect_envelope_ref
                ],
                "candidate_ref": preflight_row.candidate_ref,
                "telemetry_surface_kind": (
                    "test_result_telemetry" if review_only else "not_applicable"
                ),
                "required_telemetry_source_refs": (
                    ["telemetry-source:v77b:self-evidencing:future-test-output"]
                    if review_only
                    else []
                ),
                "checked_source_refs": [],
                "missing_source_refs": (
                    ["telemetry-source:v77b:self-evidencing:future-test-output"]
                    if review_only
                    else []
                ),
                "telemetry_posture": (
                    "telemetry_required_later" if review_only else "telemetry_future_family_only"
                ),
                "limitation_note": (
                    "Telemetry is required later and is not observed telemetry; no runtime "
                    "permission is granted."
                    if review_only
                    else "Telemetry is future-family only and not observed telemetry; no runtime "
                    "permission is granted."
                ),
            }
        )
    payload = {
        "schema": REPO_RUNTIME_TELEMETRY_REQUIREMENT_SCHEMA,
        "runtime_telemetry_requirement_id": "",
        "command_preflight_contract_id": preflight.command_preflight_contract_id,
        "action_effect_envelope_id": envelope.action_effect_envelope_id,
        "runtime_permission_review_request_id": (
            preflight.runtime_permission_review_request_id
        ),
        "runtime_non_execution_guardrail_id": (
            preflight.runtime_non_execution_guardrail_id
        ),
        "review_id": preflight.review_id,
        "snapshot_id": preflight.snapshot_id,
        "source_set_id": preflight.source_set_id,
        "telemetry_requirement_rows": sorted(
            rows,
            key=lambda row: row["telemetry_requirement_ref"],
        ),
        "telemetry_boundary_summary": (
            "Runtime telemetry rows are requirements, not observed telemetry, and no "
            "runtime permission is granted."
        ),
    }
    payload["runtime_telemetry_requirement_id"] = _surface_id(
        "repo_runtime_telemetry_requirement",
        REPO_RUNTIME_TELEMETRY_REQUIREMENT_SCHEMA,
        payload,
        "runtime_telemetry_requirement_id",
    )
    return RepoRuntimeTelemetryRequirement.model_validate(payload)


def derive_v77b_repo_runtime_rollback_contract(
    *,
    repo_root: Path | None = None,
    command_preflight_contract: RepoCommandPreflightContract | None = None,
    action_effect_envelope: RepoActionEffectEnvelope | None = None,
) -> RepoRuntimeRollbackContract:
    _ = repo_root
    preflight = command_preflight_contract or derive_v77b_repo_command_preflight_contract()
    envelope = action_effect_envelope or derive_v77b_repo_action_effect_envelope(
        command_preflight_contract=preflight
    )
    envelope_by_preflight = {
        row.preflight_refs[0]: row for row in envelope.effect_envelope_rows
    }
    rows = []
    for preflight_row in preflight.preflight_rows:
        review_only = preflight_row.preflight_posture == "preflight_contract_for_review_only"
        rows.append(
            {
                "rollback_contract_ref": (
                    preflight_row.required_rollback_refs[0]
                    if preflight_row.required_rollback_refs
                    else preflight_row.preflight_ref.replace(
                        "preflight:v77b",
                        "rollback:v77b",
                    )
                ),
                "runtime_review_refs": preflight_row.runtime_review_refs,
                "preflight_refs": [preflight_row.preflight_ref],
                "effect_envelope_refs": [
                    envelope_by_preflight[preflight_row.preflight_ref].effect_envelope_ref
                ],
                "candidate_ref": preflight_row.candidate_ref,
                "rollback_surface_kind": (
                    "source_revert_plan" if review_only else "not_applicable"
                ),
                "required_rollback_source_refs": (
                    ["rollback-source:v77b:self-evidencing:future-clean-revert"]
                    if review_only
                    else []
                ),
                "rollback_posture": (
                    "rollback_required_later" if review_only else "rollback_future_family_only"
                ),
                "blocking_gap_refs": [],
                "limitation_note": (
                    "Rollback is required later and is not rollback verification; no runtime "
                    "permission is granted."
                    if review_only
                    else "Rollback is future-family only and not rollback verification; no "
                    "runtime permission is granted."
                ),
            }
        )
    payload = {
        "schema": REPO_RUNTIME_ROLLBACK_CONTRACT_SCHEMA,
        "runtime_rollback_contract_id": "",
        "command_preflight_contract_id": preflight.command_preflight_contract_id,
        "action_effect_envelope_id": envelope.action_effect_envelope_id,
        "runtime_permission_review_request_id": (
            preflight.runtime_permission_review_request_id
        ),
        "runtime_non_execution_guardrail_id": (
            preflight.runtime_non_execution_guardrail_id
        ),
        "review_id": preflight.review_id,
        "snapshot_id": preflight.snapshot_id,
        "source_set_id": preflight.source_set_id,
        "rollback_contract_rows": sorted(rows, key=lambda row: row["rollback_contract_ref"]),
        "rollback_boundary_summary": (
            "Runtime rollback rows are requirements, not rollback verification, and no "
            "runtime permission is granted."
        ),
    }
    payload["runtime_rollback_contract_id"] = _surface_id(
        "repo_runtime_rollback_contract",
        REPO_RUNTIME_ROLLBACK_CONTRACT_SCHEMA,
        payload,
        "runtime_rollback_contract_id",
    )
    return RepoRuntimeRollbackContract.model_validate(payload)


def validate_v77b_runtime_preflight_bundle(
    *,
    runtime_permission_review_request: RepoRuntimePermissionReviewRequest,
    runtime_non_execution_guardrail: RepoRuntimeNonExecutionGuardrail,
    command_preflight_contract: RepoCommandPreflightContract,
    action_effect_envelope: RepoActionEffectEnvelope,
    runtime_telemetry_requirement: RepoRuntimeTelemetryRequirement,
    runtime_rollback_contract: RepoRuntimeRollbackContract,
) -> None:
    if (
        command_preflight_contract.runtime_permission_review_request_id
        != runtime_permission_review_request.runtime_permission_review_request_id
    ):
        raise ValueError("command preflight must reference V77-A request surface")
    if (
        command_preflight_contract.runtime_non_execution_guardrail_id
        != runtime_non_execution_guardrail.runtime_non_execution_guardrail_id
    ):
        raise ValueError("command preflight must reference V77-A guardrail surface")
    for surface_name, surface in (
        ("effect envelope", action_effect_envelope),
        ("telemetry requirement", runtime_telemetry_requirement),
        ("rollback contract", runtime_rollback_contract),
    ):
        if surface.command_preflight_contract_id != (
            command_preflight_contract.command_preflight_contract_id
        ):
            raise ValueError(f"{surface_name} must reference command preflight surface")
        if surface.runtime_permission_review_request_id != (
            runtime_permission_review_request.runtime_permission_review_request_id
        ):
            raise ValueError(f"{surface_name} must reference V77-A request surface")
        if surface.runtime_non_execution_guardrail_id != (
            runtime_non_execution_guardrail.runtime_non_execution_guardrail_id
        ):
            raise ValueError(f"{surface_name} must reference V77-A guardrail surface")
        if (
            surface.review_id,
            surface.snapshot_id,
            surface.source_set_id,
        ) != (
            command_preflight_contract.review_id,
            command_preflight_contract.snapshot_id,
            command_preflight_contract.source_set_id,
        ):
            raise ValueError(f"{surface_name} provenance must match command preflight")

    request_rows = {
        row.runtime_review_ref: row for row in runtime_permission_review_request.request_rows
    }
    guardrail_rows = {
        row.guardrail_ref: row for row in runtime_non_execution_guardrail.guardrail_rows
    }
    preflight_rows = {
        row.preflight_ref: row for row in command_preflight_contract.preflight_rows
    }
    effect_rows = {
        row.effect_envelope_ref: row for row in action_effect_envelope.effect_envelope_rows
    }
    for preflight_row in command_preflight_contract.preflight_rows:
        for review_ref in preflight_row.runtime_review_refs:
            if review_ref not in request_rows:
                raise ValueError("preflight runtime review refs must be known V77-A refs")
            if request_rows[review_ref].candidate_ref != preflight_row.candidate_ref:
                raise ValueError("preflight rows must match request candidate")
        for guardrail_ref in preflight_row.non_execution_guardrail_refs:
            if guardrail_ref not in guardrail_rows:
                raise ValueError("preflight guardrail refs must be known V77-A refs")
            if guardrail_rows[guardrail_ref].candidate_ref != preflight_row.candidate_ref:
                raise ValueError("preflight guardrails must match candidate")
    for effect_row in action_effect_envelope.effect_envelope_rows:
        for preflight_ref in effect_row.preflight_refs:
            if preflight_ref not in preflight_rows:
                raise ValueError("effect envelope preflight refs must be known")
            if preflight_rows[preflight_ref].candidate_ref != effect_row.candidate_ref:
                raise ValueError("effect envelope rows must match preflight candidate")
        for guardrail_ref in effect_row.non_execution_guardrail_refs:
            if guardrail_ref not in guardrail_rows:
                raise ValueError("effect envelope guardrail refs must be known")
            if guardrail_rows[guardrail_ref].candidate_ref != effect_row.candidate_ref:
                raise ValueError("effect envelope guardrails must match candidate")
    for telemetry_row in runtime_telemetry_requirement.telemetry_requirement_rows:
        for preflight_ref in telemetry_row.preflight_refs:
            if preflight_ref not in preflight_rows:
                raise ValueError("telemetry preflight refs must be known")
            if preflight_rows[preflight_ref].candidate_ref != telemetry_row.candidate_ref:
                raise ValueError("telemetry rows must match preflight candidate")
        for effect_ref in telemetry_row.effect_envelope_refs:
            if effect_ref not in effect_rows:
                raise ValueError("telemetry effect envelope refs must be known")
            if effect_rows[effect_ref].candidate_ref != telemetry_row.candidate_ref:
                raise ValueError("telemetry rows must match effect candidate")
    for rollback_row in runtime_rollback_contract.rollback_contract_rows:
        for preflight_ref in rollback_row.preflight_refs:
            if preflight_ref not in preflight_rows:
                raise ValueError("rollback preflight refs must be known")
            if preflight_rows[preflight_ref].candidate_ref != rollback_row.candidate_ref:
                raise ValueError("rollback rows must match preflight candidate")
        for effect_ref in rollback_row.effect_envelope_refs:
            if effect_ref not in effect_rows:
                raise ValueError("rollback effect envelope refs must be known")
            if effect_rows[effect_ref].candidate_ref != rollback_row.candidate_ref:
                raise ValueError("rollback rows must match effect candidate")


def derive_v77b_runtime_preflight_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoCommandPreflightContract,
    RepoActionEffectEnvelope,
    RepoRuntimeTelemetryRequirement,
    RepoRuntimeRollbackContract,
]:
    _, request, guardrail = derive_v77a_runtime_permission_review_bundle(repo_root=repo_root)
    preflight = derive_v77b_repo_command_preflight_contract(
        repo_root=repo_root,
        runtime_permission_review_request=request,
        runtime_non_execution_guardrail=guardrail,
    )
    envelope = derive_v77b_repo_action_effect_envelope(
        repo_root=repo_root,
        command_preflight_contract=preflight,
    )
    telemetry = derive_v77b_repo_runtime_telemetry_requirement(
        repo_root=repo_root,
        command_preflight_contract=preflight,
        action_effect_envelope=envelope,
    )
    rollback = derive_v77b_repo_runtime_rollback_contract(
        repo_root=repo_root,
        command_preflight_contract=preflight,
        action_effect_envelope=envelope,
    )
    validate_v77b_runtime_preflight_bundle(
        runtime_permission_review_request=request,
        runtime_non_execution_guardrail=guardrail,
        command_preflight_contract=preflight,
        action_effect_envelope=envelope,
        runtime_telemetry_requirement=telemetry,
        runtime_rollback_contract=rollback,
    )
    return preflight, envelope, telemetry, rollback


class RepoRuntimePermissionAuthorityPostureRow(_CartographyBase):
    authority_posture_ref: str
    runtime_review_refs: list[str] = Field(min_length=1)
    preflight_refs: list[str] = Field(default_factory=list)
    effect_envelope_refs: list[str] = Field(default_factory=list)
    telemetry_requirement_refs: list[str] = Field(default_factory=list)
    rollback_contract_refs: list[str] = Field(default_factory=list)
    candidate_ref: str
    authority_requirement_kind: RuntimePermissionAuthorityRequirementKind
    authority_source_refs: list[str] = Field(min_length=1)
    authority_gap_posture: RuntimePermissionAuthorityGapPosture
    authority_decision_posture: RuntimePermissionAuthorityDecisionPosture
    forbidden_authority_inferences: list[ForbiddenV77CAuthorityInference] = Field(
        min_length=1
    )
    limitation_note: str

    @model_validator(mode="after")
    def _validate_runtime_authority_posture_row(
        self,
    ) -> RepoRuntimePermissionAuthorityPostureRow:
        _non_empty(self.authority_posture_ref, field_name="authority_posture_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        _reject_runtime_authority_claim(self.limitation_note, field_name="limitation_note")
        for field_name in (
            "runtime_review_refs",
            "preflight_refs",
            "effect_envelope_refs",
            "telemetry_requirement_refs",
            "rollback_contract_refs",
            "authority_source_refs",
            "forbidden_authority_inferences",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.authority_source_refs:
            _repo_ref(source_ref, field_name="authority_source_refs")
        missing = _FORBIDDEN_V77C_AUTHORITY_INFERENCES.difference(
            self.forbidden_authority_inferences
        )
        if missing:
            raise ValueError("runtime authority posture omits forbidden authority inferences")
        if self.authority_decision_posture not in {
            "authority_required_later",
            "authority_missing",
            "authority_not_applicable",
            "authority_future_family_only",
            "authority_rejected_out_of_scope",
        }:
            raise ValueError("runtime authority posture may not grant authority")
        if (
            self.authority_requirement_kind
            in {"runtime_permission_authority", "tool_use_authority"}
            and self.authority_decision_posture == "authority_not_applicable"
        ):
            raise ValueError("runtime and tool authority rows must remain required or missing")
        return self


class RepoRuntimePermissionAuthorityPosture(_CartographyBase):
    schema: Literal["repo_runtime_permission_authority_posture@1"] = (
        REPO_RUNTIME_PERMISSION_AUTHORITY_POSTURE_SCHEMA
    )
    runtime_permission_authority_posture_id: str
    runtime_permission_review_request_id: str
    command_preflight_contract_id: str
    action_effect_envelope_id: str
    runtime_telemetry_requirement_id: str
    runtime_rollback_contract_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    authority_posture_rows: list[RepoRuntimePermissionAuthorityPostureRow] = Field(
        min_length=1
    )
    authority_boundary_summary: str

    @model_validator(mode="after")
    def _validate_runtime_authority_posture(
        self,
    ) -> RepoRuntimePermissionAuthorityPosture:
        object.__setattr__(
            self,
            "authority_posture_rows",
            _sorted_unique_by_ref(
                self.authority_posture_rows,
                attr="authority_posture_ref",
                field_name="authority_posture_rows",
            ),
        )
        _require_terms(
            self.authority_boundary_summary,
            field_name="authority_boundary_summary",
            terms=("required", "missing", "no runtime permission", "no tool-use"),
        )
        expected_id = _surface_id(
            "repo_runtime_permission_authority_posture",
            self.schema,
            self.model_dump(mode="json"),
            "runtime_permission_authority_posture_id",
        )
        if self.runtime_permission_authority_posture_id != expected_id:
            raise ValueError(
                "runtime_permission_authority_posture_id does not match canonical payload hash"
            )
        return self


class RepoRuntimePermissionReviewSummaryRow(_CartographyBase):
    runtime_summary_ref: str
    runtime_review_refs: list[str] = Field(min_length=1)
    preflight_refs: list[str] = Field(default_factory=list)
    effect_envelope_refs: list[str] = Field(default_factory=list)
    telemetry_requirement_refs: list[str] = Field(default_factory=list)
    rollback_contract_refs: list[str] = Field(default_factory=list)
    authority_posture_refs: list[str] = Field(min_length=1)
    candidate_ref: str
    summary_posture: RuntimePermissionSummaryPosture
    ready_basis_posture: RuntimePermissionReadyBasisPosture
    carried_blocker_refs: list[str] = Field(default_factory=list)
    non_execution_guardrail: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_runtime_summary_row(self) -> RepoRuntimePermissionReviewSummaryRow:
        _non_empty(self.runtime_summary_ref, field_name="runtime_summary_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        _non_empty(self.non_execution_guardrail, field_name="non_execution_guardrail")
        _reject_runtime_authority_claim(self.limitation_note, field_name="limitation_note")
        for field_name in (
            "runtime_review_refs",
            "preflight_refs",
            "effect_envelope_refs",
            "telemetry_requirement_refs",
            "rollback_contract_refs",
            "authority_posture_refs",
            "carried_blocker_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        if self.summary_posture in {
            "review_ready_no_blockers",
            "review_ready_with_nonblocking_warnings",
        } and self.carried_blocker_refs:
            raise ValueError("runtime summary ready posture cannot carry blockers")
        if self.summary_posture.startswith("blocked_by_") and not self.carried_blocker_refs:
            raise ValueError("blocked runtime summaries require carried blocker refs")
        if self.summary_posture.startswith("review_ready") and (
            self.ready_basis_posture == "not_ready_blockers_remain"
        ):
            raise ValueError("ready runtime summaries cannot carry not-ready basis posture")
        return self


class RepoRuntimePermissionReviewSummary(_CartographyBase):
    schema: Literal["repo_runtime_permission_review_summary@1"] = (
        REPO_RUNTIME_PERMISSION_REVIEW_SUMMARY_SCHEMA
    )
    runtime_permission_review_summary_id: str
    runtime_permission_authority_posture_id: str
    runtime_permission_review_request_id: str
    command_preflight_contract_id: str
    action_effect_envelope_id: str
    runtime_telemetry_requirement_id: str
    runtime_rollback_contract_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    summary_rows: list[RepoRuntimePermissionReviewSummaryRow] = Field(min_length=1)
    runtime_summary_boundary: str

    @model_validator(mode="after")
    def _validate_runtime_review_summary(self) -> RepoRuntimePermissionReviewSummary:
        object.__setattr__(
            self,
            "summary_rows",
            _sorted_unique_by_ref(
                self.summary_rows,
                attr="runtime_summary_ref",
                field_name="summary_rows",
            ),
        )
        _require_terms(
            self.runtime_summary_boundary,
            field_name="runtime_summary_boundary",
            terms=("summary", "blocker", "no runtime permission", "no command"),
        )
        expected_id = _surface_id(
            "repo_runtime_permission_review_summary",
            self.schema,
            self.model_dump(mode="json"),
            "runtime_permission_review_summary_id",
        )
        if self.runtime_permission_review_summary_id != expected_id:
            raise ValueError(
                "runtime_permission_review_summary_id does not match canonical payload hash"
            )
        return self


class RepoPostRuntimePermissionReviewHandoffRow(_CartographyBase):
    handoff_ref: str
    runtime_summary_refs: list[str] = Field(min_length=1)
    runtime_review_refs: list[str] = Field(min_length=1)
    authority_posture_refs: list[str] = Field(min_length=1)
    carried_gap_refs: list[str] = Field(default_factory=list)
    handoff_target: PostRuntimePermissionReviewHandoffTarget
    handoff_subject_horizon: str
    handoff_posture: PostRuntimePermissionReviewHandoffPosture
    required_later_authority_refs: list[str] = Field(default_factory=list)
    required_later_authority_kinds: list[RuntimePermissionAuthorityRequirementKind] = Field(
        default_factory=list
    )
    non_execution_guardrail: str
    runtime_permission_execution_posture: RuntimePermissionExecutionPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_post_runtime_handoff_row(
        self,
    ) -> RepoPostRuntimePermissionReviewHandoffRow:
        _non_empty(self.handoff_ref, field_name="handoff_ref")
        _non_empty(self.handoff_subject_horizon, field_name="handoff_subject_horizon")
        _non_empty(self.non_execution_guardrail, field_name="non_execution_guardrail")
        _reject_runtime_authority_claim(self.limitation_note, field_name="limitation_note")
        for field_name in (
            "runtime_summary_refs",
            "runtime_review_refs",
            "authority_posture_refs",
            "carried_gap_refs",
            "required_later_authority_refs",
            "required_later_authority_kinds",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        if (
            self.runtime_permission_execution_posture
            != "no_runtime_permission_granted_by_v77"
        ):
            raise ValueError("post-runtime handoffs must not grant runtime permission")
        if self.handoff_posture == "ready_for_later_review" and self.carried_gap_refs:
            raise ValueError("ready post-runtime handoffs cannot carry blocking gaps")
        target_required: dict[str, RuntimePermissionAuthorityRequirementKind] = {
            "future_runtime_execution_authority_review": "runtime_permission_authority",
            "future_tool_use_permission_review": "tool_use_authority",
            "future_product_review": "product_authorization",
            "future_external_branch_review": "external_branch_activation",
        }
        required_kind = target_required.get(self.handoff_target)
        if required_kind is not None and required_kind not in self.required_later_authority_kinds:
            raise ValueError("post-runtime handoff target requires matching authority kind")
        if self.required_later_authority_refs and not self.required_later_authority_kinds:
            raise ValueError("required later authority refs require authority kinds")
        return self


class RepoPostRuntimePermissionReviewHandoff(_CartographyBase):
    schema: Literal["repo_post_runtime_permission_review_handoff@1"] = (
        REPO_POST_RUNTIME_PERMISSION_REVIEW_HANDOFF_SCHEMA
    )
    post_runtime_permission_review_handoff_id: str
    runtime_permission_review_summary_id: str
    runtime_permission_authority_posture_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    handoff_rows: list[RepoPostRuntimePermissionReviewHandoffRow] = Field(min_length=1)
    handoff_boundary_summary: str

    @model_validator(mode="after")
    def _validate_post_runtime_handoff(self) -> RepoPostRuntimePermissionReviewHandoff:
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
            self.handoff_boundary_summary,
            field_name="handoff_boundary_summary",
            terms=("request", "no runtime permission", "no target family"),
        )
        expected_id = _surface_id(
            "repo_post_runtime_permission_review_handoff",
            self.schema,
            self.model_dump(mode="json"),
            "post_runtime_permission_review_handoff_id",
        )
        if self.post_runtime_permission_review_handoff_id != expected_id:
            raise ValueError(
                "post_runtime_permission_review_handoff_id does not match canonical payload hash"
            )
        return self


class RepoRuntimePermissionFamilyCloseoutAlignmentRow(_CartographyBase):
    family: Literal["V77"]
    closed_slice_ladder: list[Literal["V77-A", "V77-B", "V77-C"]] = Field(min_length=3)
    closed_by_arc: Literal["vNext+217"]
    consumed_source_families: list[str] = Field(min_length=1)
    shipped_record_shapes: list[str] = Field(min_length=1)
    runtime_authority_boundary: str
    future_family_authority: str
    unselected_future_surfaces: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_runtime_family_closeout_row(
        self,
    ) -> RepoRuntimePermissionFamilyCloseoutAlignmentRow:
        object.__setattr__(
            self,
            "closed_slice_ladder",
            _sorted_unique(self.closed_slice_ladder, field_name="closed_slice_ladder"),
        )
        object.__setattr__(
            self,
            "consumed_source_families",
            _sorted_unique(self.consumed_source_families, field_name="consumed_source_families"),
        )
        object.__setattr__(
            self,
            "shipped_record_shapes",
            _sorted_unique(self.shipped_record_shapes, field_name="shipped_record_shapes"),
        )
        object.__setattr__(
            self,
            "unselected_future_surfaces",
            _sorted_unique(
                self.unselected_future_surfaces,
                field_name="unselected_future_surfaces",
            ),
        )
        if self.closed_slice_ladder != ["V77-A", "V77-B", "V77-C"]:
            raise ValueError("runtime closeout must close exactly V77-A, V77-B, and V77-C")
        _require_terms(
            self.runtime_authority_boundary,
            field_name="runtime_authority_boundary",
            terms=("review", "no runtime permission", "no command"),
        )
        _require_terms(
            self.future_family_authority,
            field_name="future_family_authority",
            terms=("future", "not selected"),
        )
        _reject_runtime_authority_claim(self.limitation_note, field_name="limitation_note")
        if "v78 selected" in self.future_family_authority.lower():
            raise ValueError("runtime closeout must not select V78")
        return self


class RepoRuntimePermissionFamilyCloseoutAlignment(_CartographyBase):
    schema: Literal["repo_runtime_permission_family_closeout_alignment@1"] = (
        REPO_RUNTIME_PERMISSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
    )
    runtime_permission_family_closeout_alignment_id: str
    runtime_permission_review_summary_id: str
    post_runtime_permission_review_handoff_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    closeout_rows: list[RepoRuntimePermissionFamilyCloseoutAlignmentRow] = Field(
        min_length=1
    )
    closeout_boundary_summary: str

    @model_validator(mode="after")
    def _validate_runtime_family_closeout(
        self,
    ) -> RepoRuntimePermissionFamilyCloseoutAlignment:
        object.__setattr__(
            self,
            "closeout_rows",
            _sorted_unique_by_ref(self.closeout_rows, attr="family", field_name="closeout_rows"),
        )
        _require_terms(
            self.closeout_boundary_summary,
            field_name="closeout_boundary_summary",
            terms=("v77", "review", "no runtime permission", "not selected"),
        )
        expected_id = _surface_id(
            "repo_runtime_permission_family_closeout_alignment",
            self.schema,
            self.model_dump(mode="json"),
            "runtime_permission_family_closeout_alignment_id",
        )
        if self.runtime_permission_family_closeout_alignment_id != expected_id:
            raise ValueError(
                "runtime_permission_family_closeout_alignment_id does not match "
                "canonical payload hash"
            )
        return self


def _v77c_authority_kind_for_v77a_ref(
    authority_ref: str,
) -> RuntimePermissionAuthorityRequirementKind:
    if "tool-use" in authority_ref:
        return "tool_use_authority"
    if "product" in authority_ref:
        return "product_authorization"
    if "external" in authority_ref:
        return "external_branch_activation"
    return "runtime_permission_authority"


def derive_v77c_repo_runtime_permission_authority_posture(
    *,
    repo_root: Path | None = None,
    runtime_permission_review_request: RepoRuntimePermissionReviewRequest | None = None,
    command_preflight_contract: RepoCommandPreflightContract | None = None,
    action_effect_envelope: RepoActionEffectEnvelope | None = None,
    runtime_telemetry_requirement: RepoRuntimeTelemetryRequirement | None = None,
    runtime_rollback_contract: RepoRuntimeRollbackContract | None = None,
) -> RepoRuntimePermissionAuthorityPosture:
    _ = repo_root
    request = (
        runtime_permission_review_request
        or derive_v77a_repo_runtime_permission_review_request()
    )
    preflight = command_preflight_contract or derive_v77b_repo_command_preflight_contract(
        runtime_permission_review_request=request
    )
    envelope = action_effect_envelope or derive_v77b_repo_action_effect_envelope(
        command_preflight_contract=preflight
    )
    telemetry = runtime_telemetry_requirement or derive_v77b_repo_runtime_telemetry_requirement(
        command_preflight_contract=preflight,
        action_effect_envelope=envelope,
    )
    rollback = runtime_rollback_contract or derive_v77b_repo_runtime_rollback_contract(
        command_preflight_contract=preflight,
        action_effect_envelope=envelope,
    )
    preflight_by_review = {
        review_ref: row
        for row in preflight.preflight_rows
        for review_ref in row.runtime_review_refs
    }
    effect_by_preflight = {
        preflight_ref: row
        for row in envelope.effect_envelope_rows
        for preflight_ref in row.preflight_refs
    }
    telemetry_by_preflight = {
        preflight_ref: row
        for row in telemetry.telemetry_requirement_rows
        for preflight_ref in row.preflight_refs
    }
    rollback_by_preflight = {
        preflight_ref: row
        for row in rollback.rollback_contract_rows
        for preflight_ref in row.preflight_refs
    }
    rows = []
    for request_row in request.request_rows:
        preflight_row = preflight_by_review[request_row.runtime_review_ref]
        effect_row = effect_by_preflight[preflight_row.preflight_ref]
        telemetry_row = telemetry_by_preflight[preflight_row.preflight_ref]
        rollback_row = rollback_by_preflight[preflight_row.preflight_ref]
        for authority_ref in request_row.required_later_authority_refs:
            authority_kind = _v77c_authority_kind_for_v77a_ref(authority_ref)
            posture_suffix = authority_ref.removeprefix("authority:v77a:")
            rows.append(
                {
                    "authority_posture_ref": f"authority-posture:v77c:{posture_suffix}",
                    "runtime_review_refs": [request_row.runtime_review_ref],
                    "preflight_refs": [preflight_row.preflight_ref],
                    "effect_envelope_refs": [effect_row.effect_envelope_ref],
                    "telemetry_requirement_refs": [telemetry_row.telemetry_requirement_ref],
                    "rollback_contract_refs": [rollback_row.rollback_contract_ref],
                    "candidate_ref": request_row.candidate_ref,
                    "authority_requirement_kind": authority_kind,
                    "authority_source_refs": ["docs/LOCKED_CONTINUATION_vNEXT_PLUS217.md"],
                    "authority_gap_posture": "authority_gap_present",
                    "authority_decision_posture": (
                        "authority_future_family_only"
                        if authority_kind in {"product_authorization", "external_branch_activation"}
                        else "authority_required_later"
                    ),
                    "forbidden_authority_inferences": sorted(
                        _FORBIDDEN_V77C_AUTHORITY_INFERENCES
                    ),
                    "limitation_note": (
                        "Authority is required later only: no runtime permission, "
                        "no tool-use permission, no command execution, and no release."
                    ),
                }
            )
    payload = {
        "schema": REPO_RUNTIME_PERMISSION_AUTHORITY_POSTURE_SCHEMA,
        "runtime_permission_authority_posture_id": "",
        "runtime_permission_review_request_id": request.runtime_permission_review_request_id,
        "command_preflight_contract_id": preflight.command_preflight_contract_id,
        "action_effect_envelope_id": envelope.action_effect_envelope_id,
        "runtime_telemetry_requirement_id": telemetry.runtime_telemetry_requirement_id,
        "runtime_rollback_contract_id": rollback.runtime_rollback_contract_id,
        "review_id": request.review_id,
        "snapshot_id": "vNext+217-runtime-authority-review",
        "source_set_id": request.source_set_id,
        "authority_posture_rows": sorted(rows, key=lambda row: row["authority_posture_ref"]),
        "authority_boundary_summary": (
            "Runtime authority is required or missing only: no runtime permission, "
            "no tool-use permission, and no release."
        ),
    }
    payload["runtime_permission_authority_posture_id"] = _surface_id(
        "repo_runtime_permission_authority_posture",
        REPO_RUNTIME_PERMISSION_AUTHORITY_POSTURE_SCHEMA,
        payload,
        "runtime_permission_authority_posture_id",
    )
    return RepoRuntimePermissionAuthorityPosture.model_validate(payload)


def derive_v77c_repo_runtime_permission_review_summary(
    *,
    repo_root: Path | None = None,
    runtime_permission_review_request: RepoRuntimePermissionReviewRequest | None = None,
    command_preflight_contract: RepoCommandPreflightContract | None = None,
    action_effect_envelope: RepoActionEffectEnvelope | None = None,
    runtime_telemetry_requirement: RepoRuntimeTelemetryRequirement | None = None,
    runtime_rollback_contract: RepoRuntimeRollbackContract | None = None,
    runtime_permission_authority_posture: RepoRuntimePermissionAuthorityPosture | None = None,
) -> RepoRuntimePermissionReviewSummary:
    _ = repo_root
    request = (
        runtime_permission_review_request
        or derive_v77a_repo_runtime_permission_review_request()
    )
    preflight = command_preflight_contract or derive_v77b_repo_command_preflight_contract(
        runtime_permission_review_request=request
    )
    envelope = action_effect_envelope or derive_v77b_repo_action_effect_envelope(
        command_preflight_contract=preflight
    )
    telemetry = runtime_telemetry_requirement or derive_v77b_repo_runtime_telemetry_requirement(
        command_preflight_contract=preflight,
        action_effect_envelope=envelope,
    )
    rollback = runtime_rollback_contract or derive_v77b_repo_runtime_rollback_contract(
        command_preflight_contract=preflight,
        action_effect_envelope=envelope,
    )
    authority = runtime_permission_authority_posture or (
        derive_v77c_repo_runtime_permission_authority_posture(
            runtime_permission_review_request=request,
            command_preflight_contract=preflight,
            action_effect_envelope=envelope,
            runtime_telemetry_requirement=telemetry,
            runtime_rollback_contract=rollback,
        )
    )
    preflight_by_review = {
        review_ref: row
        for row in preflight.preflight_rows
        for review_ref in row.runtime_review_refs
    }
    effect_by_preflight = {
        preflight_ref: row
        for row in envelope.effect_envelope_rows
        for preflight_ref in row.preflight_refs
    }
    telemetry_by_preflight = {
        preflight_ref: row
        for row in telemetry.telemetry_requirement_rows
        for preflight_ref in row.preflight_refs
    }
    rollback_by_preflight = {
        preflight_ref: row
        for row in rollback.rollback_contract_rows
        for preflight_ref in row.preflight_refs
    }
    authority_by_candidate: dict[str, list[str]] = {}
    for authority_row in authority.authority_posture_rows:
        authority_by_candidate.setdefault(authority_row.candidate_ref, []).append(
            authority_row.authority_posture_ref
        )
    rows = []
    for request_row in request.request_rows:
        preflight_row = preflight_by_review[request_row.runtime_review_ref]
        effect_row = effect_by_preflight[preflight_row.preflight_ref]
        telemetry_row = telemetry_by_preflight[preflight_row.preflight_ref]
        rollback_row = rollback_by_preflight[preflight_row.preflight_ref]
        authority_refs = sorted(authority_by_candidate.get(request_row.candidate_ref, []))
        product_only = request_row.requested_permission_horizon == "future_product_review"
        rows.append(
            {
                "runtime_summary_ref": request_row.runtime_review_ref.replace(
                    "runtime-review:v77a",
                    "runtime-summary:v77c",
                ),
                "runtime_review_refs": [request_row.runtime_review_ref],
                "preflight_refs": [preflight_row.preflight_ref],
                "effect_envelope_refs": [effect_row.effect_envelope_ref],
                "telemetry_requirement_refs": [telemetry_row.telemetry_requirement_ref],
                "rollback_contract_refs": [rollback_row.rollback_contract_ref],
                "authority_posture_refs": authority_refs,
                "candidate_ref": request_row.candidate_ref,
                "summary_posture": (
                    "future_family_only" if product_only else "blocked_by_missing_authority"
                ),
                "ready_basis_posture": (
                    "future_family_only" if product_only else "not_ready_blockers_remain"
                ),
                "carried_blocker_refs": authority_refs,
                "non_execution_guardrail": request_row.guardrail_refs[0],
                "limitation_note": (
                    "Runtime review summary preserves blockers with no command execution, "
                    "no runtime permission, no tool-use permission, and no release."
                ),
            }
        )
    payload = {
        "schema": REPO_RUNTIME_PERMISSION_REVIEW_SUMMARY_SCHEMA,
        "runtime_permission_review_summary_id": "",
        "runtime_permission_authority_posture_id": (
            authority.runtime_permission_authority_posture_id
        ),
        "runtime_permission_review_request_id": request.runtime_permission_review_request_id,
        "command_preflight_contract_id": preflight.command_preflight_contract_id,
        "action_effect_envelope_id": envelope.action_effect_envelope_id,
        "runtime_telemetry_requirement_id": telemetry.runtime_telemetry_requirement_id,
        "runtime_rollback_contract_id": rollback.runtime_rollback_contract_id,
        "review_id": request.review_id,
        "snapshot_id": authority.snapshot_id,
        "source_set_id": request.source_set_id,
        "summary_rows": sorted(rows, key=lambda row: row["runtime_summary_ref"]),
        "runtime_summary_boundary": (
            "Runtime summary preserves blocker state with no command execution and no "
            "runtime permission."
        ),
    }
    payload["runtime_permission_review_summary_id"] = _surface_id(
        "repo_runtime_permission_review_summary",
        REPO_RUNTIME_PERMISSION_REVIEW_SUMMARY_SCHEMA,
        payload,
        "runtime_permission_review_summary_id",
    )
    return RepoRuntimePermissionReviewSummary.model_validate(payload)


def derive_v77c_repo_post_runtime_permission_review_handoff(
    *,
    repo_root: Path | None = None,
    runtime_permission_review_request: RepoRuntimePermissionReviewRequest | None = None,
    runtime_permission_authority_posture: RepoRuntimePermissionAuthorityPosture | None = None,
    runtime_permission_review_summary: RepoRuntimePermissionReviewSummary | None = None,
) -> RepoPostRuntimePermissionReviewHandoff:
    _ = repo_root
    request = (
        runtime_permission_review_request
        or derive_v77a_repo_runtime_permission_review_request()
    )
    authority = runtime_permission_authority_posture or (
        derive_v77c_repo_runtime_permission_authority_posture(
            runtime_permission_review_request=request
        )
    )
    summary = runtime_permission_review_summary or (
        derive_v77c_repo_runtime_permission_review_summary(
            runtime_permission_review_request=request,
            runtime_permission_authority_posture=authority,
        )
    )
    summary_by_review = {
        review_ref: row for row in summary.summary_rows for review_ref in row.runtime_review_refs
    }
    authority_rows = {
        row.authority_posture_ref: row for row in authority.authority_posture_rows
    }
    rows = []
    for request_row in request.request_rows:
        summary_row = summary_by_review[request_row.runtime_review_ref]
        authority_refs = summary_row.authority_posture_refs
        authority_kinds = sorted(
            {
                authority_rows[authority_ref].authority_requirement_kind
                for authority_ref in authority_refs
            }
        )
        product_only = request_row.requested_permission_horizon == "future_product_review"
        rows.append(
            {
                "handoff_ref": request_row.runtime_review_ref.replace(
                    "runtime-review:v77a",
                    "handoff:v77c",
                ),
                "runtime_summary_refs": [summary_row.runtime_summary_ref],
                "runtime_review_refs": [request_row.runtime_review_ref],
                "authority_posture_refs": authority_refs,
                "carried_gap_refs": authority_refs,
                "handoff_target": (
                    "future_product_review"
                    if product_only
                    else "future_runtime_execution_authority_review"
                ),
                "handoff_subject_horizon": (
                    "Product pressure review request only"
                    if product_only
                    else "Runtime execution authority review request only"
                ),
                "handoff_posture": (
                    "deferred_to_future_family"
                    if product_only
                    else "blocked_by_required_later_authority"
                ),
                "required_later_authority_refs": authority_refs,
                "required_later_authority_kinds": authority_kinds,
                "non_execution_guardrail": request_row.guardrail_refs[0],
                "runtime_permission_execution_posture": (
                    "no_runtime_permission_granted_by_v77"
                ),
                "limitation_note": (
                    "Post-runtime-permission-review handoff requests later review only: "
                    "no runtime permission, no command execution, no tool-use permission, "
                    "and no release."
                ),
            }
        )
    payload = {
        "schema": REPO_POST_RUNTIME_PERMISSION_REVIEW_HANDOFF_SCHEMA,
        "post_runtime_permission_review_handoff_id": "",
        "runtime_permission_review_summary_id": summary.runtime_permission_review_summary_id,
        "runtime_permission_authority_posture_id": (
            authority.runtime_permission_authority_posture_id
        ),
        "review_id": request.review_id,
        "snapshot_id": summary.snapshot_id,
        "source_set_id": request.source_set_id,
        "handoff_rows": sorted(rows, key=lambda row: row["handoff_ref"]),
        "handoff_boundary_summary": (
            "Post-runtime handoffs are requests for later review with no runtime "
            "permission and no target family performed."
        ),
    }
    payload["post_runtime_permission_review_handoff_id"] = _surface_id(
        "repo_post_runtime_permission_review_handoff",
        REPO_POST_RUNTIME_PERMISSION_REVIEW_HANDOFF_SCHEMA,
        payload,
        "post_runtime_permission_review_handoff_id",
    )
    return RepoPostRuntimePermissionReviewHandoff.model_validate(payload)


def derive_v77c_repo_runtime_permission_family_closeout_alignment(
    *,
    repo_root: Path | None = None,
    runtime_permission_review_summary: RepoRuntimePermissionReviewSummary | None = None,
    post_runtime_permission_review_handoff: RepoPostRuntimePermissionReviewHandoff | None = None,
) -> RepoRuntimePermissionFamilyCloseoutAlignment:
    _ = repo_root
    summary = (
        runtime_permission_review_summary
        or derive_v77c_repo_runtime_permission_review_summary()
    )
    handoff = post_runtime_permission_review_handoff or (
        derive_v77c_repo_post_runtime_permission_review_handoff(
            runtime_permission_review_summary=summary
        )
    )
    payload = {
        "schema": REPO_RUNTIME_PERMISSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
        "runtime_permission_family_closeout_alignment_id": "",
        "runtime_permission_review_summary_id": summary.runtime_permission_review_summary_id,
        "post_runtime_permission_review_handoff_id": (
            handoff.post_runtime_permission_review_handoff_id
        ),
        "review_id": summary.review_id,
        "snapshot_id": summary.snapshot_id,
        "source_set_id": summary.source_set_id,
        "closeout_rows": [
            {
                "family": "V77",
                "closed_slice_ladder": ["V77-A", "V77-B", "V77-C"],
                "closed_by_arc": "vNext+217",
                "consumed_source_families": [
                    "V68",
                    "V69",
                    "V70",
                    "V71",
                    "V72",
                    "V73",
                    "V74",
                    "V75",
                    "V76",
                ],
                "shipped_record_shapes": sorted([
                    REPO_RUNTIME_PERMISSION_REVIEW_REQUEST_SCHEMA,
                    REPO_RUNTIME_PERMISSION_SOURCE_INDEX_SCHEMA,
                    REPO_RUNTIME_NON_EXECUTION_GUARDRAIL_SCHEMA,
                    REPO_COMMAND_PREFLIGHT_CONTRACT_SCHEMA,
                    REPO_ACTION_EFFECT_ENVELOPE_SCHEMA,
                    REPO_RUNTIME_TELEMETRY_REQUIREMENT_SCHEMA,
                    REPO_RUNTIME_ROLLBACK_CONTRACT_SCHEMA,
                    REPO_RUNTIME_PERMISSION_AUTHORITY_POSTURE_SCHEMA,
                    REPO_RUNTIME_PERMISSION_REVIEW_SUMMARY_SCHEMA,
                    REPO_POST_RUNTIME_PERMISSION_REVIEW_HANDOFF_SCHEMA,
                    REPO_RUNTIME_PERMISSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
                ]),
                "runtime_authority_boundary": (
                    "V77 closes as runtime-permission review only with no runtime "
                    "permission, no command execution, and no tool-use permission."
                ),
                "future_family_authority": (
                    "Future runtime execution, product, external, graph-memory, and "
                    "policy surfaces remain future pressure and are not selected here."
                ),
                "unselected_future_surfaces": sorted([
                    "runtime_execution_authority",
                    "tool_use_permission",
                    "product_authorization",
                    "external_branch_activation",
                    "living_decision_graph",
                    "recursive_policy_amendment",
                ]),
                "limitation_note": (
                    "Family closeout alignment is review only with no command execution, "
                    "no runtime permission, no tool-use permission, no product authorization, "
                    "no external branch activation, and no release."
                ),
            }
        ],
        "closeout_boundary_summary": (
            "V77 closes as review posture only: no runtime permission, no command "
            "execution, and later family selection is not selected here."
        ),
    }
    payload["runtime_permission_family_closeout_alignment_id"] = _surface_id(
        "repo_runtime_permission_family_closeout_alignment",
        REPO_RUNTIME_PERMISSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
        payload,
        "runtime_permission_family_closeout_alignment_id",
    )
    return RepoRuntimePermissionFamilyCloseoutAlignment.model_validate(payload)


def validate_v77c_runtime_permission_closeout_bundle(
    *,
    runtime_permission_review_request: RepoRuntimePermissionReviewRequest,
    command_preflight_contract: RepoCommandPreflightContract,
    action_effect_envelope: RepoActionEffectEnvelope,
    runtime_telemetry_requirement: RepoRuntimeTelemetryRequirement,
    runtime_rollback_contract: RepoRuntimeRollbackContract,
    runtime_permission_authority_posture: RepoRuntimePermissionAuthorityPosture,
    runtime_permission_review_summary: RepoRuntimePermissionReviewSummary,
    post_runtime_permission_review_handoff: RepoPostRuntimePermissionReviewHandoff,
    runtime_permission_family_closeout_alignment: RepoRuntimePermissionFamilyCloseoutAlignment,
) -> None:
    if (
        runtime_permission_authority_posture.runtime_permission_review_request_id
        != runtime_permission_review_request.runtime_permission_review_request_id
    ):
        raise ValueError("runtime authority posture must reference V77-A request surface")
    for surface_name, surface in (
        ("summary", runtime_permission_review_summary),
        ("family closeout", runtime_permission_family_closeout_alignment),
    ):
        if (
            surface.review_id,
            surface.snapshot_id,
            surface.source_set_id,
        ) != (
            runtime_permission_authority_posture.review_id,
            runtime_permission_authority_posture.snapshot_id,
            runtime_permission_authority_posture.source_set_id,
        ):
            raise ValueError(f"{surface_name} provenance must match runtime authority posture")
    if (
        runtime_permission_review_summary.runtime_permission_authority_posture_id
        != runtime_permission_authority_posture.runtime_permission_authority_posture_id
    ):
        raise ValueError("runtime summary must reference authority posture surface")
    if (
        post_runtime_permission_review_handoff.runtime_permission_review_summary_id
        != runtime_permission_review_summary.runtime_permission_review_summary_id
    ):
        raise ValueError("post-runtime handoff must reference runtime summary surface")
    if (
        post_runtime_permission_review_handoff.runtime_permission_authority_posture_id
        != runtime_permission_authority_posture.runtime_permission_authority_posture_id
    ):
        raise ValueError("post-runtime handoff must reference authority posture surface")
    if (
        runtime_permission_family_closeout_alignment.runtime_permission_review_summary_id
        != runtime_permission_review_summary.runtime_permission_review_summary_id
    ):
        raise ValueError("runtime closeout must reference runtime summary surface")
    if (
        runtime_permission_family_closeout_alignment.post_runtime_permission_review_handoff_id
        != post_runtime_permission_review_handoff.post_runtime_permission_review_handoff_id
    ):
        raise ValueError("runtime closeout must reference post-runtime handoff surface")

    request_rows = {
        row.runtime_review_ref: row for row in runtime_permission_review_request.request_rows
    }
    preflight_rows = {
        row.preflight_ref: row for row in command_preflight_contract.preflight_rows
    }
    effect_rows = {
        row.effect_envelope_ref: row for row in action_effect_envelope.effect_envelope_rows
    }
    telemetry_rows = {
        row.telemetry_requirement_ref: row
        for row in runtime_telemetry_requirement.telemetry_requirement_rows
    }
    rollback_rows = {
        row.rollback_contract_ref: row for row in runtime_rollback_contract.rollback_contract_rows
    }
    authority_rows = {
        row.authority_posture_ref: row
        for row in runtime_permission_authority_posture.authority_posture_rows
    }
    summary_rows = {
        row.runtime_summary_ref: row for row in runtime_permission_review_summary.summary_rows
    }

    def _candidate_for_runtime_ref(ref: str) -> str:
        return request_rows[ref].candidate_ref

    for authority_row in runtime_permission_authority_posture.authority_posture_rows:
        for runtime_ref in authority_row.runtime_review_refs:
            if runtime_ref not in request_rows:
                raise ValueError("authority posture runtime refs must be known V77-A refs")
            if _candidate_for_runtime_ref(runtime_ref) != authority_row.candidate_ref:
                raise ValueError("authority posture runtime refs must match candidate")
        for preflight_ref in authority_row.preflight_refs:
            if preflight_ref not in preflight_rows:
                raise ValueError("authority posture preflight refs must be known")
            if preflight_rows[preflight_ref].candidate_ref != authority_row.candidate_ref:
                raise ValueError("authority posture preflight refs must match candidate")
        for effect_ref in authority_row.effect_envelope_refs:
            if effect_ref not in effect_rows:
                raise ValueError("authority posture effect refs must be known")
            if effect_rows[effect_ref].candidate_ref != authority_row.candidate_ref:
                raise ValueError("authority posture effect refs must match candidate")
        for telemetry_ref in authority_row.telemetry_requirement_refs:
            if telemetry_ref not in telemetry_rows:
                raise ValueError("authority posture telemetry refs must be known")
            if telemetry_rows[telemetry_ref].candidate_ref != authority_row.candidate_ref:
                raise ValueError("authority posture telemetry refs must match candidate")
        for rollback_ref in authority_row.rollback_contract_refs:
            if rollback_ref not in rollback_rows:
                raise ValueError("authority posture rollback refs must be known")
            if rollback_rows[rollback_ref].candidate_ref != authority_row.candidate_ref:
                raise ValueError("authority posture rollback refs must match candidate")

    for summary_row in runtime_permission_review_summary.summary_rows:
        for authority_ref in summary_row.authority_posture_refs:
            if authority_ref not in authority_rows:
                raise ValueError("runtime summary authority refs must be known")
            if authority_rows[authority_ref].candidate_ref != summary_row.candidate_ref:
                raise ValueError("runtime summary authority refs must match candidate")
        for blocker_ref in summary_row.carried_blocker_refs:
            if blocker_ref not in authority_rows:
                raise ValueError("runtime summary blockers must be known authority refs")
        for runtime_ref in summary_row.runtime_review_refs:
            if runtime_ref not in request_rows:
                raise ValueError("runtime summary runtime refs must be known V77-A refs")
            if request_rows[runtime_ref].candidate_ref != summary_row.candidate_ref:
                raise ValueError("runtime summary runtime refs must match candidate")

    for handoff_row in post_runtime_permission_review_handoff.handoff_rows:
        for summary_ref in handoff_row.runtime_summary_refs:
            if summary_ref not in summary_rows:
                raise ValueError("post-runtime handoff summary refs must be known")
        for authority_ref in handoff_row.authority_posture_refs:
            if authority_ref not in authority_rows:
                raise ValueError("post-runtime handoff authority refs must be known")
        for authority_ref in handoff_row.required_later_authority_refs:
            if authority_ref not in authority_rows:
                raise ValueError("post-runtime handoff authority refs must be known")
        authority_kinds = {
            authority_rows[authority_ref].authority_requirement_kind
            for authority_ref in handoff_row.required_later_authority_refs
        }
        if not set(handoff_row.required_later_authority_kinds).issubset(authority_kinds):
            raise ValueError("post-runtime handoff authority kinds must resolve to refs")


def derive_v77c_runtime_permission_closeout_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoRuntimePermissionAuthorityPosture,
    RepoRuntimePermissionReviewSummary,
    RepoPostRuntimePermissionReviewHandoff,
    RepoRuntimePermissionFamilyCloseoutAlignment,
]:
    _, request, guardrail = derive_v77a_runtime_permission_review_bundle(repo_root=repo_root)
    preflight, envelope, telemetry, rollback = derive_v77b_runtime_preflight_bundle(
        repo_root=repo_root
    )
    authority = derive_v77c_repo_runtime_permission_authority_posture(
        repo_root=repo_root,
        runtime_permission_review_request=request,
        command_preflight_contract=preflight,
        action_effect_envelope=envelope,
        runtime_telemetry_requirement=telemetry,
        runtime_rollback_contract=rollback,
    )
    summary = derive_v77c_repo_runtime_permission_review_summary(
        repo_root=repo_root,
        runtime_permission_review_request=request,
        command_preflight_contract=preflight,
        action_effect_envelope=envelope,
        runtime_telemetry_requirement=telemetry,
        runtime_rollback_contract=rollback,
        runtime_permission_authority_posture=authority,
    )
    handoff = derive_v77c_repo_post_runtime_permission_review_handoff(
        repo_root=repo_root,
        runtime_permission_review_request=request,
        runtime_permission_authority_posture=authority,
        runtime_permission_review_summary=summary,
    )
    closeout = derive_v77c_repo_runtime_permission_family_closeout_alignment(
        repo_root=repo_root,
        runtime_permission_review_summary=summary,
        post_runtime_permission_review_handoff=handoff,
    )
    validate_v77b_runtime_preflight_bundle(
        runtime_permission_review_request=request,
        runtime_non_execution_guardrail=guardrail,
        command_preflight_contract=preflight,
        action_effect_envelope=envelope,
        runtime_telemetry_requirement=telemetry,
        runtime_rollback_contract=rollback,
    )
    validate_v77c_runtime_permission_closeout_bundle(
        runtime_permission_review_request=request,
        command_preflight_contract=preflight,
        action_effect_envelope=envelope,
        runtime_telemetry_requirement=telemetry,
        runtime_rollback_contract=rollback,
        runtime_permission_authority_posture=authority,
        runtime_permission_review_summary=summary,
        post_runtime_permission_review_handoff=handoff,
        runtime_permission_family_closeout_alignment=closeout,
    )
    return authority, summary, handoff, closeout
