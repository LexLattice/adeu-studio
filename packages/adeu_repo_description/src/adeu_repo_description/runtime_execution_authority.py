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

REPO_RUNTIME_EXECUTION_AUTHORITY_REQUEST_SCHEMA = (
    "repo_runtime_execution_authority_request@1"
)
REPO_RUNTIME_AUTHORITY_SOURCE_INDEX_SCHEMA = "repo_runtime_authority_source_index@1"
REPO_RUNTIME_AUTHORITY_NON_ACTION_GUARDRAIL_SCHEMA = (
    "repo_runtime_authority_non_action_guardrail@1"
)
REPO_RUNTIME_EXECUTION_AUTHORITY_DECISION_SCHEMA = (
    "repo_runtime_execution_authority_decision@1"
)
REPO_TOOL_USE_PERMISSION_ENVELOPE_SCHEMA = "repo_tool_use_permission_envelope@1"
REPO_COMMAND_SCOPE_AUTHORIZATION_BOUNDARY_SCHEMA = (
    "repo_command_scope_authorization_boundary@1"
)
REPO_RUNTIME_AUTHORITY_EXCEPTION_REGISTER_SCHEMA = (
    "repo_runtime_authority_exception_register@1"
)

RuntimeAuthoritySourceRole = Literal[
    "v77_authority_posture_source",
    "v77_runtime_summary_source",
    "v77_post_runtime_permission_review_handoff_source",
    "v77_family_closeout_source",
    "v77_command_preflight_context",
    "v77_effect_envelope_context",
    "v77_telemetry_requirement_context",
    "v77_rollback_contract_context",
    "combined_dogfood_source",
    "support_context",
    "absence_marker",
]
RuntimeExecutionAuthorityRequestPosture = Literal[
    "eligible_for_runtime_execution_authority_review",
    "blocked_by_missing_source",
    "blocked_by_missing_authority_source",
    "blocked_by_product_authority_gap",
    "blocked_by_external_branch_gap",
    "blocked_by_unbounded_command_scope",
    "blocked_by_missing_telemetry_requirement",
    "blocked_by_missing_rollback_requirement",
    "future_family_only",
    "rejected_out_of_scope",
]
RequestedRuntimeAuthorityHorizon = Literal[
    "bounded_command_execution_review",
    "bounded_tool_invocation_review",
    "bounded_repo_script_execution_review",
    "bounded_api_call_execution_review",
    "telemetry_observation_review",
    "rollback_execution_review",
    "future_product_runtime_review",
    "future_external_branch_runtime_review",
    "future_family_review",
]
RuntimeExecutionAuthorityKind = Literal[
    "maintainer_authority",
    "policy_authority",
    "runtime_execution_review_authority",
    "tool_use_review_authority",
    "product_authorization",
    "external_branch_activation",
    "release_authority",
    "recursive_policy_authority",
]
RuntimeAuthorityGapPosture = Literal[
    "authority_gap_present",
    "authority_checked_absent",
    "authority_not_applicable",
    "unknown_needs_review",
]
RuntimeAuthorityExecutionPosture = Literal[
    "no_execution_performed_by_v78",
    "execution_requires_later_family",
    "execution_forbidden_by_this_family",
]
RuntimeAuthorityToolInvocationPosture = Literal[
    "no_tool_invocation_performed_by_v78",
    "tool_invocation_requires_later_family",
    "tool_invocation_forbidden_by_this_family",
]
RuntimeAuthorityForbiddenAction = Literal[
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
RuntimeAuthorityForbiddenDownstreamAuthority = Literal[
    "product_authorization",
    "external_branch_activation",
    "released_truth",
    "benchmark_truth",
    "model_selection",
    "living_memory_authority",
    "recursive_policy_amendment",
]
RuntimeExecutionAuthorityDecisionPosture = Literal[
    "review_authority_granted_for_bounded_execution_surface",
    "review_authority_denied",
    "review_authority_deferred",
    "review_authority_blocked_by_missing_source",
    "review_authority_blocked_by_missing_scope",
    "review_authority_blocked_by_missing_telemetry",
    "review_authority_blocked_by_missing_rollback",
    "review_authority_future_family_only",
    "review_authority_rejected_out_of_scope",
]
RuntimeAuthorizedSurfaceKind = Literal[
    "later_execution_review_surface",
    "later_tool_invocation_review_surface",
    "later_telemetry_review_surface",
    "later_rollback_review_surface",
    "future_family_review_surface",
]
RuntimeAuthorityGrantHorizon = Literal[
    "later_execution_review_only",
    "later_tool_invocation_review_only",
    "later_telemetry_review_only",
    "later_rollback_review_only",
    "future_family_review_only",
]
RuntimeExecutionAuthorizationPosture = Literal[
    "execution_not_authorized_by_v78",
    "execution_requires_later_family",
    "execution_forbidden_by_this_family",
]
ToolUsePermissionPosture = Literal[
    "tool_use_permission_granted_for_later_execution_review",
    "tool_use_permission_denied",
    "tool_use_permission_deferred",
    "tool_use_permission_blocked_by_missing_authority",
    "tool_use_permission_future_family_only",
    "tool_use_not_applicable",
]
RuntimeTargetResolutionKind = Literal[
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
RuntimeAuthorizedScopePosture = Literal[
    "bounded_scope_authorized_for_later_execution_review",
    "scope_denied",
    "scope_deferred",
    "scope_blocked_by_missing_target",
    "scope_blocked_by_unbounded_target",
    "scope_blocked_by_missing_telemetry",
    "scope_blocked_by_missing_rollback",
    "scope_future_family_only",
]
RuntimeAuthorityExceptionKind = Literal[
    "missing_authority_source",
    "missing_command_scope",
    "unbounded_target",
    "missing_telemetry_requirement",
    "missing_rollback_requirement",
    "tool_permission_gap",
    "product_authority_gap",
    "external_branch_authority_gap",
    "release_authority_gap",
    "command_output_without_prior_authority",
    "unknown_needs_review",
]
RuntimeAuthorityExceptionPosture = Literal[
    "blocking",
    "warning_only",
    "carried_forward",
    "not_applicable",
    "future_family_only",
]
RuntimeAuthorityRequiredNextSurface = Literal[
    "later_execution_review_surface",
    "later_tool_invocation_review_surface",
    "future_product_review",
    "future_external_branch_review",
    "future_family_review",
    "none",
]

_ELIGIBILITY_SOURCE_ROLES = {
    "v77_authority_posture_source",
    "v77_runtime_summary_source",
    "v77_post_runtime_permission_review_handoff_source",
    "v77_family_closeout_source",
}
_CONTEXT_SOURCE_ROLES = {
    "v77_command_preflight_context",
    "v77_effect_envelope_context",
    "v77_telemetry_requirement_context",
    "v77_rollback_contract_context",
    "combined_dogfood_source",
    "support_context",
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
    "product_authorization",
    "external_branch_activation",
    "released_truth",
    "benchmark_truth",
    "model_selection",
    "living_memory_authority",
    "recursive_policy_amendment",
}
_GRANT_DECISION_POSTURES = {"review_authority_granted_for_bounded_execution_surface"}
_LATER_REVIEW_SURFACE_KINDS = {
    "later_execution_review_surface",
    "later_tool_invocation_review_surface",
    "later_telemetry_review_surface",
    "later_rollback_review_surface",
}


def _reject_v78_action_claim(value: str, *, field_name: str) -> str:
    lowered = value.lower()
    forbidden_patterns = [
        r"command (?:is |was |has been |gets |got )?executed",
        r"execution (?:is |was |has been |gets |got )?authorized",
        r"run command",
        r"command output proves",
        r"tool (?:is |was |has been |gets |got )?invoked",
        r"invoke tool",
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
            raise ValueError(f"{field_name} may not carry runtime action or authority")
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


class RepoRuntimeAuthoritySourceRow(_CartographyBase):
    source_ref: str
    source_kind: CandidateSourceKind
    authority_layer: CandidateAuthorityLayer
    source_status: SourceStatus
    source_presence_posture: CandidateSourcePresencePosture
    runtime_authority_source_role: RuntimeAuthoritySourceRole
    source_horizon: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_runtime_authority_source_row(self) -> RepoRuntimeAuthoritySourceRow:
        _repo_ref(self.source_ref, field_name="source_ref")
        _non_empty(self.source_horizon, field_name="source_horizon")
        _reject_v78_action_claim(self.limitation_note, field_name="limitation_note")
        if (
            self.runtime_authority_source_role != "absence_marker"
            and self.source_presence_posture != "present"
        ):
            raise ValueError("non-absence runtime authority source rows must be present")
        if (
            self.runtime_authority_source_role == "absence_marker"
            and self.source_presence_posture == "present"
        ):
            raise ValueError("absence-marker runtime authority rows must not be present sources")
        if (
            self.runtime_authority_source_role in _CONTEXT_SOURCE_ROLES
            and self.authority_layer == "lock"
            and self.source_kind == "support_doc"
        ):
            raise ValueError("support context may not be marked as lock authority")
        return self


class RepoRuntimeAuthoritySourceIndex(_CartographyBase):
    schema: Literal["repo_runtime_authority_source_index@1"] = (
        REPO_RUNTIME_AUTHORITY_SOURCE_INDEX_SCHEMA
    )
    runtime_authority_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    source_rows: list[RepoRuntimeAuthoritySourceRow] = Field(min_length=1)
    runtime_authority_source_summary: str

    @model_validator(mode="after")
    def _validate_runtime_authority_source_index(self) -> RepoRuntimeAuthoritySourceIndex:
        object.__setattr__(
            self,
            "source_rows",
            _sorted_unique_by_ref(self.source_rows, attr="source_ref", field_name="source_rows"),
        )
        _non_empty(self.review_id, field_name="review_id")
        _non_empty(self.snapshot_id, field_name="snapshot_id")
        _non_empty(self.source_set_id, field_name="source_set_id")
        _require_terms(
            self.runtime_authority_source_summary,
            field_name="runtime_authority_source_summary",
            terms=("eligibility", "context", "no prose memory", "no execution"),
        )
        expected_id = _surface_id(
            "repo_runtime_authority_source_index",
            self.schema,
            self.model_dump(mode="json"),
            "runtime_authority_source_index_id",
        )
        if self.runtime_authority_source_index_id != expected_id:
            raise ValueError("runtime_authority_source_index_id does not match canonical hash")
        return self


class RepoRuntimeAuthorityRequirementRow(_CartographyBase):
    authority_requirement_ref: str
    candidate_ref: str
    authority_kind: RuntimeExecutionAuthorityKind
    required_for_horizon: RequestedRuntimeAuthorityHorizon
    source_refs: list[str] = Field(min_length=1)
    source_presence_posture: CandidateSourcePresencePosture
    authority_gap_posture: RuntimeAuthorityGapPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_runtime_authority_requirement_row(
        self,
    ) -> RepoRuntimeAuthorityRequirementRow:
        _non_empty(self.authority_requirement_ref, field_name="authority_requirement_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        object.__setattr__(
            self,
            "source_refs",
            _sorted_unique(self.source_refs, field_name="source_refs"),
        )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        _reject_v78_action_claim(self.limitation_note, field_name="limitation_note")
        if (
            self.source_presence_posture != "present"
            and self.authority_gap_posture != "unknown_needs_review"
        ):
            raise ValueError("missing authority requirement sources must remain unknown")
        return self


class RepoRuntimeExecutionAuthorityRequestRow(_CartographyBase):
    authority_request_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    v77_authority_posture_refs: list[str] = Field(default_factory=list)
    v77_summary_refs: list[str] = Field(default_factory=list)
    v77_handoff_refs: list[str] = Field(default_factory=list)
    v77_closeout_refs: list[str] = Field(default_factory=list)
    requested_authority_horizon: RequestedRuntimeAuthorityHorizon
    authority_request_posture: RuntimeExecutionAuthorityRequestPosture
    requested_tool_use_refs: list[str] = Field(default_factory=list)
    requested_command_scope_refs: list[str] = Field(default_factory=list)
    required_authority_source_refs: list[str] = Field(default_factory=list)
    authority_requirement_rows: list[RepoRuntimeAuthorityRequirementRow] = Field(
        default_factory=list
    )
    target_boundary_refs: list[str] = Field(default_factory=list)
    telemetry_requirement_refs: list[str] = Field(default_factory=list)
    rollback_requirement_refs: list[str] = Field(default_factory=list)
    guardrail_refs: list[str] = Field(min_length=1)
    execution_posture: RuntimeAuthorityExecutionPosture
    tool_invocation_posture: RuntimeAuthorityToolInvocationPosture
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_runtime_execution_authority_request_row(
        self,
    ) -> RepoRuntimeExecutionAuthorityRequestRow:
        _non_empty(self.authority_request_ref, field_name="authority_request_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "v77_authority_posture_refs",
            "v77_summary_refs",
            "v77_handoff_refs",
            "v77_closeout_refs",
            "requested_tool_use_refs",
            "requested_command_scope_refs",
            "required_authority_source_refs",
            "target_boundary_refs",
            "telemetry_requirement_refs",
            "rollback_requirement_refs",
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
            "authority_requirement_rows",
            _sorted_unique_by_ref(
                self.authority_requirement_rows,
                attr="authority_requirement_ref",
                field_name="authority_requirement_rows",
            ),
        )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        for target_ref in self.target_boundary_refs:
            _reject_glob_ref(target_ref, field_name="target_boundary_refs")
            _repo_ref(target_ref, field_name="target_boundary_refs")
        if self.execution_posture != "no_execution_performed_by_v78":
            raise ValueError("V78-A request rows must not perform execution")
        if self.tool_invocation_posture != "no_tool_invocation_performed_by_v78":
            raise ValueError("V78-A request rows must not invoke tools")
        if self.required_authority_source_refs and not self.authority_requirement_rows:
            raise ValueError("required authority source refs must resolve to row-shaped records")
        row_refs = {row.authority_requirement_ref for row in self.authority_requirement_rows}
        if set(self.required_authority_source_refs) != row_refs:
            raise ValueError("required authority source refs must match authority rows")
        for row in self.authority_requirement_rows:
            if row.candidate_ref != self.candidate_ref:
                raise ValueError("authority requirement rows must match request candidate")
        _reject_v78_action_claim(self.limitation_note, field_name="limitation_note")
        if self.authority_request_posture == "eligible_for_runtime_execution_authority_review":
            if self.requested_authority_horizon in {
                "future_product_runtime_review",
                "future_external_branch_runtime_review",
            }:
                raise ValueError("product/external pressure is not runtime-authority-ready")
            if not self.v77_authority_posture_refs:
                raise ValueError("eligible authority requests require V77 authority refs")
            if not self.v77_summary_refs:
                raise ValueError("eligible authority requests require V77 summary refs")
            if not self.v77_handoff_refs:
                raise ValueError("eligible authority requests require V77 handoff refs")
            if not self.v77_closeout_refs:
                raise ValueError("eligible authority requests require V77 closeout refs")
            authority_kinds = {row.authority_kind for row in self.authority_requirement_rows}
            if "runtime_execution_review_authority" not in authority_kinds:
                raise ValueError("eligible authority requests require runtime review authority")
            if "tool_use_review_authority" not in authority_kinds:
                raise ValueError("eligible authority requests require tool-use review authority")
        if self.requested_authority_horizon == "future_product_runtime_review":
            if self.authority_request_posture not in {
                "blocked_by_product_authority_gap",
                "future_family_only",
                "rejected_out_of_scope",
            }:
                raise ValueError("product pressure must remain product-blocked in V78-A")
            if not any(
                row.authority_kind == "product_authorization"
                for row in self.authority_requirement_rows
            ):
                raise ValueError("product pressure requires product authority blocker")
        if self.requested_authority_horizon == "future_external_branch_runtime_review":
            if self.authority_request_posture not in {
                "blocked_by_external_branch_gap",
                "future_family_only",
                "rejected_out_of_scope",
            }:
                raise ValueError("external branch pressure must remain blocked in V78-A")
            if not any(
                row.authority_kind == "external_branch_activation"
                for row in self.authority_requirement_rows
            ):
                raise ValueError("external branch pressure requires external authority blocker")
        if self.requested_command_scope_refs:
            raise ValueError("V78-A must not emit command-scope authorization refs")
        return self


class RepoRuntimeExecutionAuthorityRequest(_CartographyBase):
    schema: Literal["repo_runtime_execution_authority_request@1"] = (
        REPO_RUNTIME_EXECUTION_AUTHORITY_REQUEST_SCHEMA
    )
    runtime_execution_authority_request_id: str
    runtime_authority_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    request_rows: list[RepoRuntimeExecutionAuthorityRequestRow] = Field(min_length=1)
    runtime_authority_boundary_summary: str

    @model_validator(mode="after")
    def _validate_runtime_execution_authority_request(
        self,
    ) -> RepoRuntimeExecutionAuthorityRequest:
        object.__setattr__(
            self,
            "request_rows",
            _sorted_unique_by_ref(
                self.request_rows,
                attr="authority_request_ref",
                field_name="request_rows",
            ),
        )
        _require_terms(
            self.runtime_authority_boundary_summary,
            field_name="runtime_authority_boundary_summary",
            terms=("request", "no execution", "no tool invocation", "no release"),
        )
        expected_id = _surface_id(
            "repo_runtime_execution_authority_request",
            self.schema,
            self.model_dump(mode="json"),
            "runtime_execution_authority_request_id",
        )
        if self.runtime_execution_authority_request_id != expected_id:
            raise ValueError(
                "runtime_execution_authority_request_id does not match canonical hash"
            )
        return self


class RepoRuntimeAuthorityNonActionGuardrailRow(_CartographyBase):
    guardrail_ref: str
    candidate_ref: str
    authority_request_refs: list[str] = Field(min_length=1)
    forbidden_runtime_actions: list[RuntimeAuthorityForbiddenAction] = Field(min_length=1)
    forbidden_downstream_authority: list[RuntimeAuthorityForbiddenDownstreamAuthority] = Field(
        min_length=1
    )
    execution_posture: RuntimeAuthorityExecutionPosture
    tool_invocation_posture: RuntimeAuthorityToolInvocationPosture
    authority_gap_refs: list[str] = Field(default_factory=list)
    source_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_runtime_authority_guardrail_row(
        self,
    ) -> RepoRuntimeAuthorityNonActionGuardrailRow:
        _non_empty(self.guardrail_ref, field_name="guardrail_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "authority_request_refs",
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
        missing_actions = _FORBIDDEN_RUNTIME_ACTIONS.difference(
            self.forbidden_runtime_actions
        )
        if missing_actions:
            raise ValueError("runtime authority guardrail omits forbidden runtime actions")
        missing_authority = _FORBIDDEN_DOWNSTREAM_AUTHORITIES.difference(
            self.forbidden_downstream_authority
        )
        if missing_authority:
            raise ValueError("runtime authority guardrail omits forbidden downstream authority")
        if self.execution_posture != "no_execution_performed_by_v78":
            raise ValueError("runtime authority guardrails must preserve no-execution posture")
        if self.tool_invocation_posture != "no_tool_invocation_performed_by_v78":
            raise ValueError("runtime authority guardrails may not invoke tools")
        _reject_v78_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("no execution", "no tool invocation", "no release"),
        )
        return self


class RepoRuntimeAuthorityNonActionGuardrail(_CartographyBase):
    schema: Literal["repo_runtime_authority_non_action_guardrail@1"] = (
        REPO_RUNTIME_AUTHORITY_NON_ACTION_GUARDRAIL_SCHEMA
    )
    runtime_authority_non_action_guardrail_id: str
    runtime_execution_authority_request_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    guardrail_rows: list[RepoRuntimeAuthorityNonActionGuardrailRow] = Field(min_length=1)
    non_action_summary: str

    @model_validator(mode="after")
    def _validate_runtime_authority_guardrail(
        self,
    ) -> RepoRuntimeAuthorityNonActionGuardrail:
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
            self.non_action_summary,
            field_name="non_action_summary",
            terms=("no execution", "no tool invocation", "no release"),
        )
        expected_id = _surface_id(
            "repo_runtime_authority_non_action_guardrail",
            self.schema,
            self.model_dump(mode="json"),
            "runtime_authority_non_action_guardrail_id",
        )
        if self.runtime_authority_non_action_guardrail_id != expected_id:
            raise ValueError(
                "runtime_authority_non_action_guardrail_id does not match canonical hash"
            )
        return self


def derive_v78a_repo_runtime_authority_source_index(
    *, repo_root: Path | None = None
) -> RepoRuntimeAuthoritySourceIndex:
    _ = repo_root
    payload = {
        "schema": REPO_RUNTIME_AUTHORITY_SOURCE_INDEX_SCHEMA,
        "runtime_authority_source_index_id": "",
        "review_id": "review:v78a:runtime-execution-authority-request",
        "snapshot_id": "vNext+217-closed-on-main",
        "source_set_id": "source-set:v78a:released-v77c-runtime-authority-pressure",
        "source_rows": [
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus217/"
                    "repo_runtime_permission_authority_posture_v217_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_authority_source_role": "v77_authority_posture_source",
                "source_horizon": "Released V77-C runtime authority posture rows.",
                "limitation_note": (
                    "Eligibility source for authority request review only; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus217/"
                    "repo_runtime_permission_review_summary_v217_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_authority_source_role": "v77_runtime_summary_source",
                "source_horizon": "Released V77-C runtime review summary rows.",
                "limitation_note": (
                    "Eligibility source for authority request review only; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus217/"
                    "repo_post_runtime_permission_review_handoff_v217_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_authority_source_role": (
                    "v77_post_runtime_permission_review_handoff_source"
                ),
                "source_horizon": (
                    "Released V77-C post-runtime-permission-review handoff rows."
                ),
                "limitation_note": (
                    "Eligibility source for authority request review only; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus217/"
                    "repo_runtime_permission_family_closeout_alignment_v217_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_authority_source_role": "v77_family_closeout_source",
                "source_horizon": "Released V77 family closeout alignment rows.",
                "limitation_note": "Eligibility source for family boundary only; no execution.",
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus216/"
                    "repo_command_preflight_contract_v216_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_authority_source_role": "v77_command_preflight_context",
                "source_horizon": "Released V77-B command preflight context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus216/"
                    "repo_action_effect_envelope_v216_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_authority_source_role": "v77_effect_envelope_context",
                "source_horizon": "Released V77-B action-effect envelope context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus216/"
                    "repo_runtime_telemetry_requirement_v216_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_authority_source_role": "v77_telemetry_requirement_context",
                "source_horizon": "Released V77-B telemetry requirement context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus216/"
                    "repo_runtime_rollback_contract_v216_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_authority_source_role": "v77_rollback_contract_context",
                "source_horizon": "Released V77-B rollback contract context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "docs/support/arc_series_mapping/"
                    "V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_COMBINED_DOGFOOD_TEST_v0.json"
                ),
                "source_kind": "support_doc",
                "authority_layer": "support",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_authority_source_role": "combined_dogfood_source",
                "source_horizon": "Combined V68-V77 dogfood context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
            {
                "source_ref": _source_path("docs/LOCKED_CONTINUATION_vNEXT_PLUS218.md"),
                "source_kind": "planning_doc",
                "authority_layer": "lock",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_authority_source_role": "support_context",
                "source_horizon": "Active V78-A starter lock context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
        ],
        "runtime_authority_source_summary": (
            "Runtime authority source rows separate eligibility from context with "
            "no prose memory and no execution."
        ),
    }
    payload["source_rows"] = sorted(payload["source_rows"], key=lambda row: row["source_ref"])
    payload["runtime_authority_source_index_id"] = _surface_id(
        "repo_runtime_authority_source_index",
        REPO_RUNTIME_AUTHORITY_SOURCE_INDEX_SCHEMA,
        payload,
        "runtime_authority_source_index_id",
    )
    return RepoRuntimeAuthoritySourceIndex.model_validate(payload)


def _runtime_authority_requirement_rows_for_candidate(
    candidate_ref: str,
) -> list[RepoRuntimeAuthorityRequirementRow]:
    if candidate_ref == "candidate:internal:self_evidencing_workflow_type_emergence":
        rows = [
            {
                "authority_requirement_ref": "authority:v78a:self-evidencing:runtime-review",
                "candidate_ref": candidate_ref,
                "authority_kind": "runtime_execution_review_authority",
                "required_for_horizon": "bounded_repo_script_execution_review",
                "source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus217/"
                    "repo_runtime_permission_authority_posture_v217_reference.json",
                    "docs/LOCKED_CONTINUATION_vNEXT_PLUS218.md",
                ],
                "source_presence_posture": "present",
                "authority_gap_posture": "authority_gap_present",
                "limitation_note": (
                    "Runtime execution review authority remains required; no execution."
                ),
            },
            {
                "authority_requirement_ref": "authority:v78a:self-evidencing:tool-use-review",
                "candidate_ref": candidate_ref,
                "authority_kind": "tool_use_review_authority",
                "required_for_horizon": "bounded_tool_invocation_review",
                "source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus217/"
                    "repo_runtime_permission_authority_posture_v217_reference.json",
                    "docs/LOCKED_CONTINUATION_vNEXT_PLUS218.md",
                ],
                "source_presence_posture": "present",
                "authority_gap_posture": "authority_gap_present",
                "limitation_note": (
                    "Tool-use review authority remains required; no tool invocation."
                ),
            },
        ]
    elif candidate_ref == "candidate:internal:typed_adjudication_product_wedge":
        rows = [
            {
                "authority_requirement_ref": "authority:v78a:product-wedge:product-review",
                "candidate_ref": candidate_ref,
                "authority_kind": "product_authorization",
                "required_for_horizon": "future_product_runtime_review",
                "source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus217/"
                    "repo_runtime_permission_authority_posture_v217_reference.json",
                    "docs/LOCKED_CONTINUATION_vNEXT_PLUS218.md",
                ],
                "source_presence_posture": "present",
                "authority_gap_posture": "authority_gap_present",
                "limitation_note": "Product authorization remains required before product review.",
            }
        ]
    elif candidate_ref == "candidate:conditional:v43_external_branch":
        rows = [
            {
                "authority_requirement_ref": "authority:v78a:v43:external-branch",
                "candidate_ref": candidate_ref,
                "authority_kind": "external_branch_activation",
                "required_for_horizon": "future_external_branch_runtime_review",
                "source_refs": ["docs/LOCKED_CONTINUATION_vNEXT_PLUS218.md"],
                "source_presence_posture": "present",
                "authority_gap_posture": "authority_gap_present",
                "limitation_note": "External branch activation remains required before review.",
            }
        ]
    else:
        rows = []
    return [RepoRuntimeAuthorityRequirementRow.model_validate(row) for row in rows]


def derive_v78a_repo_runtime_execution_authority_request(
    *,
    repo_root: Path | None = None,
    runtime_authority_source_index: RepoRuntimeAuthoritySourceIndex | None = None,
) -> RepoRuntimeExecutionAuthorityRequest:
    _ = repo_root
    source_index = (
        runtime_authority_source_index
        or derive_v78a_repo_runtime_authority_source_index()
    )
    eligibility_sources = [
        row.source_ref
        for row in source_index.source_rows
        if row.runtime_authority_source_role in _ELIGIBILITY_SOURCE_ROLES
    ]
    context_sources = [
        row.source_ref
        for row in source_index.source_rows
        if row.runtime_authority_source_role in _CONTEXT_SOURCE_ROLES
    ]
    self_candidate = "candidate:internal:self_evidencing_workflow_type_emergence"
    product_candidate = "candidate:internal:typed_adjudication_product_wedge"
    self_authority_rows = _runtime_authority_requirement_rows_for_candidate(self_candidate)
    product_authority_rows = _runtime_authority_requirement_rows_for_candidate(product_candidate)
    payload = {
        "schema": REPO_RUNTIME_EXECUTION_AUTHORITY_REQUEST_SCHEMA,
        "runtime_execution_authority_request_id": "",
        "runtime_authority_source_index_id": source_index.runtime_authority_source_index_id,
        "review_id": source_index.review_id,
        "snapshot_id": source_index.snapshot_id,
        "source_set_id": source_index.source_set_id,
        "request_rows": [
            {
                "authority_request_ref": (
                    "authority-request:v78a:self-evidencing:runtime-execution-review"
                ),
                "candidate_ref": self_candidate,
                "source_refs": sorted([*eligibility_sources, *context_sources]),
                "v77_authority_posture_refs": [
                    "authority-posture:v77c:self-evidencing:runtime-execution",
                    "authority-posture:v77c:self-evidencing:tool-use",
                ],
                "v77_summary_refs": ["runtime-summary:v77c:self-evidencing:preflight"],
                "v77_handoff_refs": ["handoff:v77c:self-evidencing:preflight"],
                "v77_closeout_refs": [
                    "repo_runtime_permission_family_closeout_alignment_836d6f0ac44683ea0914ef7e"
                ],
                "requested_authority_horizon": "bounded_repo_script_execution_review",
                "authority_request_posture": "eligible_for_runtime_execution_authority_review",
                "requested_tool_use_refs": ["tool-use-request:v78a:self-evidencing:review-only"],
                "requested_command_scope_refs": [],
                "required_authority_source_refs": [
                    row.authority_requirement_ref for row in self_authority_rows
                ],
                "authority_requirement_rows": [
                    row.model_dump(mode="json") for row in self_authority_rows
                ],
                "target_boundary_refs": [
                    "packages/adeu_repo_description/src/adeu_repo_description/"
                    "runtime_execution_authority.py"
                ],
                "telemetry_requirement_refs": ["telemetry:v77b:self-evidencing:required"],
                "rollback_requirement_refs": ["rollback:v77b:self-evidencing:required"],
                "guardrail_refs": ["guardrail:v78a:self-evidencing:non-action"],
                "execution_posture": "no_execution_performed_by_v78",
                "tool_invocation_posture": "no_tool_invocation_performed_by_v78",
                "odeu_lanes": ["deontic", "epistemic", "utility"],
                "limitation_note": (
                    "Eligible for runtime execution authority request review only with "
                    "no execution, no tool invocation, and no release."
                ),
            },
            {
                "authority_request_ref": "authority-request:v78a:product-wedge:blocked",
                "candidate_ref": product_candidate,
                "source_refs": sorted([*eligibility_sources, *context_sources]),
                "v77_authority_posture_refs": [
                    "authority-posture:v77c:product-wedge:product-review"
                ],
                "v77_summary_refs": ["runtime-summary:v77c:product-wedge:blocked"],
                "v77_handoff_refs": ["handoff:v77c:product-wedge:blocked"],
                "v77_closeout_refs": [
                    "repo_runtime_permission_family_closeout_alignment_836d6f0ac44683ea0914ef7e"
                ],
                "requested_authority_horizon": "future_product_runtime_review",
                "authority_request_posture": "blocked_by_product_authority_gap",
                "requested_tool_use_refs": [],
                "requested_command_scope_refs": [],
                "required_authority_source_refs": [
                    row.authority_requirement_ref for row in product_authority_rows
                ],
                "authority_requirement_rows": [
                    row.model_dump(mode="json") for row in product_authority_rows
                ],
                "target_boundary_refs": [],
                "telemetry_requirement_refs": [],
                "rollback_requirement_refs": [],
                "guardrail_refs": ["guardrail:v78a:product-wedge:non-action"],
                "execution_posture": "no_execution_performed_by_v78",
                "tool_invocation_posture": "no_tool_invocation_performed_by_v78",
                "odeu_lanes": ["deontic", "utility"],
                "limitation_note": (
                    "Product pressure remains blocked by later product authority with "
                    "no execution, no tool invocation, and no release."
                ),
            },
        ],
        "runtime_authority_boundary_summary": (
            "Runtime execution authority request is request only: no execution, "
            "no tool invocation, no product authorization, and no release."
        ),
    }
    payload["request_rows"] = sorted(
        payload["request_rows"],
        key=lambda row: row["authority_request_ref"],
    )
    payload["runtime_execution_authority_request_id"] = _surface_id(
        "repo_runtime_execution_authority_request",
        REPO_RUNTIME_EXECUTION_AUTHORITY_REQUEST_SCHEMA,
        payload,
        "runtime_execution_authority_request_id",
    )
    return RepoRuntimeExecutionAuthorityRequest.model_validate(payload)


def derive_v78a_repo_runtime_authority_non_action_guardrail(
    *,
    repo_root: Path | None = None,
    runtime_execution_authority_request: RepoRuntimeExecutionAuthorityRequest | None = None,
) -> RepoRuntimeAuthorityNonActionGuardrail:
    _ = repo_root
    request = (
        runtime_execution_authority_request
        or derive_v78a_repo_runtime_execution_authority_request()
    )
    grouped_rows: dict[str, dict[str, object]] = {}
    for request_row in request.request_rows:
        for guardrail_ref in request_row.guardrail_refs:
            existing = grouped_rows.setdefault(
                guardrail_ref,
                {
                    "guardrail_ref": guardrail_ref,
                    "candidate_ref": request_row.candidate_ref,
                    "authority_request_refs": [],
                    "forbidden_runtime_actions": sorted(_FORBIDDEN_RUNTIME_ACTIONS),
                    "forbidden_downstream_authority": sorted(
                        _FORBIDDEN_DOWNSTREAM_AUTHORITIES
                    ),
                    "execution_posture": "no_execution_performed_by_v78",
                    "tool_invocation_posture": "no_tool_invocation_performed_by_v78",
                    "authority_gap_refs": [],
                    "source_refs": [],
                    "limitation_note": (
                        "This V78-A row is request only: no execution, no tool invocation, "
                        "no product authorization, no external branch activation, and no release."
                    ),
                },
            )
            if existing["candidate_ref"] != request_row.candidate_ref:
                raise ValueError("runtime authority guardrail derivation cannot merge candidates")
            existing["authority_request_refs"] = sorted(
                {
                    *existing["authority_request_refs"],
                    request_row.authority_request_ref,
                }
            )
            existing["authority_gap_refs"] = sorted(
                {
                    *existing["authority_gap_refs"],
                    *request_row.required_authority_source_refs,
                }
            )
            existing["source_refs"] = sorted(
                {*existing["source_refs"], *request_row.source_refs}
            )
    payload = {
        "schema": REPO_RUNTIME_AUTHORITY_NON_ACTION_GUARDRAIL_SCHEMA,
        "runtime_authority_non_action_guardrail_id": "",
        "runtime_execution_authority_request_id": (
            request.runtime_execution_authority_request_id
        ),
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
        "guardrail_rows": sorted(
            grouped_rows.values(),
            key=lambda row: row["guardrail_ref"],
        ),
        "non_action_summary": (
            "Runtime authority non-action guardrails preserve request only: "
            "no execution, no tool invocation, no product authorization, and no release."
        ),
    }
    payload["runtime_authority_non_action_guardrail_id"] = _surface_id(
        "repo_runtime_authority_non_action_guardrail",
        REPO_RUNTIME_AUTHORITY_NON_ACTION_GUARDRAIL_SCHEMA,
        payload,
        "runtime_authority_non_action_guardrail_id",
    )
    return RepoRuntimeAuthorityNonActionGuardrail.model_validate(payload)


def validate_v78a_runtime_execution_authority_bundle(
    *,
    runtime_authority_source_index: RepoRuntimeAuthoritySourceIndex,
    runtime_execution_authority_request: RepoRuntimeExecutionAuthorityRequest,
    runtime_authority_non_action_guardrail: RepoRuntimeAuthorityNonActionGuardrail,
) -> None:
    if (
        runtime_execution_authority_request.runtime_authority_source_index_id
        != runtime_authority_source_index.runtime_authority_source_index_id
    ):
        raise ValueError("runtime authority request must reference the source index")
    if (
        runtime_execution_authority_request.review_id,
        runtime_execution_authority_request.snapshot_id,
        runtime_execution_authority_request.source_set_id,
    ) != (
        runtime_authority_source_index.review_id,
        runtime_authority_source_index.snapshot_id,
        runtime_authority_source_index.source_set_id,
    ):
        raise ValueError("runtime authority request provenance must match source index")
    if (
        runtime_authority_non_action_guardrail.runtime_execution_authority_request_id
        != runtime_execution_authority_request.runtime_execution_authority_request_id
    ):
        raise ValueError("runtime authority guardrail must reference the request surface")
    if (
        runtime_authority_non_action_guardrail.review_id,
        runtime_authority_non_action_guardrail.snapshot_id,
        runtime_authority_non_action_guardrail.source_set_id,
    ) != (
        runtime_execution_authority_request.review_id,
        runtime_execution_authority_request.snapshot_id,
        runtime_execution_authority_request.source_set_id,
    ):
        raise ValueError("runtime authority guardrail provenance must match request")

    source_roles = {
        row.source_ref: row.runtime_authority_source_role
        for row in runtime_authority_source_index.source_rows
    }
    known_sources = set(source_roles)
    request_rows = {
        row.authority_request_ref: row
        for row in runtime_execution_authority_request.request_rows
    }
    guardrail_rows = {
        row.guardrail_ref: row
        for row in runtime_authority_non_action_guardrail.guardrail_rows
    }
    for request_row in runtime_execution_authority_request.request_rows:
        if any(source_ref not in known_sources for source_ref in request_row.source_refs):
            raise ValueError("runtime authority request source refs must be known")
        roles = {source_roles[source_ref] for source_ref in request_row.source_refs}
        if (
            request_row.authority_request_posture
            == "eligible_for_runtime_execution_authority_review"
        ):
            if not _ELIGIBILITY_SOURCE_ROLES.issubset(roles):
                raise ValueError(
                    "eligible runtime authority requests require released V77-C sources"
                )
        for requirement_row in request_row.authority_requirement_rows:
            if any(source_ref not in known_sources for source_ref in requirement_row.source_refs):
                raise ValueError("runtime authority requirement source refs must be known")
        if any(
            guardrail_ref not in guardrail_rows
            for guardrail_ref in request_row.guardrail_refs
        ):
            raise ValueError("runtime authority request guardrail refs must be known")
        for guardrail_ref in request_row.guardrail_refs:
            guardrail_row = guardrail_rows[guardrail_ref]
            if guardrail_row.candidate_ref != request_row.candidate_ref:
                raise ValueError("runtime authority guardrails must match candidate")
            if request_row.authority_request_ref not in guardrail_row.authority_request_refs:
                raise ValueError("runtime authority guardrails must reference request rows")
            if set(request_row.required_authority_source_refs) - set(
                guardrail_row.authority_gap_refs
            ):
                raise ValueError("runtime authority guardrails must carry authority gap refs")

    for guardrail_row in runtime_authority_non_action_guardrail.guardrail_rows:
        if any(source_ref not in known_sources for source_ref in guardrail_row.source_refs):
            raise ValueError("runtime authority guardrail source refs must be known")
        if any(ref not in request_rows for ref in guardrail_row.authority_request_refs):
            raise ValueError("guardrail authority request refs must be known")
        for ref in guardrail_row.authority_request_refs:
            if request_rows[ref].candidate_ref != guardrail_row.candidate_ref:
                raise ValueError("guardrail authority refs must match candidate")


def derive_v78a_runtime_execution_authority_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoRuntimeAuthoritySourceIndex,
    RepoRuntimeExecutionAuthorityRequest,
    RepoRuntimeAuthorityNonActionGuardrail,
]:
    source_index = derive_v78a_repo_runtime_authority_source_index(repo_root=repo_root)
    request = derive_v78a_repo_runtime_execution_authority_request(
        repo_root=repo_root,
        runtime_authority_source_index=source_index,
    )
    guardrail = derive_v78a_repo_runtime_authority_non_action_guardrail(
        repo_root=repo_root,
        runtime_execution_authority_request=request,
    )
    validate_v78a_runtime_execution_authority_bundle(
        runtime_authority_source_index=source_index,
        runtime_execution_authority_request=request,
        runtime_authority_non_action_guardrail=guardrail,
    )
    return source_index, request, guardrail


class RepoRuntimeExecutionAuthorityDecisionRow(_CartographyBase):
    authority_decision_ref: str
    authority_request_refs: list[str] = Field(min_length=1)
    candidate_ref: str
    decision_posture: RuntimeExecutionAuthorityDecisionPosture
    decision_horizon: RequestedRuntimeAuthorityHorizon
    authorized_surface_kind: RuntimeAuthorizedSurfaceKind
    authority_grant_horizon: RuntimeAuthorityGrantHorizon
    authority_source_refs: list[str] = Field(default_factory=list)
    authority_actor_refs: list[str] = Field(default_factory=list)
    tool_use_permission_refs: list[str] = Field(default_factory=list)
    command_scope_boundary_refs: list[str] = Field(default_factory=list)
    telemetry_requirement_refs: list[str] = Field(default_factory=list)
    rollback_requirement_refs: list[str] = Field(default_factory=list)
    exception_refs: list[str] = Field(default_factory=list)
    execution_posture: RuntimeAuthorityExecutionPosture
    execution_authorization_posture: RuntimeExecutionAuthorizationPosture
    non_action_guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_runtime_authority_decision_row(
        self,
    ) -> RepoRuntimeExecutionAuthorityDecisionRow:
        _non_empty(self.authority_decision_ref, field_name="authority_decision_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "authority_request_refs",
            "authority_source_refs",
            "authority_actor_refs",
            "tool_use_permission_refs",
            "command_scope_boundary_refs",
            "telemetry_requirement_refs",
            "rollback_requirement_refs",
            "exception_refs",
            "non_action_guardrail_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        if self.execution_posture != "no_execution_performed_by_v78":
            raise ValueError("runtime authority decisions must not perform execution")
        if self.execution_authorization_posture != "execution_not_authorized_by_v78":
            raise ValueError("V78-B decisions must not authorize execution")
        _reject_v78_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("later review", "no execution"),
        )
        if self.decision_posture in _GRANT_DECISION_POSTURES:
            if not self.authority_source_refs:
                raise ValueError("grant-like decisions require authority source refs")
            if not self.non_action_guardrail_refs:
                raise ValueError("grant-like decisions require non-action guardrails")
            if not self.command_scope_boundary_refs:
                raise ValueError("grant-like decisions require command-scope refs")
            if self.authorized_surface_kind not in _LATER_REVIEW_SURFACE_KINDS:
                raise ValueError("grant-like decisions require a later-review surface")
            if not self.authority_grant_horizon.startswith("later_"):
                raise ValueError("grant-like decisions require later-review-only horizon")
            if self.decision_horizon in {
                "future_product_runtime_review",
                "future_external_branch_runtime_review",
            }:
                raise ValueError("product/external pressure cannot be granted by V78-B")
        return self


class RepoRuntimeExecutionAuthorityDecision(_CartographyBase):
    schema: Literal["repo_runtime_execution_authority_decision@1"] = (
        REPO_RUNTIME_EXECUTION_AUTHORITY_DECISION_SCHEMA
    )
    runtime_execution_authority_decision_id: str
    runtime_execution_authority_request_id: str
    runtime_authority_non_action_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    decision_rows: list[RepoRuntimeExecutionAuthorityDecisionRow] = Field(min_length=1)
    authority_decision_summary: str

    @model_validator(mode="after")
    def _validate_runtime_authority_decision(
        self,
    ) -> RepoRuntimeExecutionAuthorityDecision:
        object.__setattr__(
            self,
            "decision_rows",
            _sorted_unique_by_ref(
                self.decision_rows,
                attr="authority_decision_ref",
                field_name="decision_rows",
            ),
        )
        _require_terms(
            self.authority_decision_summary,
            field_name="authority_decision_summary",
            terms=("later review", "no execution", "no tool invocation"),
        )
        expected_id = _surface_id(
            "repo_runtime_execution_authority_decision",
            self.schema,
            self.model_dump(mode="json"),
            "runtime_execution_authority_decision_id",
        )
        if self.runtime_execution_authority_decision_id != expected_id:
            raise ValueError(
                "runtime_execution_authority_decision_id does not match canonical hash"
            )
        return self


class RepoToolUsePermissionEnvelopeRow(_CartographyBase):
    tool_permission_ref: str
    authority_request_refs: list[str] = Field(min_length=1)
    candidate_ref: str
    tool_id: str
    tool_target_horizon: RequestedRuntimeAuthorityHorizon
    tool_target_refs: list[str] = Field(default_factory=list)
    permission_posture: ToolUsePermissionPosture
    permission_scope_boundary_refs: list[str] = Field(default_factory=list)
    authority_source_refs: list[str] = Field(default_factory=list)
    telemetry_requirement_refs: list[str] = Field(default_factory=list)
    rollback_requirement_refs: list[str] = Field(default_factory=list)
    exception_refs: list[str] = Field(default_factory=list)
    tool_invocation_posture: RuntimeAuthorityToolInvocationPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_tool_use_permission_row(self) -> RepoToolUsePermissionEnvelopeRow:
        _non_empty(self.tool_permission_ref, field_name="tool_permission_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        _non_empty(self.tool_id, field_name="tool_id")
        for field_name in (
            "authority_request_refs",
            "tool_target_refs",
            "permission_scope_boundary_refs",
            "authority_source_refs",
            "telemetry_requirement_refs",
            "rollback_requirement_refs",
            "exception_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for target_ref in self.tool_target_refs:
            _reject_glob_ref(target_ref, field_name="tool_target_refs")
            _repo_ref(target_ref, field_name="tool_target_refs")
        if self.tool_id in {"*", "global", "all_tools", "tool:*"}:
            raise ValueError("tool-use permission may not be global")
        if self.tool_invocation_posture != "no_tool_invocation_performed_by_v78":
            raise ValueError("tool-use permission envelopes must not invoke tools")
        _reject_v78_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("later review", "no tool invocation"),
        )
        if (
            self.permission_posture
            == "tool_use_permission_granted_for_later_execution_review"
        ):
            if not self.tool_target_refs:
                raise ValueError("tool-use permission grants require target refs")
            if not self.permission_scope_boundary_refs:
                raise ValueError("tool-use permission grants require scope boundary refs")
            if not self.authority_source_refs:
                raise ValueError("tool-use permission grants require authority refs")
        return self


class RepoToolUsePermissionEnvelope(_CartographyBase):
    schema: Literal["repo_tool_use_permission_envelope@1"] = (
        REPO_TOOL_USE_PERMISSION_ENVELOPE_SCHEMA
    )
    tool_use_permission_envelope_id: str
    runtime_execution_authority_request_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    permission_rows: list[RepoToolUsePermissionEnvelopeRow] = Field(min_length=1)
    tool_permission_summary: str

    @model_validator(mode="after")
    def _validate_tool_use_permission_envelope(
        self,
    ) -> RepoToolUsePermissionEnvelope:
        object.__setattr__(
            self,
            "permission_rows",
            _sorted_unique_by_ref(
                self.permission_rows,
                attr="tool_permission_ref",
                field_name="permission_rows",
            ),
        )
        _require_terms(
            self.tool_permission_summary,
            field_name="tool_permission_summary",
            terms=("target-bound", "later review", "no tool invocation"),
        )
        expected_id = _surface_id(
            "repo_tool_use_permission_envelope",
            self.schema,
            self.model_dump(mode="json"),
            "tool_use_permission_envelope_id",
        )
        if self.tool_use_permission_envelope_id != expected_id:
            raise ValueError("tool_use_permission_envelope_id does not match canonical hash")
        return self


class RepoCommandScopeAuthorizationBoundaryRow(_CartographyBase):
    command_scope_ref: str
    authority_request_refs: list[str] = Field(min_length=1)
    candidate_ref: str
    command_intent_kind: Literal[
        "no_command_intent",
        "shell_command_later_review",
        "python_tool_later_review",
        "repo_script_later_review",
        "api_call_later_review",
        "external_tool_later_review",
        "future_family_only",
    ]
    target_resolution_kind: RuntimeTargetResolutionKind
    target_refs: list[str] = Field(default_factory=list)
    authorized_scope_posture: RuntimeAuthorizedScopePosture
    allowed_effect_surface_refs: list[str] = Field(default_factory=list)
    forbidden_effect_surface_refs: list[str] = Field(default_factory=list)
    telemetry_requirement_refs: list[str] = Field(default_factory=list)
    rollback_requirement_refs: list[str] = Field(default_factory=list)
    authority_source_refs: list[str] = Field(default_factory=list)
    exception_refs: list[str] = Field(default_factory=list)
    execution_posture: RuntimeAuthorityExecutionPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_command_scope_boundary_row(
        self,
    ) -> RepoCommandScopeAuthorizationBoundaryRow:
        _non_empty(self.command_scope_ref, field_name="command_scope_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "authority_request_refs",
            "target_refs",
            "allowed_effect_surface_refs",
            "forbidden_effect_surface_refs",
            "telemetry_requirement_refs",
            "rollback_requirement_refs",
            "authority_source_refs",
            "exception_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for target_ref in self.target_refs:
            _reject_glob_ref(target_ref, field_name="target_refs")
            _repo_ref(target_ref, field_name="target_refs")
        if self.execution_posture != "no_execution_performed_by_v78":
            raise ValueError("command-scope boundaries must not perform execution")
        _reject_v78_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("later review", "no execution"),
        )
        if (
            self.authorized_scope_posture
            == "bounded_scope_authorized_for_later_execution_review"
        ):
            if not self.target_refs:
                raise ValueError("bounded command scope requires target refs")
            if self.target_resolution_kind == "no_target_boundary":
                raise ValueError("bounded command scope requires concrete targets")
            if not self.telemetry_requirement_refs:
                raise ValueError("bounded command scope requires telemetry refs")
            if not self.rollback_requirement_refs:
                raise ValueError("bounded command scope requires rollback refs")
            if not self.authority_source_refs:
                raise ValueError("bounded command scope requires authority refs")
        if (
            self.target_resolution_kind == "bounded_package_surface_with_child_refs"
            and not self.target_refs
        ):
            raise ValueError("bounded package surfaces require child target refs")
        return self


class RepoCommandScopeAuthorizationBoundary(_CartographyBase):
    schema: Literal["repo_command_scope_authorization_boundary@1"] = (
        REPO_COMMAND_SCOPE_AUTHORIZATION_BOUNDARY_SCHEMA
    )
    command_scope_authorization_boundary_id: str
    runtime_execution_authority_request_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    command_scope_rows: list[RepoCommandScopeAuthorizationBoundaryRow] = Field(
        min_length=1
    )
    command_scope_summary: str

    @model_validator(mode="after")
    def _validate_command_scope_boundary(
        self,
    ) -> RepoCommandScopeAuthorizationBoundary:
        object.__setattr__(
            self,
            "command_scope_rows",
            _sorted_unique_by_ref(
                self.command_scope_rows,
                attr="command_scope_ref",
                field_name="command_scope_rows",
            ),
        )
        _require_terms(
            self.command_scope_summary,
            field_name="command_scope_summary",
            terms=("later review", "concrete target", "no execution"),
        )
        expected_id = _surface_id(
            "repo_command_scope_authorization_boundary",
            self.schema,
            self.model_dump(mode="json"),
            "command_scope_authorization_boundary_id",
        )
        if self.command_scope_authorization_boundary_id != expected_id:
            raise ValueError(
                "command_scope_authorization_boundary_id does not match canonical hash"
            )
        return self


class RepoRuntimeAuthorityExceptionRegisterRow(_CartographyBase):
    exception_ref: str
    candidate_ref: str
    authority_request_refs: list[str] = Field(min_length=1)
    exception_kind: RuntimeAuthorityExceptionKind
    exception_posture: RuntimeAuthorityExceptionPosture
    blocking_surface_refs: list[str] = Field(default_factory=list)
    source_refs: list[str] = Field(min_length=1)
    required_next_surface: RuntimeAuthorityRequiredNextSurface
    limitation_note: str

    @model_validator(mode="after")
    def _validate_runtime_authority_exception_row(
        self,
    ) -> RepoRuntimeAuthorityExceptionRegisterRow:
        _non_empty(self.exception_ref, field_name="exception_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in ("authority_request_refs", "blocking_surface_refs", "source_refs"):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        _reject_v78_action_claim(self.limitation_note, field_name="limitation_note")
        lowered = self.limitation_note.lower()
        if "resolved by prose" in lowered or "command output resolves" in lowered:
            raise ValueError("runtime authority exceptions cannot be resolved by prose")
        if self.exception_posture == "blocking" and not self.blocking_surface_refs:
            raise ValueError("blocking exceptions require blocking surface refs")
        return self


class RepoRuntimeAuthorityExceptionRegister(_CartographyBase):
    schema: Literal["repo_runtime_authority_exception_register@1"] = (
        REPO_RUNTIME_AUTHORITY_EXCEPTION_REGISTER_SCHEMA
    )
    runtime_authority_exception_register_id: str
    runtime_execution_authority_request_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    exception_rows: list[RepoRuntimeAuthorityExceptionRegisterRow] = Field(min_length=1)
    exception_register_summary: str

    @model_validator(mode="after")
    def _validate_runtime_authority_exception_register(
        self,
    ) -> RepoRuntimeAuthorityExceptionRegister:
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
            self.exception_register_summary,
            field_name="exception_register_summary",
            terms=("exception", "no execution", "no prose"),
        )
        expected_id = _surface_id(
            "repo_runtime_authority_exception_register",
            self.schema,
            self.model_dump(mode="json"),
            "runtime_authority_exception_register_id",
        )
        if self.runtime_authority_exception_register_id != expected_id:
            raise ValueError(
                "runtime_authority_exception_register_id does not match canonical hash"
            )
        return self


def _request_row_by_candidate(
    request: RepoRuntimeExecutionAuthorityRequest,
    candidate_ref: str,
) -> RepoRuntimeExecutionAuthorityRequestRow:
    for row in request.request_rows:
        if row.candidate_ref == candidate_ref:
            return row
    raise ValueError(f"missing V78-A request row for {candidate_ref}")


def _v78b_base_request_bundle(
    runtime_execution_authority_request: RepoRuntimeExecutionAuthorityRequest | None,
    runtime_authority_non_action_guardrail: RepoRuntimeAuthorityNonActionGuardrail | None,
) -> tuple[RepoRuntimeExecutionAuthorityRequest, RepoRuntimeAuthorityNonActionGuardrail]:
    if runtime_execution_authority_request is None:
        _, request, guardrail = derive_v78a_runtime_execution_authority_bundle()
        return request, runtime_authority_non_action_guardrail or guardrail
    if runtime_authority_non_action_guardrail is None:
        guardrail = derive_v78a_repo_runtime_authority_non_action_guardrail(
            runtime_execution_authority_request=runtime_execution_authority_request,
        )
        return runtime_execution_authority_request, guardrail
    return runtime_execution_authority_request, runtime_authority_non_action_guardrail


def derive_v78b_repo_runtime_authority_exception_register(
    *,
    repo_root: Path | None = None,
    runtime_execution_authority_request: RepoRuntimeExecutionAuthorityRequest | None = None,
) -> RepoRuntimeAuthorityExceptionRegister:
    _ = repo_root
    request, _guardrail = _v78b_base_request_bundle(
        runtime_execution_authority_request,
        None,
    )
    self_candidate = "candidate:internal:self_evidencing_workflow_type_emergence"
    product_candidate = "candidate:internal:typed_adjudication_product_wedge"
    self_request = _request_row_by_candidate(request, self_candidate)
    product_request = _request_row_by_candidate(request, product_candidate)
    payload = {
        "schema": REPO_RUNTIME_AUTHORITY_EXCEPTION_REGISTER_SCHEMA,
        "runtime_authority_exception_register_id": "",
        "runtime_execution_authority_request_id": request.runtime_execution_authority_request_id,
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
        "exception_rows": [
            {
                "exception_ref": "exception:v78b:self-evidencing:review-only-warning",
                "candidate_ref": self_candidate,
                "authority_request_refs": [self_request.authority_request_ref],
                "exception_kind": "unknown_needs_review",
                "exception_posture": "warning_only",
                "blocking_surface_refs": [
                    "authority-decision:v78b:self-evidencing:later-execution-review",
                    "command-scope:v78b:self-evidencing:runtime-authority-module",
                ],
                "source_refs": self_request.source_refs,
                "required_next_surface": "later_execution_review_surface",
                "limitation_note": (
                    "Exception is visible for later review only; no execution and "
                    "no prose resolution."
                ),
            },
            {
                "exception_ref": "exception:v78b:product-wedge:product-authority-gap",
                "candidate_ref": product_candidate,
                "authority_request_refs": [product_request.authority_request_ref],
                "exception_kind": "product_authority_gap",
                "exception_posture": "blocking",
                "blocking_surface_refs": [
                    "authority-decision:v78b:product-wedge:future-family-only"
                ],
                "source_refs": product_request.source_refs,
                "required_next_surface": "future_product_review",
                "limitation_note": (
                    "Product authority gap remains blocking for later review only; "
                    "no execution and no prose resolution."
                ),
            },
        ],
        "exception_register_summary": (
            "Runtime authority exception register keeps exception rows visible with "
            "no execution and no prose resolution."
        ),
    }
    payload["exception_rows"] = sorted(
        payload["exception_rows"],
        key=lambda row: row["exception_ref"],
    )
    payload["runtime_authority_exception_register_id"] = _surface_id(
        "repo_runtime_authority_exception_register",
        REPO_RUNTIME_AUTHORITY_EXCEPTION_REGISTER_SCHEMA,
        payload,
        "runtime_authority_exception_register_id",
    )
    return RepoRuntimeAuthorityExceptionRegister.model_validate(payload)


def derive_v78b_repo_command_scope_authorization_boundary(
    *,
    repo_root: Path | None = None,
    runtime_execution_authority_request: RepoRuntimeExecutionAuthorityRequest | None = None,
    runtime_authority_exception_register: RepoRuntimeAuthorityExceptionRegister | None = None,
) -> RepoCommandScopeAuthorizationBoundary:
    _ = repo_root
    request, _guardrail = _v78b_base_request_bundle(
        runtime_execution_authority_request,
        None,
    )
    exceptions = (
        runtime_authority_exception_register
        or derive_v78b_repo_runtime_authority_exception_register(
            runtime_execution_authority_request=request,
        )
    )
    known_exceptions = {row.exception_ref for row in exceptions.exception_rows}
    self_candidate = "candidate:internal:self_evidencing_workflow_type_emergence"
    product_candidate = "candidate:internal:typed_adjudication_product_wedge"
    self_request = _request_row_by_candidate(request, self_candidate)
    product_request = _request_row_by_candidate(request, product_candidate)
    payload = {
        "schema": REPO_COMMAND_SCOPE_AUTHORIZATION_BOUNDARY_SCHEMA,
        "command_scope_authorization_boundary_id": "",
        "runtime_execution_authority_request_id": request.runtime_execution_authority_request_id,
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
        "command_scope_rows": [
            {
                "command_scope_ref": (
                    "command-scope:v78b:self-evidencing:runtime-authority-module"
                ),
                "authority_request_refs": [self_request.authority_request_ref],
                "candidate_ref": self_candidate,
                "command_intent_kind": "repo_script_later_review",
                "target_resolution_kind": "concrete_file_ref",
                "target_refs": self_request.target_boundary_refs,
                "authorized_scope_posture": (
                    "bounded_scope_authorized_for_later_execution_review"
                ),
                "allowed_effect_surface_refs": [
                    "effect-surface:v78b:self-evidencing:review-only-schema-and-fixture"
                ],
                "forbidden_effect_surface_refs": sorted([
                    "effect-surface:v78b:command-execution",
                    "effect-surface:v78b:tool-invocation",
                    "effect-surface:v78b:release",
                ]),
                "telemetry_requirement_refs": self_request.telemetry_requirement_refs,
                "rollback_requirement_refs": self_request.rollback_requirement_refs,
                "authority_source_refs": self_request.required_authority_source_refs,
                "exception_refs": sorted(
                    {
                        "exception:v78b:self-evidencing:review-only-warning"
                    }.intersection(known_exceptions)
                ),
                "execution_posture": "no_execution_performed_by_v78",
                "limitation_note": (
                    "Command scope is bounded for later review with concrete target refs; "
                    "no execution and no target mutation in V78."
                ),
            },
            {
                "command_scope_ref": "command-scope:v78b:product-wedge:no-target",
                "authority_request_refs": [product_request.authority_request_ref],
                "candidate_ref": product_candidate,
                "command_intent_kind": "future_family_only",
                "target_resolution_kind": "no_target_boundary",
                "target_refs": [],
                "authorized_scope_posture": "scope_future_family_only",
                "allowed_effect_surface_refs": [],
                "forbidden_effect_surface_refs": sorted([
                    "effect-surface:v78b:product-authorization",
                    "effect-surface:v78b:release",
                ]),
                "telemetry_requirement_refs": [],
                "rollback_requirement_refs": [],
                "authority_source_refs": product_request.required_authority_source_refs,
                "exception_refs": sorted(
                    {
                        "exception:v78b:product-wedge:product-authority-gap"
                    }.intersection(known_exceptions)
                ),
                "execution_posture": "no_execution_performed_by_v78",
                "limitation_note": (
                    "Product wedge command scope is future-family-only for later review; "
                    "no execution and no product authorization."
                ),
            },
        ],
        "command_scope_summary": (
            "Command scope boundaries are later review records with concrete target "
            "constraints and no execution."
        ),
    }
    payload["command_scope_rows"] = sorted(
        payload["command_scope_rows"],
        key=lambda row: row["command_scope_ref"],
    )
    payload["command_scope_authorization_boundary_id"] = _surface_id(
        "repo_command_scope_authorization_boundary",
        REPO_COMMAND_SCOPE_AUTHORIZATION_BOUNDARY_SCHEMA,
        payload,
        "command_scope_authorization_boundary_id",
    )
    return RepoCommandScopeAuthorizationBoundary.model_validate(payload)


def derive_v78b_repo_tool_use_permission_envelope(
    *,
    repo_root: Path | None = None,
    runtime_execution_authority_request: RepoRuntimeExecutionAuthorityRequest | None = None,
    command_scope_authorization_boundary: RepoCommandScopeAuthorizationBoundary | None = None,
    runtime_authority_exception_register: RepoRuntimeAuthorityExceptionRegister | None = None,
) -> RepoToolUsePermissionEnvelope:
    _ = repo_root
    request, _guardrail = _v78b_base_request_bundle(
        runtime_execution_authority_request,
        None,
    )
    exceptions = (
        runtime_authority_exception_register
        or derive_v78b_repo_runtime_authority_exception_register(
            runtime_execution_authority_request=request,
        )
    )
    command_scope = (
        command_scope_authorization_boundary
        or derive_v78b_repo_command_scope_authorization_boundary(
            runtime_execution_authority_request=request,
            runtime_authority_exception_register=exceptions,
        )
    )
    command_scope_by_candidate = {
        row.candidate_ref: row.command_scope_ref for row in command_scope.command_scope_rows
    }
    known_exceptions = {row.exception_ref for row in exceptions.exception_rows}
    self_candidate = "candidate:internal:self_evidencing_workflow_type_emergence"
    product_candidate = "candidate:internal:typed_adjudication_product_wedge"
    self_request = _request_row_by_candidate(request, self_candidate)
    product_request = _request_row_by_candidate(request, product_candidate)
    payload = {
        "schema": REPO_TOOL_USE_PERMISSION_ENVELOPE_SCHEMA,
        "tool_use_permission_envelope_id": "",
        "runtime_execution_authority_request_id": request.runtime_execution_authority_request_id,
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
        "permission_rows": [
            {
                "tool_permission_ref": "tool-permission:v78b:self-evidencing:python-review",
                "authority_request_refs": [self_request.authority_request_ref],
                "candidate_ref": self_candidate,
                "tool_id": "tool:python-review-runtime-description",
                "tool_target_horizon": "bounded_tool_invocation_review",
                "tool_target_refs": self_request.target_boundary_refs,
                "permission_posture": (
                    "tool_use_permission_granted_for_later_execution_review"
                ),
                "permission_scope_boundary_refs": [
                    command_scope_by_candidate[self_candidate]
                ],
                "authority_source_refs": [
                    ref
                    for ref in self_request.required_authority_source_refs
                    if "tool-use" in ref
                ],
                "telemetry_requirement_refs": self_request.telemetry_requirement_refs,
                "rollback_requirement_refs": self_request.rollback_requirement_refs,
                "exception_refs": sorted(
                    {
                        "exception:v78b:self-evidencing:review-only-warning"
                    }.intersection(known_exceptions)
                ),
                "tool_invocation_posture": "no_tool_invocation_performed_by_v78",
                "limitation_note": (
                    "Tool-use permission is target-bound for later review only with "
                    "no tool invocation."
                ),
            },
            {
                "tool_permission_ref": "tool-permission:v78b:product-wedge:not-applicable",
                "authority_request_refs": [product_request.authority_request_ref],
                "candidate_ref": product_candidate,
                "tool_id": "tool:none-product-authority-blocked",
                "tool_target_horizon": "future_product_runtime_review",
                "tool_target_refs": [],
                "permission_posture": "tool_use_not_applicable",
                "permission_scope_boundary_refs": [
                    command_scope_by_candidate[product_candidate]
                ],
                "authority_source_refs": product_request.required_authority_source_refs,
                "telemetry_requirement_refs": [],
                "rollback_requirement_refs": [],
                "exception_refs": sorted(
                    {
                        "exception:v78b:product-wedge:product-authority-gap"
                    }.intersection(known_exceptions)
                ),
                "tool_invocation_posture": "no_tool_invocation_performed_by_v78",
                "limitation_note": (
                    "Product wedge tool-use permission is not applicable pending later "
                    "review with no tool invocation."
                ),
            },
        ],
        "tool_permission_summary": (
            "Tool-use permission envelopes are target-bound later review records "
            "with no tool invocation."
        ),
    }
    payload["permission_rows"] = sorted(
        payload["permission_rows"],
        key=lambda row: row["tool_permission_ref"],
    )
    payload["tool_use_permission_envelope_id"] = _surface_id(
        "repo_tool_use_permission_envelope",
        REPO_TOOL_USE_PERMISSION_ENVELOPE_SCHEMA,
        payload,
        "tool_use_permission_envelope_id",
    )
    return RepoToolUsePermissionEnvelope.model_validate(payload)


def derive_v78b_repo_runtime_execution_authority_decision(
    *,
    repo_root: Path | None = None,
    runtime_execution_authority_request: RepoRuntimeExecutionAuthorityRequest | None = None,
    runtime_authority_non_action_guardrail: RepoRuntimeAuthorityNonActionGuardrail | None = None,
    tool_use_permission_envelope: RepoToolUsePermissionEnvelope | None = None,
    command_scope_authorization_boundary: RepoCommandScopeAuthorizationBoundary | None = None,
    runtime_authority_exception_register: RepoRuntimeAuthorityExceptionRegister | None = None,
) -> RepoRuntimeExecutionAuthorityDecision:
    _ = repo_root
    request, guardrail = _v78b_base_request_bundle(
        runtime_execution_authority_request,
        runtime_authority_non_action_guardrail,
    )
    exceptions = (
        runtime_authority_exception_register
        or derive_v78b_repo_runtime_authority_exception_register(
            runtime_execution_authority_request=request,
        )
    )
    command_scope = (
        command_scope_authorization_boundary
        or derive_v78b_repo_command_scope_authorization_boundary(
            runtime_execution_authority_request=request,
            runtime_authority_exception_register=exceptions,
        )
    )
    tool_permission = (
        tool_use_permission_envelope
        or derive_v78b_repo_tool_use_permission_envelope(
            runtime_execution_authority_request=request,
            command_scope_authorization_boundary=command_scope,
            runtime_authority_exception_register=exceptions,
        )
    )
    command_scope_by_candidate = {
        row.candidate_ref: row.command_scope_ref for row in command_scope.command_scope_rows
    }
    tool_permission_by_candidate = {
        row.candidate_ref: row.tool_permission_ref for row in tool_permission.permission_rows
    }
    exception_by_candidate = {
        row.candidate_ref: row.exception_ref for row in exceptions.exception_rows
    }
    self_candidate = "candidate:internal:self_evidencing_workflow_type_emergence"
    product_candidate = "candidate:internal:typed_adjudication_product_wedge"
    self_request = _request_row_by_candidate(request, self_candidate)
    product_request = _request_row_by_candidate(request, product_candidate)
    payload = {
        "schema": REPO_RUNTIME_EXECUTION_AUTHORITY_DECISION_SCHEMA,
        "runtime_execution_authority_decision_id": "",
        "runtime_execution_authority_request_id": request.runtime_execution_authority_request_id,
        "runtime_authority_non_action_guardrail_id": (
            guardrail.runtime_authority_non_action_guardrail_id
        ),
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
        "decision_rows": [
            {
                "authority_decision_ref": (
                    "authority-decision:v78b:self-evidencing:later-execution-review"
                ),
                "authority_request_refs": [self_request.authority_request_ref],
                "candidate_ref": self_candidate,
                "decision_posture": (
                    "review_authority_granted_for_bounded_execution_surface"
                ),
                "decision_horizon": "bounded_repo_script_execution_review",
                "authorized_surface_kind": "later_execution_review_surface",
                "authority_grant_horizon": "later_execution_review_only",
                "authority_source_refs": self_request.required_authority_source_refs,
                "authority_actor_refs": ["authority-actor:v78b:maintainer-review-source"],
                "tool_use_permission_refs": [tool_permission_by_candidate[self_candidate]],
                "command_scope_boundary_refs": [command_scope_by_candidate[self_candidate]],
                "telemetry_requirement_refs": self_request.telemetry_requirement_refs,
                "rollback_requirement_refs": self_request.rollback_requirement_refs,
                "exception_refs": [exception_by_candidate[self_candidate]],
                "execution_posture": "no_execution_performed_by_v78",
                "execution_authorization_posture": "execution_not_authorized_by_v78",
                "non_action_guardrail_refs": self_request.guardrail_refs,
                "limitation_note": (
                    "Decision grants only a bounded later review surface with "
                    "no execution and no tool invocation."
                ),
            },
            {
                "authority_decision_ref": (
                    "authority-decision:v78b:product-wedge:future-family-only"
                ),
                "authority_request_refs": [product_request.authority_request_ref],
                "candidate_ref": product_candidate,
                "decision_posture": "review_authority_future_family_only",
                "decision_horizon": "future_product_runtime_review",
                "authorized_surface_kind": "future_family_review_surface",
                "authority_grant_horizon": "future_family_review_only",
                "authority_source_refs": product_request.required_authority_source_refs,
                "authority_actor_refs": [],
                "tool_use_permission_refs": [tool_permission_by_candidate[product_candidate]],
                "command_scope_boundary_refs": [command_scope_by_candidate[product_candidate]],
                "telemetry_requirement_refs": [],
                "rollback_requirement_refs": [],
                "exception_refs": [exception_by_candidate[product_candidate]],
                "execution_posture": "no_execution_performed_by_v78",
                "execution_authorization_posture": "execution_not_authorized_by_v78",
                "non_action_guardrail_refs": product_request.guardrail_refs,
                "limitation_note": (
                    "Product pressure is future-family-only for later review with "
                    "no execution and no product authorization."
                ),
            },
        ],
        "authority_decision_summary": (
            "Runtime execution authority decisions are later review records only: "
            "no execution, no tool invocation, and no release."
        ),
    }
    payload["decision_rows"] = sorted(
        payload["decision_rows"],
        key=lambda row: row["authority_decision_ref"],
    )
    payload["runtime_execution_authority_decision_id"] = _surface_id(
        "repo_runtime_execution_authority_decision",
        REPO_RUNTIME_EXECUTION_AUTHORITY_DECISION_SCHEMA,
        payload,
        "runtime_execution_authority_decision_id",
    )
    return RepoRuntimeExecutionAuthorityDecision.model_validate(payload)


def validate_v78b_runtime_execution_authority_bundle(
    *,
    runtime_execution_authority_request: RepoRuntimeExecutionAuthorityRequest,
    runtime_authority_non_action_guardrail: RepoRuntimeAuthorityNonActionGuardrail,
    runtime_execution_authority_decision: RepoRuntimeExecutionAuthorityDecision,
    tool_use_permission_envelope: RepoToolUsePermissionEnvelope,
    command_scope_authorization_boundary: RepoCommandScopeAuthorizationBoundary,
    runtime_authority_exception_register: RepoRuntimeAuthorityExceptionRegister,
) -> None:
    if (
        runtime_execution_authority_decision.runtime_execution_authority_request_id
        != runtime_execution_authority_request.runtime_execution_authority_request_id
    ):
        raise ValueError("runtime authority decisions must reference V78-A requests")
    if (
        runtime_execution_authority_decision.runtime_authority_non_action_guardrail_id
        != runtime_authority_non_action_guardrail.runtime_authority_non_action_guardrail_id
    ):
        raise ValueError("runtime authority decisions must reference V78-A guardrails")
    for surface_name, surface in (
        ("tool-use permission", tool_use_permission_envelope),
        ("command-scope boundary", command_scope_authorization_boundary),
        ("runtime authority exception", runtime_authority_exception_register),
    ):
        if (
            surface.runtime_execution_authority_request_id
            != runtime_execution_authority_request.runtime_execution_authority_request_id
        ):
            raise ValueError(f"{surface_name} surface must reference V78-A requests")
        if (
            surface.review_id,
            surface.snapshot_id,
            surface.source_set_id,
        ) != (
            runtime_execution_authority_request.review_id,
            runtime_execution_authority_request.snapshot_id,
            runtime_execution_authority_request.source_set_id,
        ):
            raise ValueError(f"{surface_name} provenance must match V78-A requests")

    request_rows = {
        row.authority_request_ref: row
        for row in runtime_execution_authority_request.request_rows
    }
    request_candidate_by_ref = {
        row.authority_request_ref: row.candidate_ref
        for row in runtime_execution_authority_request.request_rows
    }
    request_source_refs = {
        source_ref
        for row in runtime_execution_authority_request.request_rows
        for source_ref in row.source_refs
    }
    authority_requirement_refs = {
        authority_ref
        for row in runtime_execution_authority_request.request_rows
        for authority_ref in row.required_authority_source_refs
    }
    guardrail_rows = {
        row.guardrail_ref: row
        for row in runtime_authority_non_action_guardrail.guardrail_rows
    }
    permission_rows = {
        row.tool_permission_ref: row for row in tool_use_permission_envelope.permission_rows
    }
    command_scope_rows = {
        row.command_scope_ref: row
        for row in command_scope_authorization_boundary.command_scope_rows
    }
    exception_rows = {
        row.exception_ref: row for row in runtime_authority_exception_register.exception_rows
    }

    for row in command_scope_authorization_boundary.command_scope_rows:
        if any(ref not in request_rows for ref in row.authority_request_refs):
            raise ValueError("command-scope rows must reference known V78-A requests")
        for ref in row.authority_request_refs:
            if request_candidate_by_ref[ref] != row.candidate_ref:
                raise ValueError("command-scope rows must preserve request candidate")
        if any(ref not in authority_requirement_refs for ref in row.authority_source_refs):
            raise ValueError("command-scope authority refs must be V78-A authority refs")
        if any(ref not in exception_rows for ref in row.exception_refs):
            raise ValueError("command-scope exception refs must be known")

    for row in tool_use_permission_envelope.permission_rows:
        if any(ref not in request_rows for ref in row.authority_request_refs):
            raise ValueError("tool permission rows must reference known V78-A requests")
        for ref in row.authority_request_refs:
            if request_candidate_by_ref[ref] != row.candidate_ref:
                raise ValueError("tool permission rows must preserve request candidate")
        if any(ref not in command_scope_rows for ref in row.permission_scope_boundary_refs):
            raise ValueError("tool permission scope refs must be known")
        if any(ref not in authority_requirement_refs for ref in row.authority_source_refs):
            raise ValueError("tool permission authority refs must be V78-A authority refs")
        if any(ref not in exception_rows for ref in row.exception_refs):
            raise ValueError("tool permission exception refs must be known")

    for row in runtime_authority_exception_register.exception_rows:
        if any(ref not in request_rows for ref in row.authority_request_refs):
            raise ValueError("runtime authority exceptions must reference known requests")
        for ref in row.authority_request_refs:
            if request_candidate_by_ref[ref] != row.candidate_ref:
                raise ValueError("runtime authority exceptions must preserve request candidate")
        if any(ref not in request_source_refs for ref in row.source_refs):
            raise ValueError("runtime authority exception source refs must be V78-A sources")
        known_blocking_refs = {
            *request_rows,
            *command_scope_rows,
            *permission_rows,
            *exception_rows,
            *{
                decision.authority_decision_ref
                for decision in runtime_execution_authority_decision.decision_rows
            },
        }
        if any(ref not in known_blocking_refs for ref in row.blocking_surface_refs):
            raise ValueError("runtime authority exception blocking refs must be known")

    for row in runtime_execution_authority_decision.decision_rows:
        if any(ref not in request_rows for ref in row.authority_request_refs):
            raise ValueError("runtime authority decisions must reference known requests")
        for ref in row.authority_request_refs:
            if request_candidate_by_ref[ref] != row.candidate_ref:
                raise ValueError("runtime authority decisions must preserve request candidate")
        if any(ref not in guardrail_rows for ref in row.non_action_guardrail_refs):
            raise ValueError("runtime authority decisions must reference known guardrails")
        for ref in row.non_action_guardrail_refs:
            if guardrail_rows[ref].candidate_ref != row.candidate_ref:
                raise ValueError("runtime authority decision guardrails must match candidate")
        if any(ref not in authority_requirement_refs for ref in row.authority_source_refs):
            raise ValueError("runtime authority decision source refs must be V78-A authority refs")
        if any(ref not in permission_rows for ref in row.tool_use_permission_refs):
            raise ValueError("runtime authority decisions must reference known tool permissions")
        if any(ref not in command_scope_rows for ref in row.command_scope_boundary_refs):
            raise ValueError("runtime authority decisions must reference known command scopes")
        if any(ref not in exception_rows for ref in row.exception_refs):
            raise ValueError("runtime authority decisions must reference known exceptions")
        if row.decision_posture in _GRANT_DECISION_POSTURES:
            for command_scope_ref in row.command_scope_boundary_refs:
                command_scope = command_scope_rows[command_scope_ref]
                if (
                    command_scope.authorized_scope_posture
                    != "bounded_scope_authorized_for_later_execution_review"
                ):
                    raise ValueError("grant-like decisions require bounded command scope")
            for tool_permission_ref in row.tool_use_permission_refs:
                tool_permission = permission_rows[tool_permission_ref]
                if (
                    tool_permission.permission_posture
                    != "tool_use_permission_granted_for_later_execution_review"
                ):
                    raise ValueError("grant-like decisions require bounded tool permission")


def derive_v78b_runtime_execution_authority_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoRuntimeExecutionAuthorityRequest,
    RepoRuntimeAuthorityNonActionGuardrail,
    RepoRuntimeAuthorityExceptionRegister,
    RepoCommandScopeAuthorizationBoundary,
    RepoToolUsePermissionEnvelope,
    RepoRuntimeExecutionAuthorityDecision,
]:
    _source_index, request, guardrail = derive_v78a_runtime_execution_authority_bundle(
        repo_root=repo_root
    )
    exceptions = derive_v78b_repo_runtime_authority_exception_register(
        repo_root=repo_root,
        runtime_execution_authority_request=request,
    )
    command_scope = derive_v78b_repo_command_scope_authorization_boundary(
        repo_root=repo_root,
        runtime_execution_authority_request=request,
        runtime_authority_exception_register=exceptions,
    )
    tool_permission = derive_v78b_repo_tool_use_permission_envelope(
        repo_root=repo_root,
        runtime_execution_authority_request=request,
        command_scope_authorization_boundary=command_scope,
        runtime_authority_exception_register=exceptions,
    )
    decision = derive_v78b_repo_runtime_execution_authority_decision(
        repo_root=repo_root,
        runtime_execution_authority_request=request,
        runtime_authority_non_action_guardrail=guardrail,
        tool_use_permission_envelope=tool_permission,
        command_scope_authorization_boundary=command_scope,
        runtime_authority_exception_register=exceptions,
    )
    validate_v78b_runtime_execution_authority_bundle(
        runtime_execution_authority_request=request,
        runtime_authority_non_action_guardrail=guardrail,
        runtime_execution_authority_decision=decision,
        tool_use_permission_envelope=tool_permission,
        command_scope_authorization_boundary=command_scope,
        runtime_authority_exception_register=exceptions,
    )
    return request, guardrail, exceptions, command_scope, tool_permission, decision
