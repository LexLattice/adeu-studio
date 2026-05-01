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
    for telemetry_row in runtime_telemetry_requirement.telemetry_requirement_rows:
        for preflight_ref in telemetry_row.preflight_refs:
            if preflight_ref not in preflight_rows:
                raise ValueError("telemetry preflight refs must be known")
        for effect_ref in telemetry_row.effect_envelope_refs:
            if effect_ref not in effect_rows:
                raise ValueError("telemetry effect envelope refs must be known")
    for rollback_row in runtime_rollback_contract.rollback_contract_rows:
        for preflight_ref in rollback_row.preflight_refs:
            if preflight_ref not in preflight_rows:
                raise ValueError("rollback preflight refs must be known")
        for effect_ref in rollback_row.effect_envelope_refs:
            if effect_ref not in effect_rows:
                raise ValueError("rollback effect envelope refs must be known")


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
