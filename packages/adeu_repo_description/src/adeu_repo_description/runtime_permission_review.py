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

REPO_RUNTIME_PERMISSION_REVIEW_REQUEST_SCHEMA = "repo_runtime_permission_review_request@1"
REPO_RUNTIME_PERMISSION_SOURCE_INDEX_SCHEMA = "repo_runtime_permission_source_index@1"
REPO_RUNTIME_NON_EXECUTION_GUARDRAIL_SCHEMA = "repo_runtime_non_execution_guardrail@1"

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


def _reject_runtime_authority_claim(value: str, *, field_name: str) -> str:
    lowered = value.lower()
    forbidden = [
        "runtime permission granted",
        "grants runtime",
        "permission to run",
        "command executed",
        "command output proves",
        "tool use authorized",
        "assign worker",
        "dispatch worker",
        "open pr",
        "commit now",
        "merge now",
        "release now",
        "product authorized",
        "external branch activated",
        "external submission",
        "benchmark truth",
        "model selected",
        "policy amended",
    ]
    negation_markers = ("no ", "not ", "without ", "forbidden ", "non-")
    for phrase in forbidden:
        index = lowered.find(phrase)
        if index == -1:
            continue
        prefix = lowered[max(0, index - 18) : index]
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
    rows = []
    for request_row in request.request_rows:
        rows.append(
            {
                "guardrail_ref": request_row.guardrail_refs[0],
                "candidate_ref": request_row.candidate_ref,
                "runtime_review_refs": [request_row.runtime_review_ref],
                "forbidden_runtime_actions": sorted(_FORBIDDEN_RUNTIME_ACTIONS),
                "forbidden_downstream_authority": sorted(_FORBIDDEN_DOWNSTREAM_AUTHORITIES),
                "execution_posture": "no_execution_authorized",
                "tool_use_posture": "tool_use_not_authorized_by_v77",
                "authority_gap_refs": request_row.required_later_authority_refs,
                "source_refs": request_row.source_refs,
                "limitation_note": (
                    "This V77-A row is review only: no command execution, no runtime "
                    "permission, no tool-use permission, no product authorization, "
                    "no external branch activation, and no release."
                ),
            }
        )
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
