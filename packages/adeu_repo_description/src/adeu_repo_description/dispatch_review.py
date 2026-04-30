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
                "external_branch_review_later",
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
            raise ValueError("external branch review requires later V43 branch posture source")
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
                    ["future_product_review", "future_family_review"]
                    if request_row.requested_orchestration_horizon == "product_review_later"
                    else ["v75b_worker_orchestration_review", "v75c_reconciliation_review"]
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
        dispatch_non_execution_guardrail.dispatch_review_request_id
        != dispatch_review_request.dispatch_review_request_id
    ):
        raise ValueError("dispatch guardrail must reference the request surface")

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
            if guardrail_rows[guardrail_ref].candidate_ref != request_row.candidate_ref:
                raise ValueError("dispatch request guardrails must match candidate")

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
