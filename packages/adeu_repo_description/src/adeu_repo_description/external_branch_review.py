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

REPO_EXTERNAL_BRANCH_REVIEW_REQUEST_SCHEMA = "repo_external_branch_review_request@1"
REPO_EXTERNAL_BRANCH_SOURCE_INDEX_SCHEMA = "repo_external_branch_source_index@1"
REPO_EXTERNAL_BRANCH_NON_ACTIVATION_GUARDRAIL_SCHEMA = (
    "repo_external_branch_non_activation_guardrail@1"
)

ExternalBranchSourceRole = Literal[
    "v79_controlled_execution_summary_source",
    "v79_post_controlled_execution_review_handoff_source",
    "v79_family_closeout_source",
    "v79_combined_dogfood_context",
    "post_v74_roadmap_context",
    "v43_branch_posture_source",
    "v43_branch_posture_absence_marker",
    "external_objective_source",
    "support_process_context",
    "absence_marker",
]
ExternalBranchPostureCurrentness = Literal[
    "current_branch_posture",
    "historical_branch_planning_context",
    "explicit_absence_marker",
    "stale_or_superseded",
    "unknown_needs_review",
]
ExternalObjectiveKind = Literal[
    "arc_contest_participation_review",
    "external_benchmark_review",
    "external_corpus_ingestion_review",
    "external_tool_endpoint_review",
    "product_externalization_review",
    "external_result_claim_review",
    "future_family_only",
]
ExternalBranchReviewPosture = Literal[
    "request_recorded_objective_only",
    "eligible_for_external_branch_review",
    "blocked_by_missing_source",
    "blocked_by_missing_v43_branch_posture",
    "blocked_by_missing_external_objective",
    "blocked_by_product_authority_gap",
    "blocked_by_runtime_authority_gap",
    "future_family_only",
    "rejected_out_of_scope",
]
ExternalBranchRequestedHorizon = Literal[
    "data_boundary_required_later",
    "tool_boundary_required_later",
    "submission_authority_required_later",
    "not_selected_in_v80a",
    "blocked_by_missing_v43_branch_posture",
    "blocked_by_missing_authority",
    "future_family_only",
]
ExternalBranchRequirementPosture = Literal[
    "required_for_later_review",
    "not_selected_in_v80a",
    "not_applicable",
    "blocked_by_missing_v43_branch_posture",
    "blocked_by_missing_authority",
    "future_family_only",
]
ExternalActivationPosture = Literal[
    "no_external_branch_activation_performed_by_v80",
    "external_activation_requires_later_family",
    "external_activation_forbidden_by_this_family",
]
ExternalSubmissionPosture = Literal[
    "no_external_submission_performed_by_v80",
    "submission_requires_later_family",
    "submission_forbidden_by_this_family",
]
ExternalToolInvocationPosture = Literal[
    "no_external_tool_invocation_performed_by_v80",
    "external_tool_invocation_requires_later_family",
    "external_tool_invocation_forbidden_by_this_family",
]
ExternalBranchExecutionPosture = Literal[
    "no_execution_performed_by_v80",
    "execution_requires_later_family",
    "execution_forbidden_by_this_family",
]
ExternalForbiddenAction = Literal[
    "activate_external_branch",
    "enter_v43_contest",
    "submit_externally",
    "invoke_external_tool_for_effect",
    "mutate_external_endpoint",
    "transfer_external_data",
    "claim_external_result_truth",
    "run_command",
    "invoke_tool_for_effect",
    "assign_worker",
    "dispatch_worker",
    "open_pr",
    "commit",
    "merge",
    "release",
]
ExternalForbiddenDownstreamAuthority = Literal[
    "external_branch_activation",
    "v43_contest_participation",
    "external_submission",
    "external_tool_invocation",
    "external_result_truth",
    "product_authorization",
    "released_truth",
    "benchmark_truth",
    "model_selection",
    "living_memory_authority",
    "recursive_policy_amendment",
    "v81_selection",
]

_V79_ELIGIBILITY_SOURCE_ROLES = {
    "v79_controlled_execution_summary_source",
    "v79_post_controlled_execution_review_handoff_source",
    "v79_family_closeout_source",
}
_CONTEXT_SOURCE_ROLES = {
    "v79_combined_dogfood_context",
    "post_v74_roadmap_context",
    "support_process_context",
}
_ABSENCE_SOURCE_ROLES = {"v43_branch_posture_absence_marker", "absence_marker"}
_FORBIDDEN_EXTERNAL_ACTIONS = {
    "activate_external_branch",
    "enter_v43_contest",
    "submit_externally",
    "invoke_external_tool_for_effect",
    "mutate_external_endpoint",
    "transfer_external_data",
    "claim_external_result_truth",
    "run_command",
    "invoke_tool_for_effect",
    "assign_worker",
    "dispatch_worker",
    "open_pr",
    "commit",
    "merge",
    "release",
}
_FORBIDDEN_DOWNSTREAM_AUTHORITIES = {
    "external_branch_activation",
    "v43_contest_participation",
    "external_submission",
    "external_tool_invocation",
    "external_result_truth",
    "product_authorization",
    "released_truth",
    "benchmark_truth",
    "model_selection",
    "living_memory_authority",
    "recursive_policy_amendment",
    "v81_selection",
}


def _source_path(path: str) -> str:
    _repo_ref(path, field_name="source_ref")
    return path


def _require_terms(value: str, *, field_name: str, terms: tuple[str, ...]) -> str:
    lowered = value.lower()
    missing = [term for term in terms if term not in lowered]
    if missing:
        raise ValueError(f"{field_name} must mention {', '.join(missing)}")
    return value


def _reject_v80_action_claim(value: str, *, field_name: str) -> str:
    lowered = value.lower()
    forbidden_patterns = [
        r"external branch (?:is |was |has been |gets |got )?activated",
        r"activate external branch",
        r"v43 contest (?:is |was |has been |gets |got )?entered",
        r"enter v43 contest",
        r"external submission (?:is |was |has been |gets |got )?made",
        r"submit externally",
        r"external tool (?:is |was |has been |gets |got )?invoked",
        r"invoke external tool",
        r"external endpoint (?:is |was |has been |gets |got )?mutated",
        r"external data (?:is |was |has been |gets |got )?transferred",
        r"external result truth",
        r"command (?:is |was |has been |gets |got )?executed",
        r"run command",
        r"tool (?:is |was |has been |gets |got )?invoked",
        r"dispatch worker",
        r"product (?:is |was |has been |gets |got )?authorized",
        r"release now",
        r"v81 (?:is |was |has been |gets |got )?selected",
    ]
    negation_markers = ("no ", "not ", "without ", "forbidden ", "non-")
    for pattern in forbidden_patterns:
        match = re.search(pattern, lowered)
        if match is None:
            continue
        prefix = lowered[max(0, match.start() - 24) : match.start()]
        if not any(marker in prefix for marker in negation_markers):
            raise ValueError(f"{field_name} may not carry external branch activation")
    return value


class RepoExternalBranchSourceRow(_CartographyBase):
    source_ref: str
    source_kind: CandidateSourceKind
    authority_layer: CandidateAuthorityLayer
    source_status: SourceStatus
    source_presence_posture: CandidateSourcePresencePosture
    external_branch_source_role: ExternalBranchSourceRole
    source_horizon: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_external_branch_source_row(self) -> RepoExternalBranchSourceRow:
        _repo_ref(self.source_ref, field_name="source_ref")
        _non_empty(self.source_horizon, field_name="source_horizon")
        _reject_v80_action_claim(self.limitation_note, field_name="limitation_note")
        if (
            self.external_branch_source_role not in _ABSENCE_SOURCE_ROLES
            and self.source_presence_posture != "present"
        ):
            raise ValueError("non-absence external branch source rows must be present")
        if (
            self.external_branch_source_role in _ABSENCE_SOURCE_ROLES
            and self.source_presence_posture == "present"
        ):
            raise ValueError("absence-marker external branch rows must not be present sources")
        if (
            self.external_branch_source_role in _CONTEXT_SOURCE_ROLES
            and self.authority_layer == "lock"
            and self.source_kind == "support_doc"
        ):
            raise ValueError("support context may not be marked as lock authority")
        return self


class RepoExternalBranchSourceIndex(_CartographyBase):
    schema: Literal["repo_external_branch_source_index@1"] = (
        REPO_EXTERNAL_BRANCH_SOURCE_INDEX_SCHEMA
    )
    external_branch_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    source_rows: list[RepoExternalBranchSourceRow] = Field(min_length=1)
    external_branch_source_summary: str

    @model_validator(mode="after")
    def _validate_external_branch_source_index(self) -> RepoExternalBranchSourceIndex:
        object.__setattr__(
            self,
            "source_rows",
            _sorted_unique_by_ref(self.source_rows, attr="source_ref", field_name="source_rows"),
        )
        _non_empty(self.review_id, field_name="review_id")
        _non_empty(self.snapshot_id, field_name="snapshot_id")
        _non_empty(self.source_set_id, field_name="source_set_id")
        _require_terms(
            self.external_branch_source_summary,
            field_name="external_branch_source_summary",
            terms=("eligibility", "context", "no external activation"),
        )
        expected_id = _surface_id(
            "repo_external_branch_source_index",
            self.schema,
            self.model_dump(mode="json"),
            "external_branch_source_index_id",
        )
        if self.external_branch_source_index_id != expected_id:
            raise ValueError("external_branch_source_index_id does not match canonical hash")
        return self


class RepoExternalBranchReviewRequestRow(_CartographyBase):
    external_branch_review_request_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    v79_summary_refs: list[str] = Field(default_factory=list)
    v79_handoff_refs: list[str] = Field(default_factory=list)
    v79_closeout_refs: list[str] = Field(default_factory=list)
    branch_family_ref: str
    branch_posture_currentness: ExternalBranchPostureCurrentness
    external_objective_kind: ExternalObjectiveKind
    branch_review_posture: ExternalBranchReviewPosture
    requested_data_boundary_horizon: ExternalBranchRequestedHorizon
    requested_tool_boundary_horizon: ExternalBranchRequestedHorizon
    requested_submission_authority_horizon: ExternalBranchRequestedHorizon
    required_result_provenance_posture: ExternalBranchRequirementPosture
    required_withdrawal_posture: ExternalBranchRequirementPosture
    required_authority_refs: list[str] = Field(default_factory=list)
    guardrail_refs: list[str] = Field(min_length=1)
    external_activation_posture: ExternalActivationPosture
    external_submission_posture: ExternalSubmissionPosture
    external_tool_invocation_posture: ExternalToolInvocationPosture
    execution_posture: ExternalBranchExecutionPosture
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_external_branch_review_request_row(
        self,
    ) -> RepoExternalBranchReviewRequestRow:
        _non_empty(
            self.external_branch_review_request_ref,
            field_name="external_branch_review_request_ref",
        )
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        _non_empty(self.branch_family_ref, field_name="branch_family_ref")
        for field_name in (
            "source_refs",
            "v79_summary_refs",
            "v79_handoff_refs",
            "v79_closeout_refs",
            "required_authority_refs",
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
        if self.external_activation_posture != "no_external_branch_activation_performed_by_v80":
            raise ValueError("V80-A request rows must not activate external branches")
        if self.external_submission_posture != "no_external_submission_performed_by_v80":
            raise ValueError("V80-A request rows must not submit externally")
        if (
            self.external_tool_invocation_posture
            != "no_external_tool_invocation_performed_by_v80"
        ):
            raise ValueError("V80-A request rows must not invoke external tools")
        if self.execution_posture != "no_execution_performed_by_v80":
            raise ValueError("V80-A request rows must not perform execution")
        _reject_v80_action_claim(self.limitation_note, field_name="limitation_note")
        if self.branch_review_posture == "eligible_for_external_branch_review":
            if self.branch_posture_currentness != "current_branch_posture":
                raise ValueError("eligible external branch review requires current branch posture")
            if not self.v79_summary_refs and not self.v79_handoff_refs:
                raise ValueError("eligible external branch review requests require V79-C refs")
            if not any("v43" in ref.lower() or "external" in ref for ref in self.source_refs):
                raise ValueError("eligible external branch review requests require branch source")
            for field_name in (
                "requested_data_boundary_horizon",
                "requested_tool_boundary_horizon",
                "requested_submission_authority_horizon",
            ):
                if getattr(self, field_name) not in {
                    "data_boundary_required_later",
                    "tool_boundary_required_later",
                    "submission_authority_required_later",
                }:
                    raise ValueError("eligible external branch review requests require horizons")
        if self.branch_review_posture == "request_recorded_objective_only":
            if self.branch_posture_currentness == "current_branch_posture":
                raise ValueError("objective-only rows must not claim current branch posture")
        if self.external_objective_kind == "product_externalization_review":
            if self.branch_review_posture not in {
                "blocked_by_product_authority_gap",
                "future_family_only",
                "rejected_out_of_scope",
            }:
                raise ValueError("product pressure must remain blocked in V80-A")
            if not any("product" in ref for ref in self.required_authority_refs):
                raise ValueError("product pressure requires product authority blocker")
        return self


class RepoExternalBranchReviewRequest(_CartographyBase):
    schema: Literal["repo_external_branch_review_request@1"] = (
        REPO_EXTERNAL_BRANCH_REVIEW_REQUEST_SCHEMA
    )
    external_branch_review_request_id: str
    external_branch_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    request_rows: list[RepoExternalBranchReviewRequestRow] = Field(min_length=1)
    external_branch_boundary_summary: str

    @model_validator(mode="after")
    def _validate_external_branch_review_request(self) -> RepoExternalBranchReviewRequest:
        object.__setattr__(
            self,
            "request_rows",
            _sorted_unique_by_ref(
                self.request_rows,
                attr="external_branch_review_request_ref",
                field_name="request_rows",
            ),
        )
        _require_terms(
            self.external_branch_boundary_summary,
            field_name="external_branch_boundary_summary",
            terms=("review", "no external activation", "no external submission", "no release"),
        )
        expected_id = _surface_id(
            "repo_external_branch_review_request",
            self.schema,
            self.model_dump(mode="json"),
            "external_branch_review_request_id",
        )
        if self.external_branch_review_request_id != expected_id:
            raise ValueError("external_branch_review_request_id does not match canonical hash")
        return self


class RepoExternalBranchNonActivationGuardrailRow(_CartographyBase):
    guardrail_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    external_branch_review_request_refs: list[str] = Field(min_length=1)
    forbidden_external_actions: list[ExternalForbiddenAction] = Field(min_length=1)
    forbidden_downstream_authority: list[ExternalForbiddenDownstreamAuthority] = Field(
        min_length=1
    )
    guardrail_posture: Literal["non_activation_guardrail_active"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_external_branch_guardrail_row(
        self,
    ) -> RepoExternalBranchNonActivationGuardrailRow:
        _non_empty(self.guardrail_ref, field_name="guardrail_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "external_branch_review_request_refs",
            "forbidden_external_actions",
            "forbidden_downstream_authority",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        missing_actions = _FORBIDDEN_EXTERNAL_ACTIONS.difference(
            self.forbidden_external_actions
        )
        if missing_actions:
            raise ValueError("external branch guardrail omits forbidden external actions")
        missing_authority = _FORBIDDEN_DOWNSTREAM_AUTHORITIES.difference(
            self.forbidden_downstream_authority
        )
        if missing_authority:
            raise ValueError("external branch guardrail omits forbidden downstream authority")
        _reject_v80_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("no external activation", "no external submission", "no release"),
        )
        return self


class RepoExternalBranchNonActivationGuardrail(_CartographyBase):
    schema: Literal["repo_external_branch_non_activation_guardrail@1"] = (
        REPO_EXTERNAL_BRANCH_NON_ACTIVATION_GUARDRAIL_SCHEMA
    )
    external_branch_non_activation_guardrail_id: str
    external_branch_review_request_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    guardrail_rows: list[RepoExternalBranchNonActivationGuardrailRow] = Field(min_length=1)
    non_activation_summary: str

    @model_validator(mode="after")
    def _validate_external_branch_guardrail(
        self,
    ) -> RepoExternalBranchNonActivationGuardrail:
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
            self.non_activation_summary,
            field_name="non_activation_summary",
            terms=("no external activation", "no external submission", "no release"),
        )
        expected_id = _surface_id(
            "repo_external_branch_non_activation_guardrail",
            self.schema,
            self.model_dump(mode="json"),
            "external_branch_non_activation_guardrail_id",
        )
        if self.external_branch_non_activation_guardrail_id != expected_id:
            raise ValueError(
                "external_branch_non_activation_guardrail_id does not match canonical hash"
            )
        return self


def derive_v80a_repo_external_branch_source_index(
    *, repo_root: Path | None = None
) -> RepoExternalBranchSourceIndex:
    _ = repo_root
    payload = {
        "schema": REPO_EXTERNAL_BRANCH_SOURCE_INDEX_SCHEMA,
        "external_branch_source_index_id": "",
        "review_id": "review:v80a:external-branch-review",
        "snapshot_id": "vNext+223-controlled-execution-review-closeout",
        "source_set_id": "source-set:v80a:released-v79c-external-branch-pressure",
        "source_rows": [
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus223/"
                    "repo_controlled_execution_review_summary_v223_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "external_branch_source_role": "v79_controlled_execution_summary_source",
                "source_horizon": "Released V79-C controlled execution review summary rows.",
                "limitation_note": (
                    "Eligibility context for external branch review only; "
                    "no external activation."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus223/"
                    "repo_post_controlled_execution_review_handoff_v223_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "external_branch_source_role": (
                    "v79_post_controlled_execution_review_handoff_source"
                ),
                "source_horizon": "Released V79-C post-controlled-execution handoff rows.",
                "limitation_note": (
                    "Eligibility context for external branch review only; "
                    "no external activation."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus223/"
                    "repo_controlled_execution_review_family_closeout_alignment_v223_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "external_branch_source_role": "v79_family_closeout_source",
                "source_horizon": "Released V79 family closeout alignment rows.",
                "limitation_note": (
                    "Family closeout context for review boundary only; "
                    "no external activation."
                ),
            },
            {
                "source_ref": _source_path(
                    "docs/support/arc_series_mapping/"
                    "V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_"
                    "COMBINED_DOGFOOD_TEST_v0.json"
                ),
                "source_kind": "support_doc",
                "authority_layer": "support",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "external_branch_source_role": "v79_combined_dogfood_context",
                "source_horizon": "Combined V68-V79 dogfood context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; "
                    "no external activation."
                ),
            },
            {
                "source_ref": _source_path("docs/DRAFT_MULTI_ARC_ROADMAP_POST_V74_v0.md"),
                "source_kind": "planning_doc",
                "authority_layer": "planning",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "external_branch_source_role": "post_v74_roadmap_context",
                "source_horizon": "Post-V74 multi-arc roadmap context.",
                "limitation_note": (
                    "Roadmap context only and not sufficient for eligibility; "
                    "no external activation."
                ),
            },
            {
                "source_ref": _source_path("docs/DRAFT_NEXT_ARC_OPTIONS_v43.md"),
                "source_kind": "planning_doc",
                "authority_layer": "planning",
                "source_status": "available_but_not_integrated",
                "source_presence_posture": "present",
                "external_branch_source_role": "support_process_context",
                "source_horizon": "Historical V43 branch planning context.",
                "limitation_note": (
                    "Historical context only; not current branch posture and "
                    "no external activation."
                ),
            },
            {
                "source_ref": "external-branch-posture:v43:current:absent",
                "source_kind": "external_artifact",
                "authority_layer": "support",
                "source_status": "review_pending_input",
                "source_presence_posture": "external_unavailable",
                "external_branch_source_role": "v43_branch_posture_absence_marker",
                "source_horizon": "Current V43 external branch posture is absent.",
                "limitation_note": (
                    "Explicit absence marker only; no external activation."
                ),
            },
        ],
        "external_branch_source_summary": (
            "External branch source rows separate eligibility from context with "
            "no external activation and no prose memory."
        ),
    }
    payload["source_rows"] = sorted(payload["source_rows"], key=lambda row: row["source_ref"])
    payload["external_branch_source_index_id"] = _surface_id(
        "repo_external_branch_source_index",
        REPO_EXTERNAL_BRANCH_SOURCE_INDEX_SCHEMA,
        payload,
        "external_branch_source_index_id",
    )
    return RepoExternalBranchSourceIndex.model_validate(payload)


def derive_v80a_repo_external_branch_review_request(
    *,
    repo_root: Path | None = None,
    external_branch_source_index: RepoExternalBranchSourceIndex | None = None,
) -> RepoExternalBranchReviewRequest:
    _ = repo_root
    source_index = external_branch_source_index or derive_v80a_repo_external_branch_source_index()
    source_refs = [row.source_ref for row in source_index.source_rows]
    self_candidate = "candidate:internal:self_evidencing_workflow_type_emergence"
    product_candidate = "candidate:internal:typed_adjudication_product_wedge"
    payload = {
        "schema": REPO_EXTERNAL_BRANCH_REVIEW_REQUEST_SCHEMA,
        "external_branch_review_request_id": "",
        "external_branch_source_index_id": source_index.external_branch_source_index_id,
        "review_id": source_index.review_id,
        "snapshot_id": source_index.snapshot_id,
        "source_set_id": source_index.source_set_id,
        "request_rows": [
            {
                "external_branch_review_request_ref": (
                    "external-branch-review:v80a:self-evidencing:v43-blocked"
                ),
                "candidate_ref": self_candidate,
                "source_refs": sorted(source_refs),
                "v79_summary_refs": [
                    "controlled-execution-summary:v79c:self-evidencing:review-package"
                ],
                "v79_handoff_refs": [
                    "handoff:v79c:self-evidencing:future-execution-trial-review"
                ],
                "v79_closeout_refs": [
                    "repo_controlled_execution_review_family_closeout_alignment_c529594bf82f3e0b681d8cbc"
                ],
                "branch_family_ref": "V43",
                "branch_posture_currentness": "explicit_absence_marker",
                "external_objective_kind": "arc_contest_participation_review",
                "branch_review_posture": "blocked_by_missing_v43_branch_posture",
                "requested_data_boundary_horizon": "blocked_by_missing_v43_branch_posture",
                "requested_tool_boundary_horizon": "blocked_by_missing_v43_branch_posture",
                "requested_submission_authority_horizon": (
                    "blocked_by_missing_v43_branch_posture"
                ),
                "required_result_provenance_posture": (
                    "blocked_by_missing_v43_branch_posture"
                ),
                "required_withdrawal_posture": "blocked_by_missing_v43_branch_posture",
                "required_authority_refs": ["external-branch-posture:v43:current:absent"],
                "guardrail_refs": ["guardrail:v80a:self-evidencing:non-activation"],
                "external_activation_posture": (
                    "no_external_branch_activation_performed_by_v80"
                ),
                "external_submission_posture": "no_external_submission_performed_by_v80",
                "external_tool_invocation_posture": (
                    "no_external_tool_invocation_performed_by_v80"
                ),
                "execution_posture": "no_execution_performed_by_v80",
                "odeu_lanes": ["deontic", "epistemic", "utility"],
                "limitation_note": (
                    "External branch review is blocked by missing current V43 "
                    "posture with no external activation, no external submission, "
                    "and no release."
                ),
            },
            {
                "external_branch_review_request_ref": (
                    "external-branch-review:v80a:product-wedge:out-of-scope"
                ),
                "candidate_ref": product_candidate,
                "source_refs": sorted(source_refs),
                "v79_summary_refs": ["controlled-execution-summary:v79c:product-wedge:blocked"],
                "v79_handoff_refs": ["handoff:v79c:product-wedge:future-product-review"],
                "v79_closeout_refs": [
                    "repo_controlled_execution_review_family_closeout_alignment_c529594bf82f3e0b681d8cbc"
                ],
                "branch_family_ref": "V80",
                "branch_posture_currentness": "explicit_absence_marker",
                "external_objective_kind": "product_externalization_review",
                "branch_review_posture": "blocked_by_product_authority_gap",
                "requested_data_boundary_horizon": "future_family_only",
                "requested_tool_boundary_horizon": "future_family_only",
                "requested_submission_authority_horizon": "future_family_only",
                "required_result_provenance_posture": "future_family_only",
                "required_withdrawal_posture": "not_applicable",
                "required_authority_refs": ["authority:v78a:product-wedge:product-review"],
                "guardrail_refs": ["guardrail:v80a:product-wedge:non-activation"],
                "external_activation_posture": (
                    "no_external_branch_activation_performed_by_v80"
                ),
                "external_submission_posture": "no_external_submission_performed_by_v80",
                "external_tool_invocation_posture": (
                    "no_external_tool_invocation_performed_by_v80"
                ),
                "execution_posture": "no_execution_performed_by_v80",
                "odeu_lanes": ["deontic", "utility"],
                "limitation_note": (
                    "Product pressure remains blocked by product authority with "
                    "no external activation, no external submission, and no release."
                ),
            },
        ],
        "external_branch_boundary_summary": (
            "External branch review request is review only: no external activation, "
            "no external submission, no external tool invocation, and no release."
        ),
    }
    payload["request_rows"] = sorted(
        payload["request_rows"],
        key=lambda row: row["external_branch_review_request_ref"],
    )
    payload["external_branch_review_request_id"] = _surface_id(
        "repo_external_branch_review_request",
        REPO_EXTERNAL_BRANCH_REVIEW_REQUEST_SCHEMA,
        payload,
        "external_branch_review_request_id",
    )
    return RepoExternalBranchReviewRequest.model_validate(payload)


def derive_v80a_repo_external_branch_non_activation_guardrail(
    *,
    repo_root: Path | None = None,
    external_branch_review_request: RepoExternalBranchReviewRequest | None = None,
) -> RepoExternalBranchNonActivationGuardrail:
    _ = repo_root
    request = external_branch_review_request or derive_v80a_repo_external_branch_review_request()
    grouped_rows: dict[str, dict[str, object]] = {}
    for request_row in request.request_rows:
        for guardrail_ref in request_row.guardrail_refs:
            existing = grouped_rows.setdefault(
                guardrail_ref,
                {
                    "guardrail_ref": guardrail_ref,
                    "candidate_ref": request_row.candidate_ref,
                    "source_refs": [],
                    "external_branch_review_request_refs": [],
                    "forbidden_external_actions": sorted(_FORBIDDEN_EXTERNAL_ACTIONS),
                    "forbidden_downstream_authority": sorted(
                        _FORBIDDEN_DOWNSTREAM_AUTHORITIES
                    ),
                    "guardrail_posture": "non_activation_guardrail_active",
                    "limitation_note": (
                        "This V80-A row is review only: no external activation, "
                        "no external submission, no external tool invocation, "
                        "no product authorization, and no release."
                    ),
                },
            )
            if existing["candidate_ref"] != request_row.candidate_ref:
                raise ValueError("external branch guardrail cannot merge candidates")
            existing["external_branch_review_request_refs"] = sorted(
                {
                    *existing["external_branch_review_request_refs"],
                    request_row.external_branch_review_request_ref,
                }
            )
            existing["source_refs"] = sorted({*existing["source_refs"], *request_row.source_refs})
    payload = {
        "schema": REPO_EXTERNAL_BRANCH_NON_ACTIVATION_GUARDRAIL_SCHEMA,
        "external_branch_non_activation_guardrail_id": "",
        "external_branch_review_request_id": request.external_branch_review_request_id,
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
        "guardrail_rows": sorted(grouped_rows.values(), key=lambda row: row["guardrail_ref"]),
        "non_activation_summary": (
            "External branch non-activation guardrails preserve review only: "
            "no external activation, no external submission, and no release."
        ),
    }
    payload["external_branch_non_activation_guardrail_id"] = _surface_id(
        "repo_external_branch_non_activation_guardrail",
        REPO_EXTERNAL_BRANCH_NON_ACTIVATION_GUARDRAIL_SCHEMA,
        payload,
        "external_branch_non_activation_guardrail_id",
    )
    return RepoExternalBranchNonActivationGuardrail.model_validate(payload)


def validate_v80a_external_branch_review_bundle(
    *,
    external_branch_source_index: RepoExternalBranchSourceIndex,
    external_branch_review_request: RepoExternalBranchReviewRequest,
    external_branch_non_activation_guardrail: RepoExternalBranchNonActivationGuardrail,
) -> None:
    if (
        external_branch_review_request.external_branch_source_index_id
        != external_branch_source_index.external_branch_source_index_id
    ):
        raise ValueError("external branch request must reference the source index")
    if (
        external_branch_review_request.review_id,
        external_branch_review_request.snapshot_id,
        external_branch_review_request.source_set_id,
    ) != (
        external_branch_source_index.review_id,
        external_branch_source_index.snapshot_id,
        external_branch_source_index.source_set_id,
    ):
        raise ValueError("external branch request provenance must match source index")
    if (
        external_branch_non_activation_guardrail.external_branch_review_request_id
        != external_branch_review_request.external_branch_review_request_id
    ):
        raise ValueError("external branch guardrail must reference the request surface")

    source_roles = {
        row.source_ref: row.external_branch_source_role
        for row in external_branch_source_index.source_rows
    }
    known_sources = set(source_roles)
    request_rows = {
        row.external_branch_review_request_ref: row
        for row in external_branch_review_request.request_rows
    }
    guardrail_rows = {
        row.guardrail_ref: row
        for row in external_branch_non_activation_guardrail.guardrail_rows
    }
    for request_row in external_branch_review_request.request_rows:
        if any(source_ref not in known_sources for source_ref in request_row.source_refs):
            raise ValueError("external branch request source refs must be known")
        roles = {source_roles[source_ref] for source_ref in request_row.source_refs}
        if request_row.branch_review_posture == "eligible_for_external_branch_review":
            if not roles.intersection(_V79_ELIGIBILITY_SOURCE_ROLES):
                raise ValueError("eligible external branch requests require released V79-C sources")
            if "v43_branch_posture_source" not in roles:
                raise ValueError("eligible external branch requests require current V43 posture")
            if "external_objective_source" in roles and len(roles) == 1:
                raise ValueError("external objective source alone cannot create eligibility")
        if (
            request_row.branch_review_posture == "request_recorded_objective_only"
            and "v43_branch_posture_source" in roles
        ):
            raise ValueError("objective-only request rows must not cite current branch posture")
        if request_row.v79_summary_refs and "v79_controlled_execution_summary_source" not in roles:
            raise ValueError("V79-C summary refs require a controlled-execution summary source")
        if (
            request_row.v79_handoff_refs
            and "v79_post_controlled_execution_review_handoff_source" not in roles
        ):
            raise ValueError("V79-C handoff refs require a post-review handoff source")
        if any(guardrail_ref not in guardrail_rows for guardrail_ref in request_row.guardrail_refs):
            raise ValueError("external branch request guardrail refs must be known")
        for guardrail_ref in request_row.guardrail_refs:
            guardrail_row = guardrail_rows[guardrail_ref]
            if guardrail_row.candidate_ref != request_row.candidate_ref:
                raise ValueError("external branch guardrails must match candidate")
            if (
                request_row.external_branch_review_request_ref
                not in guardrail_row.external_branch_review_request_refs
            ):
                raise ValueError("external branch guardrails must reference request rows")
    for guardrail_row in external_branch_non_activation_guardrail.guardrail_rows:
        if any(source_ref not in known_sources for source_ref in guardrail_row.source_refs):
            raise ValueError("external branch guardrail source refs must be known")
        if any(
            ref not in request_rows
            for ref in guardrail_row.external_branch_review_request_refs
        ):
            raise ValueError("guardrail external branch request refs must be known")
        for ref in guardrail_row.external_branch_review_request_refs:
            if request_rows[ref].candidate_ref != guardrail_row.candidate_ref:
                raise ValueError("guardrail request refs must match candidate")


def derive_v80a_external_branch_review_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoExternalBranchSourceIndex,
    RepoExternalBranchReviewRequest,
    RepoExternalBranchNonActivationGuardrail,
]:
    source_index = derive_v80a_repo_external_branch_source_index(repo_root=repo_root)
    request = derive_v80a_repo_external_branch_review_request(
        repo_root=repo_root,
        external_branch_source_index=source_index,
    )
    guardrail = derive_v80a_repo_external_branch_non_activation_guardrail(
        repo_root=repo_root,
        external_branch_review_request=request,
    )
    validate_v80a_external_branch_review_bundle(
        external_branch_source_index=source_index,
        external_branch_review_request=request,
        external_branch_non_activation_guardrail=guardrail,
    )
    return source_index, request, guardrail
