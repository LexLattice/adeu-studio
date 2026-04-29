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
from .candidate_outcome_review import (
    RepoOperatorCognitionOutcomeSignal,
    RepoOutcomePromotionDemotionRecommendation,
    RepoOutcomeReviewFamilyCloseoutAlignment,
    RepoSelfImprovementOutcomeLedger,
)
from .candidate_review_classification import _load_json, _surface_id
from .recursive_candidate_intake import (
    CandidateAuthorityLayer,
    CandidateSourceKind,
    CandidateSourcePresencePosture,
    OdeuLane,
)

REPO_OPERATOR_PROJECTION_CASE_VIEW_SCHEMA = "repo_operator_projection_case_view@1"
REPO_OPERATOR_PROJECTION_SOURCE_INDEX_SCHEMA = "repo_operator_projection_source_index@1"
REPO_OPERATOR_PROJECTION_NON_AUTHORITY_GUARDRAIL_SCHEMA = (
    "repo_operator_projection_non_authority_guardrail@1"
)
REPO_TYPED_ADJUDICATION_CASE_VIEW_SCHEMA = "repo_typed_adjudication_case_view@1"
REPO_MODEL_OUTPUT_COMPARISON_PROJECTION_SCHEMA = "repo_model_output_comparison_projection@1"
REPO_PROJECTION_EXCEPTION_VISIBILITY_REGISTER_SCHEMA = (
    "repo_projection_exception_visibility_register@1"
)
REPO_DECISION_VISIBILITY_CONTRACT_SCHEMA = "repo_decision_visibility_contract@1"
REPO_RATIFICATION_REVIEW_WORKBENCH_PROJECTION_SCHEMA = (
    "repo_ratification_review_workbench_projection@1"
)
REPO_POST_PROJECTION_HANDOFF_SCHEMA = "repo_post_projection_handoff@1"
REPO_OPERATOR_PROJECTION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA = (
    "repo_operator_projection_family_closeout_alignment@1"
)

ProjectionCaseKind = Literal[
    "self_improvement_outcome_case",
    "candidate_decision_case",
    "operator_cognition_signal_case",
    "typed_adjudication_case",
    "model_output_comparison_case",
    "product_pressure_case",
    "future_family_case",
]
ProjectionPosture = Literal[
    "eligible_for_operator_projection",
    "blocked_by_missing_source",
    "blocked_by_unresolved_regression",
    "blocked_by_unresolved_dissent",
    "blocked_by_authority_boundary",
    "future_family_only",
    "rejected_out_of_scope",
]
VisibleDecisionState = Literal[
    "ready_for_human_review",
    "blocked_pending_evidence",
    "blocked_pending_authority",
    "blocked_pending_dissent_resolution",
    "recommended_for_later_review",
    "recommended_more_evidence",
    "deferred_to_future_family",
    "rejected_out_of_scope",
]
ProjectionHorizon = Literal[
    "human_review_visibility",
    "later_ratification_review_request",
    "later_product_review_request",
    "later_dispatch_review_request",
    "future_family_visibility_only",
]
VisibleAuthorityState = Literal[
    "no_authority_granted",
    "ratification_required",
    "product_authority_missing",
    "runtime_authority_missing",
    "dispatch_authority_missing",
    "release_authority_missing",
]
ProjectionSourceRole = Literal[
    "primary_projection_source",
    "outcome_ledger_source",
    "operator_signal_source",
    "recommendation_source",
    "family_closeout_source",
    "dogfood_source",
    "review_source",
    "ratification_source",
    "integration_source",
    "conceptual_diff_source",
    "product_wedge_source",
    "prompt_source",
    "model_output_source",
    "adjudicator_schema_source",
    "absence_marker",
]
VisibleBlockerKind = Literal[
    "source_gap",
    "unresolved_regression",
    "unresolved_dissent",
    "authority_boundary_gap",
    "product_authority_gap",
    "runtime_authority_gap",
    "dispatch_authority_gap",
    "release_authority_gap",
    "model_output_provenance_gap",
    "comparison_axis_gap",
]
VisibleBlockerPosture = Literal[
    "blocking",
    "warning_only",
    "carried_forward",
    "not_applicable",
    "unknown_needs_review",
]
ProjectionRequiredNextSurface = Literal[
    "v74b_exception_visibility",
    "v74c_visibility_contract",
    "v75_dispatch_review",
    "future_product_review",
    "future_ratification_or_policy_review",
    "future_family_review",
    "deferred_no_selection",
]
ForbiddenProjectionAuthority = Literal[
    "ratification_authority",
    "adoption_authority",
    "implementation_authority",
    "commit_release_authority",
    "merge_authority",
    "released_truth",
    "product_authorization",
    "runtime_permission",
    "dispatch_authority",
    "external_contest_authority",
]
OperatorActionPosture = Literal[
    "inspect_only",
    "acknowledge_only",
    "request_later_review_only",
    "annotate_source_gap_only",
    "export_support_report_only",
    "no_operator_action_selected",
]
ProjectionRequiredLaterAuthority = Literal[
    "human_ratification_required",
    "maintainer_release_authority_required",
    "product_authority_required",
    "runtime_authority_required",
    "dispatch_authority_required",
    "external_contest_authority_required",
    "none_selected_here",
]
VisibilityObligationKind = Literal[
    "no_hidden_source_status",
    "no_hidden_authority_boundary",
    "no_hidden_regression",
    "no_hidden_dissent",
    "no_hidden_product_authority_gap",
    "no_hidden_runtime_or_dispatch_gap",
]
NonDerivableAuthorityKind = Literal[
    "release_truth",
    "product_selection",
    "runtime_permission",
    "dispatch_authority",
]
DecisionVisibilityContractPosture = Literal[
    "visibility_contract_ready",
    "blocked_by_missing_case_view",
    "blocked_by_hidden_required_exception",
    "blocked_by_authority_boundary",
    "future_family_only",
    "rejected_out_of_scope",
]
RequiredBeforeAction = Literal[
    "before_ratification_review",
    "before_product_review",
    "before_runtime_review",
    "before_dispatch_review",
    "before_release_review",
    "before_external_contest_review",
    "not_selected_here",
]
ForbiddenOperatorActionPosture = Literal[
    "ratify_now",
    "adopt_now",
    "implement_now",
    "commit_now",
    "merge_now",
    "release_now",
    "authorize_product_now",
    "grant_runtime_permission_now",
    "dispatch_now",
    "enter_external_contest_now",
]
WorkbenchProjectionPosture = Literal[
    "projection_ready_for_operator_review",
    "blocked_by_missing_visibility_contract",
    "blocked_by_unresolved_exception",
    "blocked_by_authority_boundary",
    "future_family_only",
    "rejected_out_of_scope",
]
PostProjectionHandoffTarget = Literal[
    "v75_dispatch_review",
    "future_product_review",
    "future_ratification_or_policy_review",
    "future_family_review",
    "deferred_no_selection",
]
PostProjectionHandoffPosture = Literal[
    "ready_for_later_review",
    "blocked_by_unresolved_exception",
    "blocked_by_authority_boundary",
    "deferred_to_future_family",
    "rejected_out_of_scope",
]
TypedAdjudicationCasePosture = Literal[
    "projection_ready",
    "blocked_by_missing_conceptual_diff_source",
    "blocked_by_missing_review_source",
    "blocked_by_unresolved_exception",
    "future_family_only",
    "rejected_out_of_scope",
]
ComparisonAxisKind = Literal[
    "source_binding",
    "authority_boundary_preservation",
    "odeu_lane_separation",
    "evidence_classification_fit",
    "ratification_boundary_fit",
    "implementation_safety",
    "utility_next_slice_fit",
    "conceptual_completeness",
    "operator_legibility",
]
ObservedDifferencePosture = Literal[
    "variant_a_stronger_on_axis",
    "variant_b_stronger_on_axis",
    "variants_complementary_on_axis",
    "variants_conflict_on_axis",
    "no_material_difference_observed",
    "axis_unchecked",
    "axis_blocked_by_missing_source",
]
ComparisonConfidencePosture = Literal[
    "high_with_bounded_evidence",
    "moderate_with_limitations",
    "low_or_inconclusive",
    "blocked_by_missing_source",
    "not_applicable",
]
ComparisonProjectionPosture = Literal[
    "projection_ready",
    "blocked_by_missing_prompt_source",
    "blocked_by_missing_model_output_source",
    "blocked_by_missing_adjudicator_schema",
    "blocked_by_unresolved_conflict",
    "future_family_only",
    "rejected_out_of_scope",
]
ProjectionExceptionKind = Literal[
    "source_missing",
    "source_stale",
    "authority_boundary_blocker",
    "unresolved_dissent",
    "unresolved_regression",
    "review_conflict",
    "evidence_gap",
    "product_authority_missing",
    "runtime_authority_missing",
    "dispatch_authority_missing",
    "comparison_axis_unchecked",
    "model_output_provenance_gap",
]

_V73C_LEDGER_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus205/"
    "repo_self_improvement_outcome_ledger_v205_reference.json"
)
_V73C_OPERATOR_SIGNAL_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus205/"
    "repo_operator_cognition_outcome_signal_v205_reference.json"
)
_V73C_RECOMMENDATION_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus205/"
    "repo_outcome_promotion_demotion_recommendation_v205_reference.json"
)
_V73C_FAMILY_CLOSEOUT_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus205/"
    "repo_outcome_review_family_closeout_alignment_v205_reference.json"
)
_V73C_CLOSEOUT_EVIDENCE = (
    "artifacts/agent_harness/v205/evidence_inputs/"
    "v73c_candidate_outcome_closeout_evidence_v205.json"
)
_V73_FAMILY_CLOSEOUT_ALIGNMENT = (
    "artifacts/agent_harness/v205/evidence_inputs/v73_family_closeout_alignment_v205.json"
)
_V68_V73_DOGFOOD = (
    "docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_COMBINED_DOGFOOD_TEST_v0.json"
)
_PRODUCT_WEDGE_SUPPORT = (
    "docs/support/arc_series_mapping/DRAFT_ADEU_TYPED_ADJUDICATION_PRODUCT_WEDGE_v0.md"
)
_CONCEPTUAL_DIFF_SUPPORT = (
    "docs/support/arc_series_mapping/DRAFT_ARC_SERIES_ODEU_CONCEPTUAL_DIFF_v0.report.json"
)
_CONCEPTUAL_DIFF_SCHEMA_SUPPORT = (
    "docs/support/arc_series_mapping/odeu_conceptual_diff_report.schema.json"
)
_V74A_CLOSEOUT_EVIDENCE = (
    "artifacts/agent_harness/v206/evidence_inputs/v74a_operator_projection_evidence_v206.json"
)
_V74B_CLOSEOUT_EVIDENCE = (
    "artifacts/agent_harness/v207/evidence_inputs/v74b_operator_projection_evidence_v207.json"
)
_V74A_LOCK = "docs/LOCKED_CONTINUATION_vNEXT_PLUS206.md"
_V74B_LOCK = "docs/LOCKED_CONTINUATION_vNEXT_PLUS207.md"
_V74C_LOCK = "docs/LOCKED_CONTINUATION_vNEXT_PLUS208.md"

_REQUIRED_FORBIDDEN_PROJECTION_AUTHORITIES = {
    "ratification_authority",
    "adoption_authority",
    "implementation_authority",
    "commit_release_authority",
    "merge_authority",
    "released_truth",
    "product_authorization",
    "runtime_permission",
    "dispatch_authority",
    "external_contest_authority",
}
_BLOCKED_POSTURES = {
    "blocked_by_missing_source",
    "blocked_by_unresolved_regression",
    "blocked_by_unresolved_dissent",
    "blocked_by_authority_boundary",
}
_FORBIDDEN_AUTHORITY_PHRASES = (
    "product authorized",
    "product-authorized",
    "product authorization granted",
    "benchmark truth",
    "model selected",
    "model-selected",
    "global model ranking",
    "dispatch authorized",
    "release authorized",
    "runtime permission granted",
    "self-approved",
    "self approval",
)
_FORBIDDEN_V74B_AUTHORITY_PHRASES = _FORBIDDEN_AUTHORITY_PHRASES + (
    "released schema",
    "schema released",
    "ratified decision",
    "new ratification",
    "outcome verdict",
    "exception resolved",
    "resolved exception",
)
_FORBIDDEN_V74C_AUTHORITY_PHRASES = _FORBIDDEN_V74B_AUTHORITY_PHRASES + (
    "ratify now",
    "adopt now",
    "implement now",
    "commit now",
    "merge now",
    "release now",
    "authorize product now",
    "grant runtime permission now",
    "dispatch now",
    "enter external contest now",
    "product selected",
    "product-selected",
    "dispatch performed",
    "dispatch ready",
)
_REQUIRED_VISIBILITY_OBLIGATIONS = {
    "no_hidden_source_status",
    "no_hidden_authority_boundary",
    "no_hidden_regression",
    "no_hidden_dissent",
    "no_hidden_product_authority_gap",
    "no_hidden_runtime_or_dispatch_gap",
}
_REQUIRED_NON_DERIVABLE_AUTHORITIES = {
    "release_truth",
    "product_selection",
    "runtime_permission",
    "dispatch_authority",
}
_REQUIRED_FORBIDDEN_OPERATOR_ACTIONS = {
    "ratify_now",
    "adopt_now",
    "implement_now",
    "commit_now",
    "merge_now",
    "release_now",
    "authorize_product_now",
    "grant_runtime_permission_now",
    "dispatch_now",
    "enter_external_contest_now",
}
_REQUIRED_BEFORE_ACTION_BY_AUTHORITY_KIND: dict[
    ProjectionRequiredLaterAuthority, RequiredBeforeAction
] = {
    "human_ratification_required": "before_ratification_review",
    "maintainer_release_authority_required": "before_release_review",
    "product_authority_required": "before_product_review",
    "runtime_authority_required": "before_runtime_review",
    "dispatch_authority_required": "before_dispatch_review",
    "external_contest_authority_required": "before_external_contest_review",
}


def _has_unnegated_phrase(value: str, phrase: str) -> bool:
    phrase_pattern = r"\b" + r"\s+".join(re.escape(part) for part in phrase.split()) + r"\b"
    negated_pattern = re.compile(
        r"(?:\bno\b|\bnot\b|\bwithout\b)\s+" + phrase_pattern,
        flags=re.IGNORECASE,
    )
    for match in re.finditer(phrase_pattern, value, flags=re.IGNORECASE):
        if not any(
            negated.start() <= match.start() and match.end() <= negated.end()
            for negated in negated_pattern.finditer(value)
        ):
            return True
    return False


def _v74a_note(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    for phrase in _FORBIDDEN_AUTHORITY_PHRASES:
        if _has_unnegated_phrase(normalized, phrase):
            raise ValueError(f"{field_name} may not carry projection authority")
    if _has_unnegated_phrase(normalized, "case view is source truth"):
        raise ValueError(f"{field_name} may not treat case view as source truth")
    return normalized


def _v74a_required_summary(value: str, *, field_name: str, required: tuple[str, ...]) -> str:
    normalized = _v74a_note(value, field_name=field_name)
    lowered = normalized.lower()
    missing = [phrase for phrase in required if phrase not in lowered]
    if missing:
        raise ValueError(f"{field_name} must state {', '.join(missing)}")
    return normalized


class RepoOperatorProjectionSourceRow(_CartographyBase):
    source_ref: str
    source_kind: CandidateSourceKind
    authority_layer: CandidateAuthorityLayer
    source_status: SourceStatus
    source_presence_posture: CandidateSourcePresencePosture
    projection_source_role: ProjectionSourceRole
    limitation_note: str

    @model_validator(mode="after")
    def _validate_projection_source(self) -> RepoOperatorProjectionSourceRow:
        object.__setattr__(self, "source_ref", _repo_ref(self.source_ref, field_name="source_ref"))
        object.__setattr__(
            self, "limitation_note", _v74a_note(self.limitation_note, field_name="limitation_note")
        )
        if (
            self.source_status == "integrated_shaping_source"
            and self.source_presence_posture != "present"
        ):
            raise ValueError("integrated projection source rows must be present")
        if (
            self.source_presence_posture != "present"
            and self.projection_source_role != "absence_marker"
        ):
            raise ValueError("missing projection sources must use absence_marker role")
        if self.source_kind in {"support_doc", "review_input"} and self.authority_layer == "lock":
            raise ValueError("support and review sources cannot be lock authority")
        return self


class RepoOperatorProjectionSourceIndex(_CartographyBase):
    schema: Literal["repo_operator_projection_source_index@1"] = (
        REPO_OPERATOR_PROJECTION_SOURCE_INDEX_SCHEMA
    )
    operator_projection_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    source_rows: list[RepoOperatorProjectionSourceRow] = Field(min_length=1)
    projection_source_summary: str

    @model_validator(mode="after")
    def _validate_source_index(self) -> RepoOperatorProjectionSourceIndex:
        for field_name in (
            "operator_projection_source_index_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
        ):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        object.__setattr__(
            self,
            "source_rows",
            _sorted_unique_by_ref(self.source_rows, attr="source_ref", field_name="source_rows"),
        )
        object.__setattr__(
            self,
            "projection_source_summary",
            _v74a_required_summary(
                self.projection_source_summary,
                field_name="projection_source_summary",
                required=(
                    "source rows",
                    "absence",
                    "no prose memory",
                    "no authority",
                ),
            ),
        )
        expected_id = _surface_id(
            "repo_operator_projection_source_index",
            REPO_OPERATOR_PROJECTION_SOURCE_INDEX_SCHEMA,
            self.model_dump(mode="json"),
            "operator_projection_source_index_id",
        )
        if self.operator_projection_source_index_id != expected_id:
            raise ValueError(
                "operator_projection_source_index_id must match canonical full payload "
                "hash identity"
            )
        return self


class RepoProjectionVisibleBlockerRow(_CartographyBase):
    blocker_ref: str
    candidate_ref: str
    case_view_refs: list[str] = Field(min_length=1)
    blocker_kind: VisibleBlockerKind
    source_refs: list[str] = Field(min_length=1)
    blocking_posture: VisibleBlockerPosture
    visible_decision_state: VisibleDecisionState
    required_next_surface: ProjectionRequiredNextSurface
    limitation_note: str

    @model_validator(mode="after")
    def _validate_visible_blocker(self) -> RepoProjectionVisibleBlockerRow:
        object.__setattr__(
            self, "blocker_ref", _non_empty(self.blocker_ref, field_name="blocker_ref")
        )
        object.__setattr__(
            self, "candidate_ref", _non_empty(self.candidate_ref, field_name="candidate_ref")
        )
        for field_name in ("case_view_refs", "source_refs"):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self, "limitation_note", _v74a_note(self.limitation_note, field_name="limitation_note")
        )
        if self.blocking_posture == "blocking" and self.visible_decision_state not in {
            "blocked_pending_evidence",
            "blocked_pending_authority",
            "blocked_pending_dissent_resolution",
            "deferred_to_future_family",
        }:
            raise ValueError("blocking visible blockers must use a blocked visible state")
        if (
            self.blocker_kind == "product_authority_gap"
            and self.required_next_surface != "future_product_review"
        ):
            raise ValueError("product authority blockers require future_product_review")
        return self


class RepoOperatorProjectionCaseViewRow(_CartographyBase):
    case_view_ref: str
    candidate_ref: str
    projection_case_kind: ProjectionCaseKind
    projection_posture: ProjectionPosture
    visible_decision_state: VisibleDecisionState
    projection_horizon: ProjectionHorizon
    visible_authority_state: VisibleAuthorityState
    source_refs: list[str] = Field(min_length=1)
    ledger_refs: list[str] = Field(default_factory=list)
    operator_signal_refs: list[str] = Field(default_factory=list)
    recommendation_refs: list[str] = Field(default_factory=list)
    family_closeout_refs: list[str] = Field(default_factory=list)
    exception_refs: list[str] = Field(default_factory=list)
    visible_blocker_rows: list[RepoProjectionVisibleBlockerRow] = Field(default_factory=list)
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_case_view_row(self) -> RepoOperatorProjectionCaseViewRow:
        object.__setattr__(
            self, "case_view_ref", _non_empty(self.case_view_ref, field_name="case_view_ref")
        )
        object.__setattr__(
            self, "candidate_ref", _non_empty(self.candidate_ref, field_name="candidate_ref")
        )
        for field_name in (
            "source_refs",
            "ledger_refs",
            "operator_signal_refs",
            "recommendation_refs",
            "family_closeout_refs",
            "exception_refs",
            "odeu_lanes",
            "guardrail_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "visible_blocker_rows",
            _sorted_unique_by_ref(
                self.visible_blocker_rows,
                attr="blocker_ref",
                field_name="visible_blocker_rows",
            ),
        )
        object.__setattr__(
            self, "limitation_note", _v74a_note(self.limitation_note, field_name="limitation_note")
        )
        if self.projection_posture == "eligible_for_operator_projection" and not (
            self.ledger_refs or self.operator_signal_refs or self.recommendation_refs
        ):
            raise ValueError("eligible operator projection cases require released V73-C refs")
        if self.projection_posture in _BLOCKED_POSTURES and not self.visible_blocker_rows:
            raise ValueError("blocked projection cases require visible blocker rows")
        if self.exception_refs and set(self.exception_refs) - {
            row.blocker_ref for row in self.visible_blocker_rows
        }:
            raise ValueError("exception_refs must be represented by visible blocker rows")
        for blocker in self.visible_blocker_rows:
            if self.case_view_ref not in blocker.case_view_refs:
                raise ValueError("visible blocker rows must reference their case view")
            if blocker.candidate_ref != self.candidate_ref:
                raise ValueError("visible blocker candidate_ref must match case view candidate_ref")
        if self.visible_decision_state == "ready_for_human_review" and (
            self.visible_authority_state == "no_authority_granted"
            or self.projection_horizon != "human_review_visibility"
        ):
            raise ValueError(
                "ready_for_human_review requires explicit later authority and review horizon"
            )
        if self.projection_case_kind == "product_pressure_case":
            if self.projection_posture != "rejected_out_of_scope" and (
                self.visible_authority_state != "product_authority_missing"
            ):
                raise ValueError("product-pressure cases require missing product authority")
            if self.projection_posture == "future_family_only" and not self.visible_blocker_rows:
                raise ValueError("future-family product-pressure cases require visible blockers")
        if self.projection_case_kind == "model_output_comparison_case" and (
            self.visible_decision_state == "ready_for_human_review"
        ):
            raise ValueError("model-output comparison cases cannot imply model selection")
        return self


class RepoOperatorProjectionCaseView(_CartographyBase):
    schema: Literal["repo_operator_projection_case_view@1"] = (
        REPO_OPERATOR_PROJECTION_CASE_VIEW_SCHEMA
    )
    operator_projection_case_view_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    operator_projection_source_index_id: str
    case_view_rows: list[RepoOperatorProjectionCaseViewRow] = Field(min_length=1)
    projection_boundary_summary: str

    @model_validator(mode="after")
    def _validate_case_view(self) -> RepoOperatorProjectionCaseView:
        for field_name in (
            "operator_projection_case_view_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "operator_projection_source_index_id",
        ):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        object.__setattr__(
            self,
            "case_view_rows",
            _sorted_unique_by_ref(
                self.case_view_rows, attr="case_view_ref", field_name="case_view_rows"
            ),
        )
        object.__setattr__(
            self,
            "projection_boundary_summary",
            _v74a_required_summary(
                self.projection_boundary_summary,
                field_name="projection_boundary_summary",
                required=(
                    "visibility",
                    "no ratification",
                    "no product",
                    "no release",
                    "no runtime",
                    "no dispatch",
                ),
            ),
        )
        expected_id = _surface_id(
            "repo_operator_projection_case_view",
            REPO_OPERATOR_PROJECTION_CASE_VIEW_SCHEMA,
            self.model_dump(mode="json"),
            "operator_projection_case_view_id",
        )
        if self.operator_projection_case_view_id != expected_id:
            raise ValueError(
                "operator_projection_case_view_id must match canonical full payload hash identity"
            )
        return self


class RepoOperatorProjectionNonAuthorityGuardrailRow(_CartographyBase):
    guardrail_ref: str
    case_view_refs: list[str] = Field(min_length=1)
    candidate_refs: list[str] = Field(min_length=1)
    forbidden_projection_authorities: list[ForbiddenProjectionAuthority] = Field(min_length=1)
    required_later_authority: ProjectionRequiredLaterAuthority
    operator_action_posture: OperatorActionPosture
    non_authority_statement: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_guardrail_row(self) -> RepoOperatorProjectionNonAuthorityGuardrailRow:
        object.__setattr__(
            self, "guardrail_ref", _non_empty(self.guardrail_ref, field_name="guardrail_ref")
        )
        for field_name in (
            "case_view_refs",
            "candidate_refs",
            "forbidden_projection_authorities",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "non_authority_statement",
            _v74a_required_summary(
                self.non_authority_statement,
                field_name="non_authority_statement",
                required=(
                    "projection only",
                    "no ratification",
                    "no adoption",
                    "no product",
                    "no release",
                    "no runtime",
                    "no dispatch",
                    "no external contest",
                ),
            ),
        )
        object.__setattr__(
            self, "limitation_note", _v74a_note(self.limitation_note, field_name="limitation_note")
        )
        missing = sorted(
            _REQUIRED_FORBIDDEN_PROJECTION_AUTHORITIES - set(self.forbidden_projection_authorities)
        )
        if missing:
            raise ValueError(f"guardrails must forbid projection authorities: {missing}")
        if (
            self.required_later_authority == "none_selected_here"
            and self.operator_action_posture == "request_later_review_only"
        ):
            raise ValueError("later review requests require later authority posture")
        return self


class RepoOperatorProjectionNonAuthorityGuardrail(_CartographyBase):
    schema: Literal["repo_operator_projection_non_authority_guardrail@1"] = (
        REPO_OPERATOR_PROJECTION_NON_AUTHORITY_GUARDRAIL_SCHEMA
    )
    operator_projection_non_authority_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    operator_projection_case_view_id: str
    guardrail_rows: list[RepoOperatorProjectionNonAuthorityGuardrailRow] = Field(min_length=1)
    non_authority_summary: str

    @model_validator(mode="after")
    def _validate_guardrail(self) -> RepoOperatorProjectionNonAuthorityGuardrail:
        for field_name in (
            "operator_projection_non_authority_guardrail_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "operator_projection_case_view_id",
        ):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        object.__setattr__(
            self,
            "guardrail_rows",
            _sorted_unique_by_ref(
                self.guardrail_rows, attr="guardrail_ref", field_name="guardrail_rows"
            ),
        )
        object.__setattr__(
            self,
            "non_authority_summary",
            _v74a_required_summary(
                self.non_authority_summary,
                field_name="non_authority_summary",
                required=(
                    "case view",
                    "projection only",
                    "no ratification",
                    "no adoption",
                    "no product",
                    "no release",
                    "no runtime",
                    "no dispatch",
                    "no external contest",
                ),
            ),
        )
        expected_id = _surface_id(
            "repo_operator_projection_non_authority_guardrail",
            REPO_OPERATOR_PROJECTION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            self.model_dump(mode="json"),
            "operator_projection_non_authority_guardrail_id",
        )
        if self.operator_projection_non_authority_guardrail_id != expected_id:
            raise ValueError(
                "operator_projection_non_authority_guardrail_id must match canonical full "
                "payload hash identity"
            )
        return self


def _v74b_note(value: str, *, field_name: str) -> str:
    normalized = _v74a_note(value, field_name=field_name)
    for phrase in _FORBIDDEN_V74B_AUTHORITY_PHRASES:
        if _has_unnegated_phrase(normalized, phrase):
            raise ValueError(f"{field_name} may not carry typed projection authority")
    return normalized


def _v74b_required_summary(value: str, *, field_name: str, required: tuple[str, ...]) -> str:
    normalized = _v74b_note(value, field_name=field_name)
    lowered = normalized.lower()
    missing = [phrase for phrase in required if phrase not in lowered]
    if missing:
        raise ValueError(f"{field_name} must state {', '.join(missing)}")
    return normalized


def _v74c_note(value: str, *, field_name: str) -> str:
    normalized = _v74b_note(value, field_name=field_name)
    for phrase in _FORBIDDEN_V74C_AUTHORITY_PHRASES:
        if _has_unnegated_phrase(normalized, phrase):
            raise ValueError(f"{field_name} may not carry workbench or handoff authority")
    return normalized


def _v74c_required_summary(value: str, *, field_name: str, required: tuple[str, ...]) -> str:
    normalized = _v74c_note(value, field_name=field_name)
    lowered = normalized.lower()
    missing = [phrase for phrase in required if phrase not in lowered]
    if missing:
        raise ValueError(f"{field_name} must state {', '.join(missing)}")
    return normalized


class RepoTypedAdjudicationCaseViewRow(_CartographyBase):
    typed_case_ref: str
    source_case_view_refs: list[str] = Field(min_length=1)
    candidate_refs: list[str] = Field(min_length=1)
    conceptual_diff_refs: list[str] = Field(default_factory=list)
    review_classification_refs: list[str] = Field(default_factory=list)
    ratification_refs: list[str] = Field(default_factory=list)
    outcome_recommendation_refs: list[str] = Field(default_factory=list)
    comparison_projection_refs: list[str] = Field(default_factory=list)
    exception_refs: list[str] = Field(default_factory=list)
    typed_case_posture: TypedAdjudicationCasePosture
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_typed_case_row(self) -> RepoTypedAdjudicationCaseViewRow:
        object.__setattr__(
            self, "typed_case_ref", _non_empty(self.typed_case_ref, field_name="typed_case_ref")
        )
        for field_name in (
            "source_case_view_refs",
            "candidate_refs",
            "conceptual_diff_refs",
            "review_classification_refs",
            "ratification_refs",
            "outcome_recommendation_refs",
            "comparison_projection_refs",
            "exception_refs",
            "odeu_lanes",
            "guardrail_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self, "limitation_note", _v74b_note(self.limitation_note, field_name="limitation_note")
        )
        if self.typed_case_posture == "projection_ready" and not self.conceptual_diff_refs:
            raise ValueError("projection-ready typed cases require conceptual_diff_refs")
        if self.typed_case_posture == "blocked_by_unresolved_exception" and not self.exception_refs:
            raise ValueError("exception-blocked typed cases require exception_refs")
        if any(
            "odeu_conceptual_diff_report.schema.json" in ref for ref in self.conceptual_diff_refs
        ):
            raise ValueError("conceptual-diff schema support cannot be treated as released schema")
        if self.typed_case_posture == "projection_ready" and self.exception_refs:
            raise ValueError("projection-ready typed cases cannot carry unresolved exceptions")
        return self


class RepoTypedAdjudicationCaseView(_CartographyBase):
    schema: Literal["repo_typed_adjudication_case_view@1"] = (
        REPO_TYPED_ADJUDICATION_CASE_VIEW_SCHEMA
    )
    typed_adjudication_case_view_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    operator_projection_case_view_id: str
    typed_case_rows: list[RepoTypedAdjudicationCaseViewRow] = Field(min_length=1)
    typed_case_boundary_summary: str

    @model_validator(mode="after")
    def _validate_typed_case_view(self) -> RepoTypedAdjudicationCaseView:
        for field_name in (
            "typed_adjudication_case_view_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "operator_projection_case_view_id",
        ):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        object.__setattr__(
            self,
            "typed_case_rows",
            _sorted_unique_by_ref(
                self.typed_case_rows, attr="typed_case_ref", field_name="typed_case_rows"
            ),
        )
        object.__setattr__(
            self,
            "typed_case_boundary_summary",
            _v74b_required_summary(
                self.typed_case_boundary_summary,
                field_name="typed_case_boundary_summary",
                required=(
                    "projection only",
                    "no ratification",
                    "no adoption",
                    "no product",
                    "no release",
                    "no runtime",
                    "no dispatch",
                ),
            ),
        )
        expected_id = _surface_id(
            "repo_typed_adjudication_case_view",
            REPO_TYPED_ADJUDICATION_CASE_VIEW_SCHEMA,
            self.model_dump(mode="json"),
            "typed_adjudication_case_view_id",
        )
        if self.typed_adjudication_case_view_id != expected_id:
            raise ValueError(
                "typed_adjudication_case_view_id must match canonical full payload hash identity"
            )
        return self


class RepoModelOutputSourceRow(_CartographyBase):
    model_output_ref: str
    prompt_source_ref: str
    model_identity_ref: str
    output_capture_ref: str
    run_context_ref: str
    source_presence_posture: CandidateSourcePresencePosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_model_output_source_row(self) -> RepoModelOutputSourceRow:
        for field_name in (
            "model_output_ref",
            "prompt_source_ref",
            "model_identity_ref",
            "output_capture_ref",
            "run_context_ref",
        ):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        object.__setattr__(
            self, "limitation_note", _v74b_note(self.limitation_note, field_name="limitation_note")
        )
        if self.source_presence_posture != "present":
            raise ValueError("model-output comparison provenance must be explicitly present")
        return self


class RepoComparisonAxisRow(_CartographyBase):
    axis_ref: str
    axis_kind: ComparisonAxisKind
    bounded_claim_horizon: str
    axis_source_refs: list[str] = Field(min_length=1)
    observed_difference_posture: ObservedDifferencePosture
    contradiction_refs: list[str] = Field(default_factory=list)
    complementarity_refs: list[str] = Field(default_factory=list)
    exception_refs: list[str] = Field(default_factory=list)
    confidence_posture: ComparisonConfidencePosture
    non_benchmark_guardrail: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_comparison_axis_row(self) -> RepoComparisonAxisRow:
        object.__setattr__(self, "axis_ref", _non_empty(self.axis_ref, field_name="axis_ref"))
        object.__setattr__(
            self,
            "bounded_claim_horizon",
            _v74b_note(self.bounded_claim_horizon, field_name="bounded_claim_horizon"),
        )
        for field_name in (
            "axis_source_refs",
            "contradiction_refs",
            "complementarity_refs",
            "exception_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "non_benchmark_guardrail",
            _v74b_required_summary(
                self.non_benchmark_guardrail,
                field_name="non_benchmark_guardrail",
                required=("bounded", "not benchmark truth", "no model selection"),
            ),
        )
        object.__setattr__(
            self, "limitation_note", _v74b_note(self.limitation_note, field_name="limitation_note")
        )
        if self.observed_difference_posture == "axis_blocked_by_missing_source" and (
            not self.exception_refs
        ):
            raise ValueError("source-blocked comparison axes require exception_refs")
        return self


class RepoModelOutputComparisonProjectionRow(_CartographyBase):
    comparison_projection_ref: str
    typed_case_ref: str
    prompt_source_refs: list[str] = Field(min_length=1)
    model_output_refs: list[str] = Field(min_length=1)
    model_output_source_rows: list[RepoModelOutputSourceRow] = Field(min_length=1)
    adjudicator_schema_refs: list[str] = Field(min_length=1)
    comparison_axis_rows: list[RepoComparisonAxisRow] = Field(min_length=1)
    contradiction_refs: list[str] = Field(default_factory=list)
    complementarity_refs: list[str] = Field(default_factory=list)
    exception_refs: list[str] = Field(default_factory=list)
    comparison_projection_posture: ComparisonProjectionPosture
    non_benchmark_guardrail: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_comparison_projection_row(self) -> RepoModelOutputComparisonProjectionRow:
        for field_name in ("comparison_projection_ref", "typed_case_ref"):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        for field_name in (
            "prompt_source_refs",
            "model_output_refs",
            "adjudicator_schema_refs",
            "contradiction_refs",
            "complementarity_refs",
            "exception_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "model_output_source_rows",
            _sorted_unique_by_ref(
                self.model_output_source_rows,
                attr="model_output_ref",
                field_name="model_output_source_rows",
            ),
        )
        object.__setattr__(
            self,
            "comparison_axis_rows",
            _sorted_unique_by_ref(
                self.comparison_axis_rows, attr="axis_ref", field_name="comparison_axis_rows"
            ),
        )
        object.__setattr__(
            self,
            "non_benchmark_guardrail",
            _v74b_required_summary(
                self.non_benchmark_guardrail,
                field_name="non_benchmark_guardrail",
                required=("bounded", "not benchmark truth", "no model selection"),
            ),
        )
        object.__setattr__(
            self, "limitation_note", _v74b_note(self.limitation_note, field_name="limitation_note")
        )
        model_output_source_refs = {row.model_output_ref for row in self.model_output_source_rows}
        missing_model_sources = sorted(set(self.model_output_refs) - model_output_source_refs)
        if missing_model_sources:
            raise ValueError(
                "comparison projections require model-output provenance rows: "
                f"{missing_model_sources}"
            )
        for row in self.model_output_source_rows:
            if row.prompt_source_ref not in self.prompt_source_refs:
                raise ValueError("model-output provenance rows must use known prompt_source_refs")
        if self.comparison_projection_posture == "projection_ready" and self.exception_refs:
            raise ValueError("projection-ready comparison rows cannot carry unresolved exceptions")
        if any(
            axis.observed_difference_posture == "axis_unchecked"
            for axis in self.comparison_axis_rows
        ):
            if self.comparison_projection_posture == "projection_ready":
                raise ValueError("projection-ready comparison rows cannot include unchecked axes")
        return self


class RepoModelOutputComparisonProjection(_CartographyBase):
    schema: Literal["repo_model_output_comparison_projection@1"] = (
        REPO_MODEL_OUTPUT_COMPARISON_PROJECTION_SCHEMA
    )
    model_output_comparison_projection_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    typed_adjudication_case_view_id: str
    comparison_projection_rows: list[RepoModelOutputComparisonProjectionRow] = Field(min_length=1)
    comparison_boundary_summary: str

    @model_validator(mode="after")
    def _validate_comparison_projection(self) -> RepoModelOutputComparisonProjection:
        for field_name in (
            "model_output_comparison_projection_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "typed_adjudication_case_view_id",
        ):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        object.__setattr__(
            self,
            "comparison_projection_rows",
            _sorted_unique_by_ref(
                self.comparison_projection_rows,
                attr="comparison_projection_ref",
                field_name="comparison_projection_rows",
            ),
        )
        object.__setattr__(
            self,
            "comparison_boundary_summary",
            _v74b_required_summary(
                self.comparison_boundary_summary,
                field_name="comparison_boundary_summary",
                required=("bounded", "not benchmark truth", "no model selection", "no dispatch"),
            ),
        )
        expected_id = _surface_id(
            "repo_model_output_comparison_projection",
            REPO_MODEL_OUTPUT_COMPARISON_PROJECTION_SCHEMA,
            self.model_dump(mode="json"),
            "model_output_comparison_projection_id",
        )
        if self.model_output_comparison_projection_id != expected_id:
            raise ValueError(
                "model_output_comparison_projection_id must match canonical full payload hash "
                "identity"
            )
        return self


class RepoProjectionExceptionVisibilityRow(_CartographyBase):
    exception_ref: str
    case_view_refs: list[str] = Field(default_factory=list)
    typed_case_refs: list[str] = Field(default_factory=list)
    comparison_projection_refs: list[str] = Field(default_factory=list)
    candidate_refs: list[str] = Field(min_length=1)
    exception_kind: ProjectionExceptionKind
    source_refs: list[str] = Field(min_length=1)
    visible_decision_state: VisibleDecisionState
    blocking_posture: VisibleBlockerPosture
    required_next_surface: ProjectionRequiredNextSurface
    limitation_note: str

    @model_validator(mode="after")
    def _validate_exception_visibility_row(self) -> RepoProjectionExceptionVisibilityRow:
        object.__setattr__(
            self, "exception_ref", _non_empty(self.exception_ref, field_name="exception_ref")
        )
        for field_name in (
            "case_view_refs",
            "typed_case_refs",
            "comparison_projection_refs",
            "candidate_refs",
            "source_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        if not (self.case_view_refs or self.typed_case_refs or self.comparison_projection_refs):
            raise ValueError("exception rows must reference a case, typed case, or comparison row")
        object.__setattr__(
            self, "limitation_note", _v74b_note(self.limitation_note, field_name="limitation_note")
        )
        if self.blocking_posture == "blocking" and self.visible_decision_state not in {
            "blocked_pending_evidence",
            "blocked_pending_authority",
            "blocked_pending_dissent_resolution",
            "deferred_to_future_family",
        }:
            raise ValueError("blocking exception rows must use a blocked visible state")
        if self.exception_kind == "product_authority_missing" and (
            self.required_next_surface != "future_product_review"
        ):
            raise ValueError("product authority exceptions require future_product_review")
        if _has_unnegated_phrase(self.limitation_note, "resolved"):
            raise ValueError("V74-B exception rows cannot mark exceptions resolved")
        return self


class RepoProjectionExceptionVisibilityRegister(_CartographyBase):
    schema: Literal["repo_projection_exception_visibility_register@1"] = (
        REPO_PROJECTION_EXCEPTION_VISIBILITY_REGISTER_SCHEMA
    )
    projection_exception_visibility_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    operator_projection_case_view_id: str
    typed_adjudication_case_view_id: str
    model_output_comparison_projection_id: str
    exception_rows: list[RepoProjectionExceptionVisibilityRow] = Field(min_length=1)
    exception_visibility_summary: str

    @model_validator(mode="after")
    def _validate_exception_visibility_register(self) -> RepoProjectionExceptionVisibilityRegister:
        for field_name in (
            "projection_exception_visibility_register_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "operator_projection_case_view_id",
            "typed_adjudication_case_view_id",
            "model_output_comparison_projection_id",
        ):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        object.__setattr__(
            self,
            "exception_rows",
            _sorted_unique_by_ref(
                self.exception_rows, attr="exception_ref", field_name="exception_rows"
            ),
        )
        object.__setattr__(
            self,
            "exception_visibility_summary",
            _v74b_required_summary(
                self.exception_visibility_summary,
                field_name="exception_visibility_summary",
                required=("visible", "not resolved", "no product", "no release", "no dispatch"),
            ),
        )
        expected_id = _surface_id(
            "repo_projection_exception_visibility_register",
            REPO_PROJECTION_EXCEPTION_VISIBILITY_REGISTER_SCHEMA,
            self.model_dump(mode="json"),
            "projection_exception_visibility_register_id",
        )
        if self.projection_exception_visibility_register_id != expected_id:
            raise ValueError(
                "projection_exception_visibility_register_id must match canonical full payload "
                "hash identity"
            )
        return self


class RepoProjectionLaterAuthorityRequirementRow(_CartographyBase):
    authority_requirement_ref: str
    authority_kind: ProjectionRequiredLaterAuthority
    authority_source_refs: list[str] = Field(min_length=1)
    source_presence_posture: CandidateSourcePresencePosture
    required_before_action: RequiredBeforeAction
    limitation_note: str

    @model_validator(mode="after")
    def _validate_later_authority_requirement(
        self,
    ) -> RepoProjectionLaterAuthorityRequirementRow:
        object.__setattr__(
            self,
            "authority_requirement_ref",
            _non_empty(self.authority_requirement_ref, field_name="authority_requirement_ref"),
        )
        object.__setattr__(
            self,
            "authority_source_refs",
            _sorted_unique(self.authority_source_refs, field_name="authority_source_refs"),
        )
        object.__setattr__(
            self, "limitation_note", _v74c_note(self.limitation_note, field_name="limitation_note")
        )
        if self.authority_kind == "none_selected_here":
            raise ValueError("later-authority requirement rows cannot use none_selected_here")
        if (
            self.source_presence_posture == "present"
            and not self.authority_source_refs
        ):
            raise ValueError("present authority requirements require source refs")
        expected_action = _REQUIRED_BEFORE_ACTION_BY_AUTHORITY_KIND.get(self.authority_kind)
        if expected_action is None:
            raise ValueError("later-authority requirement rows must use a known authority kind")
        if self.required_before_action != expected_action:
            raise ValueError(
                f"{self.authority_kind} must be required before {expected_action}"
            )
        return self


class RepoDecisionVisibilityContractRow(_CartographyBase):
    visibility_contract_ref: str
    case_view_refs: list[str] = Field(min_length=1)
    typed_case_refs: list[str] = Field(min_length=1)
    exception_refs: list[str] = Field(default_factory=list)
    visible_decision_state: VisibleDecisionState
    visible_source_refs: list[str] = Field(min_length=1)
    visible_exception_refs: list[str] = Field(default_factory=list)
    visibility_obligation_kinds: list[VisibilityObligationKind] = Field(min_length=1)
    non_derivable_authority_kinds: list[NonDerivableAuthorityKind] = Field(min_length=1)
    operator_action_postures: list[OperatorActionPosture] = Field(min_length=1)
    required_later_authority: list[ProjectionRequiredLaterAuthority] = Field(min_length=1)
    required_later_authority_rows: list[RepoProjectionLaterAuthorityRequirementRow] = Field(
        min_length=1
    )
    contract_posture: DecisionVisibilityContractPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_decision_visibility_contract_row(self) -> RepoDecisionVisibilityContractRow:
        object.__setattr__(
            self,
            "visibility_contract_ref",
            _non_empty(self.visibility_contract_ref, field_name="visibility_contract_ref"),
        )
        for field_name in (
            "case_view_refs",
            "typed_case_refs",
            "exception_refs",
            "visible_source_refs",
            "visible_exception_refs",
            "visibility_obligation_kinds",
            "non_derivable_authority_kinds",
            "operator_action_postures",
            "required_later_authority",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
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
        object.__setattr__(
            self, "limitation_note", _v74c_note(self.limitation_note, field_name="limitation_note")
        )
        missing_obligations = sorted(
            _REQUIRED_VISIBILITY_OBLIGATIONS - set(self.visibility_obligation_kinds)
        )
        if missing_obligations:
            raise ValueError(f"visibility obligations must remain visible: {missing_obligations}")
        missing_non_derivable = sorted(
            _REQUIRED_NON_DERIVABLE_AUTHORITIES - set(self.non_derivable_authority_kinds)
        )
        if missing_non_derivable:
            raise ValueError(
                f"non-derivable authority kinds must remain separate: {missing_non_derivable}"
            )
        if set(self.exception_refs) - set(self.visible_exception_refs):
            raise ValueError("contract exception_refs must remain visible_exception_refs")
        authority_kinds = {row.authority_kind for row in self.required_later_authority_rows}
        missing_authority_rows = sorted(set(self.required_later_authority) - authority_kinds)
        if missing_authority_rows:
            raise ValueError(
                f"required later authority must resolve through rows: {missing_authority_rows}"
            )
        extra_authority_rows = sorted(authority_kinds - set(self.required_later_authority))
        if extra_authority_rows:
            raise ValueError(
                f"required later authority rows must be listed: {extra_authority_rows}"
            )
        if self.visible_decision_state == "blocked_pending_authority" and not self.exception_refs:
            raise ValueError("authority-blocked visibility contracts require exception refs")
        if self.contract_posture == "visibility_contract_ready" and (
            self.visible_decision_state in {
                "blocked_pending_authority",
                "blocked_pending_evidence",
                "blocked_pending_dissent_resolution",
            }
        ):
            raise ValueError("ready visibility contracts cannot carry blocked decision states")
        return self


class RepoDecisionVisibilityContract(_CartographyBase):
    schema: Literal["repo_decision_visibility_contract@1"] = (
        REPO_DECISION_VISIBILITY_CONTRACT_SCHEMA
    )
    decision_visibility_contract_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    operator_projection_case_view_id: str
    typed_adjudication_case_view_id: str
    projection_exception_visibility_register_id: str
    visibility_contract_rows: list[RepoDecisionVisibilityContractRow] = Field(min_length=1)
    decision_visibility_summary: str

    @model_validator(mode="after")
    def _validate_decision_visibility_contract(self) -> RepoDecisionVisibilityContract:
        for field_name in (
            "decision_visibility_contract_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "operator_projection_case_view_id",
            "typed_adjudication_case_view_id",
            "projection_exception_visibility_register_id",
        ):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        object.__setattr__(
            self,
            "visibility_contract_rows",
            _sorted_unique_by_ref(
                self.visibility_contract_rows,
                attr="visibility_contract_ref",
                field_name="visibility_contract_rows",
            ),
        )
        object.__setattr__(
            self,
            "decision_visibility_summary",
            _v74c_required_summary(
                self.decision_visibility_summary,
                field_name="decision_visibility_summary",
                required=(
                    "visibility only",
                    "no ratification",
                    "no product",
                    "no release",
                    "no runtime",
                    "no dispatch",
                ),
            ),
        )
        expected_id = _surface_id(
            "repo_decision_visibility_contract",
            REPO_DECISION_VISIBILITY_CONTRACT_SCHEMA,
            self.model_dump(mode="json"),
            "decision_visibility_contract_id",
        )
        if self.decision_visibility_contract_id != expected_id:
            raise ValueError(
                "decision_visibility_contract_id must match canonical full payload hash identity"
            )
        return self


class RepoRatificationReviewWorkbenchProjectionRow(_CartographyBase):
    workbench_projection_ref: str
    visibility_contract_refs: list[str] = Field(min_length=1)
    case_view_refs: list[str] = Field(min_length=1)
    candidate_refs: list[str] = Field(min_length=1)
    ratification_refs: list[str] = Field(default_factory=list)
    recommendation_refs: list[str] = Field(default_factory=list)
    exception_refs: list[str] = Field(default_factory=list)
    permitted_operator_action_postures: list[OperatorActionPosture] = Field(min_length=1)
    forbidden_operator_action_postures: list[ForbiddenOperatorActionPosture] = Field(min_length=1)
    required_later_authority: list[ProjectionRequiredLaterAuthority] = Field(min_length=1)
    required_later_authority_rows: list[RepoProjectionLaterAuthorityRequirementRow] = Field(
        min_length=1
    )
    workbench_projection_posture: WorkbenchProjectionPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_workbench_projection_row(self) -> RepoRatificationReviewWorkbenchProjectionRow:
        object.__setattr__(
            self,
            "workbench_projection_ref",
            _non_empty(self.workbench_projection_ref, field_name="workbench_projection_ref"),
        )
        for field_name in (
            "visibility_contract_refs",
            "case_view_refs",
            "candidate_refs",
            "ratification_refs",
            "recommendation_refs",
            "exception_refs",
            "permitted_operator_action_postures",
            "forbidden_operator_action_postures",
            "required_later_authority",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
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
        object.__setattr__(
            self, "limitation_note", _v74c_note(self.limitation_note, field_name="limitation_note")
        )
        missing_forbidden = sorted(
            _REQUIRED_FORBIDDEN_OPERATOR_ACTIONS - set(self.forbidden_operator_action_postures)
        )
        if missing_forbidden:
            raise ValueError(
                f"workbench projection must forbid operator actions: {missing_forbidden}"
            )
        authority_kinds = {row.authority_kind for row in self.required_later_authority_rows}
        missing_authority_rows = sorted(set(self.required_later_authority) - authority_kinds)
        if missing_authority_rows:
            raise ValueError(
                f"workbench required authority must resolve through rows: {missing_authority_rows}"
            )
        extra_authority_rows = sorted(authority_kinds - set(self.required_later_authority))
        if extra_authority_rows:
            raise ValueError(
                f"workbench required authority rows must be listed: {extra_authority_rows}"
            )
        if (
            self.workbench_projection_posture == "projection_ready_for_operator_review"
            and "request_later_review_only" not in self.permitted_operator_action_postures
        ):
            raise ValueError("ready workbench projections must permit later-review requests only")
        if (
            self.workbench_projection_posture == "blocked_by_unresolved_exception"
            and not self.exception_refs
        ):
            raise ValueError("exception-blocked workbench projections require exception refs")
        return self


class RepoRatificationReviewWorkbenchProjection(_CartographyBase):
    schema: Literal["repo_ratification_review_workbench_projection@1"] = (
        REPO_RATIFICATION_REVIEW_WORKBENCH_PROJECTION_SCHEMA
    )
    ratification_review_workbench_projection_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    decision_visibility_contract_id: str
    workbench_projection_rows: list[RepoRatificationReviewWorkbenchProjectionRow] = Field(
        min_length=1
    )
    workbench_boundary_summary: str

    @model_validator(mode="after")
    def _validate_workbench_projection(self) -> RepoRatificationReviewWorkbenchProjection:
        for field_name in (
            "ratification_review_workbench_projection_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "decision_visibility_contract_id",
        ):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        object.__setattr__(
            self,
            "workbench_projection_rows",
            _sorted_unique_by_ref(
                self.workbench_projection_rows,
                attr="workbench_projection_ref",
                field_name="workbench_projection_rows",
            ),
        )
        object.__setattr__(
            self,
            "workbench_boundary_summary",
            _v74c_required_summary(
                self.workbench_boundary_summary,
                field_name="workbench_boundary_summary",
                required=(
                    "review visibility only",
                    "no ratification",
                    "no product",
                    "no release",
                    "no runtime",
                    "no dispatch",
                ),
            ),
        )
        expected_id = _surface_id(
            "repo_ratification_review_workbench_projection",
            REPO_RATIFICATION_REVIEW_WORKBENCH_PROJECTION_SCHEMA,
            self.model_dump(mode="json"),
            "ratification_review_workbench_projection_id",
        )
        if self.ratification_review_workbench_projection_id != expected_id:
            raise ValueError(
                "ratification_review_workbench_projection_id must match canonical full payload "
                "hash identity"
            )
        return self


class RepoPostProjectionHandoffRow(_CartographyBase):
    handoff_ref: str
    visibility_contract_refs: list[str] = Field(min_length=1)
    workbench_projection_refs: list[str] = Field(min_length=1)
    candidate_refs: list[str] = Field(min_length=1)
    handoff_target: PostProjectionHandoffTarget
    handoff_posture: PostProjectionHandoffPosture
    carried_exception_refs: list[str] = Field(default_factory=list)
    required_later_authority: list[ProjectionRequiredLaterAuthority] = Field(min_length=1)
    non_dispatch_guardrail: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_post_projection_handoff_row(self) -> RepoPostProjectionHandoffRow:
        object.__setattr__(
            self, "handoff_ref", _non_empty(self.handoff_ref, field_name="handoff_ref")
        )
        for field_name in (
            "visibility_contract_refs",
            "workbench_projection_refs",
            "candidate_refs",
            "carried_exception_refs",
            "required_later_authority",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "non_dispatch_guardrail",
            _v74c_required_summary(
                self.non_dispatch_guardrail,
                field_name="non_dispatch_guardrail",
                required=("request", "later review", "no dispatch"),
            ),
        )
        object.__setattr__(
            self, "limitation_note", _v74c_note(self.limitation_note, field_name="limitation_note")
        )
        if self.handoff_target == "v75_dispatch_review":
            if "dispatch_authority_required" not in self.required_later_authority:
                raise ValueError("V75 handoff rows require dispatch authority requirement")
            if not self.non_dispatch_guardrail:
                raise ValueError("V75 handoff rows require non-dispatch guardrail")
        if self.handoff_target == "future_product_review" and (
            "product_authority_required" not in self.required_later_authority
        ):
            raise ValueError("future product handoff rows require product authority")
        return self


class RepoPostProjectionHandoff(_CartographyBase):
    schema: Literal["repo_post_projection_handoff@1"] = REPO_POST_PROJECTION_HANDOFF_SCHEMA
    post_projection_handoff_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    decision_visibility_contract_id: str
    ratification_review_workbench_projection_id: str
    handoff_rows: list[RepoPostProjectionHandoffRow] = Field(min_length=1)
    handoff_boundary_summary: str

    @model_validator(mode="after")
    def _validate_post_projection_handoff(self) -> RepoPostProjectionHandoff:
        for field_name in (
            "post_projection_handoff_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "decision_visibility_contract_id",
            "ratification_review_workbench_projection_id",
        ):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        object.__setattr__(
            self,
            "handoff_rows",
            _sorted_unique_by_ref(self.handoff_rows, attr="handoff_ref", field_name="handoff_rows"),
        )
        object.__setattr__(
            self,
            "handoff_boundary_summary",
            _v74c_required_summary(
                self.handoff_boundary_summary,
                field_name="handoff_boundary_summary",
                required=("later review", "no dispatch", "no runtime", "no product", "no release"),
            ),
        )
        expected_id = _surface_id(
            "repo_post_projection_handoff",
            REPO_POST_PROJECTION_HANDOFF_SCHEMA,
            self.model_dump(mode="json"),
            "post_projection_handoff_id",
        )
        if self.post_projection_handoff_id != expected_id:
            raise ValueError(
                "post_projection_handoff_id must match canonical full payload hash identity"
            )
        return self


class RepoOperatorProjectionFamilyCloseoutAlignment(_CartographyBase):
    schema: Literal["repo_operator_projection_family_closeout_alignment@1"] = (
        REPO_OPERATOR_PROJECTION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
    )
    operator_projection_family_closeout_alignment_id: str
    family: Literal["V74"]
    closed_by_arc: Literal["vNext+208"]
    closed_slice_ladder: list[Literal["V74-A", "V74-B", "V74-C"]] = Field(min_length=3)
    shipped_record_shapes: list[str] = Field(min_length=1)
    consumed_source_families: list[str] = Field(min_length=1)
    future_family_authority: list[str] = Field(min_length=1)
    unselected_future_surfaces: list[str] = Field(min_length=1)
    operator_projection_authority_boundary: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_family_closeout_alignment(self) -> RepoOperatorProjectionFamilyCloseoutAlignment:
        object.__setattr__(
            self,
            "closed_slice_ladder",
            _sorted_unique(self.closed_slice_ladder, field_name="closed_slice_ladder"),
        )
        for field_name in (
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
        if set(self.closed_slice_ladder) != {"V74-A", "V74-B", "V74-C"}:
            raise ValueError("V74 family closeout must list V74-A, V74-B, and V74-C")
        missing_shapes = sorted(
            {
                REPO_OPERATOR_PROJECTION_CASE_VIEW_SCHEMA,
                REPO_OPERATOR_PROJECTION_SOURCE_INDEX_SCHEMA,
                REPO_OPERATOR_PROJECTION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
                REPO_TYPED_ADJUDICATION_CASE_VIEW_SCHEMA,
                REPO_MODEL_OUTPUT_COMPARISON_PROJECTION_SCHEMA,
                REPO_PROJECTION_EXCEPTION_VISIBILITY_REGISTER_SCHEMA,
                REPO_DECISION_VISIBILITY_CONTRACT_SCHEMA,
                REPO_RATIFICATION_REVIEW_WORKBENCH_PROJECTION_SCHEMA,
                REPO_POST_PROJECTION_HANDOFF_SCHEMA,
                REPO_OPERATOR_PROJECTION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            }
            - set(self.shipped_record_shapes)
        )
        if missing_shapes:
            raise ValueError(
                f"V74 family closeout must list shipped record shapes: {missing_shapes}"
            )
        object.__setattr__(
            self,
            "operator_projection_authority_boundary",
            _v74c_required_summary(
                self.operator_projection_authority_boundary,
                field_name="operator_projection_authority_boundary",
                required=(
                    "operator projection only",
                    "no product",
                    "no release",
                    "no runtime",
                    "no dispatch",
                ),
            ),
        )
        object.__setattr__(
            self, "limitation_note", _v74c_note(self.limitation_note, field_name="limitation_note")
        )
        expected_id = _surface_id(
            "repo_operator_projection_family_closeout_alignment",
            REPO_OPERATOR_PROJECTION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            self.model_dump(mode="json"),
            "operator_projection_family_closeout_alignment_id",
        )
        if self.operator_projection_family_closeout_alignment_id != expected_id:
            raise ValueError(
                "operator_projection_family_closeout_alignment_id must match canonical full "
                "payload hash identity"
            )
        return self


def _load_v73c_ledger(repo_root: Path) -> RepoSelfImprovementOutcomeLedger:
    return RepoSelfImprovementOutcomeLedger.model_validate(
        _load_json(repo_root, _V73C_LEDGER_FIXTURE)
    )


def _load_v73c_operator_signal(repo_root: Path) -> RepoOperatorCognitionOutcomeSignal:
    return RepoOperatorCognitionOutcomeSignal.model_validate(
        _load_json(repo_root, _V73C_OPERATOR_SIGNAL_FIXTURE)
    )


def _load_v73c_recommendation(repo_root: Path) -> RepoOutcomePromotionDemotionRecommendation:
    return RepoOutcomePromotionDemotionRecommendation.model_validate(
        _load_json(repo_root, _V73C_RECOMMENDATION_FIXTURE)
    )


def _load_v73c_family_closeout(repo_root: Path) -> RepoOutcomeReviewFamilyCloseoutAlignment:
    return RepoOutcomeReviewFamilyCloseoutAlignment.model_validate(
        _load_json(repo_root, _V73C_FAMILY_CLOSEOUT_FIXTURE)
    )


def derive_v74a_repo_operator_projection_source_index(
    *,
    repo_root: Path,
) -> RepoOperatorProjectionSourceIndex:
    del repo_root
    rows = [
        RepoOperatorProjectionSourceRow(
            source_ref=_V73_FAMILY_CLOSEOUT_ALIGNMENT,
            source_kind="evidence_artifact",
            authority_layer="closeout_evidence",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            projection_source_role="family_closeout_source",
            limitation_note="V73 family closeout alignment is projection source only.",
        ),
        RepoOperatorProjectionSourceRow(
            source_ref=_V73C_CLOSEOUT_EVIDENCE,
            source_kind="evidence_artifact",
            authority_layer="closeout_evidence",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            projection_source_role="primary_projection_source",
            limitation_note="V73-C closeout evidence is projection source only.",
        ),
        RepoOperatorProjectionSourceRow(
            source_ref=_V73C_LEDGER_FIXTURE,
            source_kind="fixture_file",
            authority_layer="fixture",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            projection_source_role="outcome_ledger_source",
            limitation_note="Released V73-C ledger fixture is projection source only.",
        ),
        RepoOperatorProjectionSourceRow(
            source_ref=_V73C_OPERATOR_SIGNAL_FIXTURE,
            source_kind="fixture_file",
            authority_layer="fixture",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            projection_source_role="operator_signal_source",
            limitation_note="Released V73-C operator signal fixture is projection source only.",
        ),
        RepoOperatorProjectionSourceRow(
            source_ref=_V73C_RECOMMENDATION_FIXTURE,
            source_kind="fixture_file",
            authority_layer="fixture",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            projection_source_role="recommendation_source",
            limitation_note="Released V73-C recommendation fixture is projection source only.",
        ),
        RepoOperatorProjectionSourceRow(
            source_ref=_V73C_FAMILY_CLOSEOUT_FIXTURE,
            source_kind="fixture_file",
            authority_layer="fixture",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            projection_source_role="family_closeout_source",
            limitation_note="Released V73-C family closeout fixture is projection source only.",
        ),
        RepoOperatorProjectionSourceRow(
            source_ref=_V68_V73_DOGFOOD,
            source_kind="support_doc",
            authority_layer="support",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            projection_source_role="dogfood_source",
            limitation_note="Combined dogfood result is support projection source only.",
        ),
        RepoOperatorProjectionSourceRow(
            source_ref=_PRODUCT_WEDGE_SUPPORT,
            source_kind="support_doc",
            authority_layer="support",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            projection_source_role="product_wedge_source",
            limitation_note="Product wedge support doc is not product authority.",
        ),
    ]
    payload = {
        "schema": REPO_OPERATOR_PROJECTION_SOURCE_INDEX_SCHEMA,
        "review_id": "review:v74a:operator-projection",
        "snapshot_id": "vNext+206-prestart-on-main",
        "source_set_id": "source-set:v74a:released-v73c-projection",
        "source_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.source_ref)
        ],
        "projection_source_summary": (
            "Projection source rows record concrete sources and absence posture; no prose memory "
            "and no authority is minted by source visibility."
        ),
    }
    payload["operator_projection_source_index_id"] = _surface_id(
        "repo_operator_projection_source_index",
        REPO_OPERATOR_PROJECTION_SOURCE_INDEX_SCHEMA,
        payload,
        "operator_projection_source_index_id",
    )
    return RepoOperatorProjectionSourceIndex.model_validate(payload)


def derive_v74a_repo_operator_projection_case_view(
    *,
    repo_root: Path,
    operator_projection_source_index: RepoOperatorProjectionSourceIndex | None = None,
) -> RepoOperatorProjectionCaseView:
    source_index = (
        operator_projection_source_index
        or derive_v74a_repo_operator_projection_source_index(repo_root=repo_root)
    )
    rows = [
        RepoOperatorProjectionCaseViewRow(
            case_view_ref="case-view:v74a:self-evidencing:operator-projection",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            projection_case_kind="self_improvement_outcome_case",
            projection_posture="eligible_for_operator_projection",
            visible_decision_state="ready_for_human_review",
            projection_horizon="human_review_visibility",
            visible_authority_state="ratification_required",
            source_refs=sorted(
                [
                    _V68_V73_DOGFOOD,
                    _V73C_LEDGER_FIXTURE,
                    _V73C_OPERATOR_SIGNAL_FIXTURE,
                    _V73C_RECOMMENDATION_FIXTURE,
                ]
            ),
            ledger_refs=["ledger:v73c:self-evidencing:positive-review-signal"],
            operator_signal_refs=["operator-signal:v73c:self-evidencing:workflow-type-emergence"],
            recommendation_refs=["recommendation:v73c:self-evidencing:promote-for-later-review"],
            family_closeout_refs=["V73"],
            exception_refs=[],
            visible_blocker_rows=[],
            odeu_lanes=["deontic", "epistemic", "utility"],
            guardrail_refs=["guardrail:v74a:self-evidencing:no-authority"],
            limitation_note=(
                "Case view is visibility for human review only with no ratification, "
                "no product authority, no release authority, no runtime permission, "
                "and no dispatch."
            ),
        ),
        RepoOperatorProjectionCaseViewRow(
            case_view_ref="case-view:v74a:product-wedge:future-family",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            projection_case_kind="product_pressure_case",
            projection_posture="future_family_only",
            visible_decision_state="blocked_pending_authority",
            projection_horizon="later_product_review_request",
            visible_authority_state="product_authority_missing",
            source_refs=[_PRODUCT_WEDGE_SUPPORT],
            ledger_refs=[],
            operator_signal_refs=[],
            recommendation_refs=[],
            family_closeout_refs=[],
            exception_refs=["blocker:v74a:product-wedge:product-authority-gap"],
            visible_blocker_rows=[
                RepoProjectionVisibleBlockerRow(
                    blocker_ref="blocker:v74a:product-wedge:product-authority-gap",
                    candidate_ref="candidate:internal:typed_adjudication_product_wedge",
                    case_view_refs=["case-view:v74a:product-wedge:future-family"],
                    blocker_kind="product_authority_gap",
                    source_refs=[_PRODUCT_WEDGE_SUPPORT],
                    blocking_posture="blocking",
                    visible_decision_state="blocked_pending_authority",
                    required_next_surface="future_product_review",
                    limitation_note=(
                        "Product-pressure visibility carries product authority gap only."
                    ),
                )
            ],
            odeu_lanes=["deontic", "epistemic", "utility"],
            guardrail_refs=["guardrail:v74a:product-wedge:no-product-authority"],
            limitation_note=(
                "Product pressure is visible for later review only with no product authority, "
                "no release authority, no runtime permission, and no dispatch."
            ),
        ),
    ]
    payload = {
        "schema": REPO_OPERATOR_PROJECTION_CASE_VIEW_SCHEMA,
        "review_id": source_index.review_id,
        "snapshot_id": source_index.snapshot_id,
        "source_set_id": source_index.source_set_id,
        "operator_projection_source_index_id": source_index.operator_projection_source_index_id,
        "case_view_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.case_view_ref)
        ],
        "projection_boundary_summary": (
            "Operator projection is visibility only: no ratification, no product authorization, "
            "no release authority, no runtime permission, and no dispatch authority."
        ),
    }
    payload["operator_projection_case_view_id"] = _surface_id(
        "repo_operator_projection_case_view",
        REPO_OPERATOR_PROJECTION_CASE_VIEW_SCHEMA,
        payload,
        "operator_projection_case_view_id",
    )
    return RepoOperatorProjectionCaseView.model_validate(payload)


def derive_v74a_repo_operator_projection_non_authority_guardrail(
    *,
    repo_root: Path,
    operator_projection_case_view: RepoOperatorProjectionCaseView | None = None,
) -> RepoOperatorProjectionNonAuthorityGuardrail:
    case_view = operator_projection_case_view or derive_v74a_repo_operator_projection_case_view(
        repo_root=repo_root
    )
    rows = [
        RepoOperatorProjectionNonAuthorityGuardrailRow(
            guardrail_ref="guardrail:v74a:product-wedge:no-product-authority",
            case_view_refs=["case-view:v74a:product-wedge:future-family"],
            candidate_refs=["candidate:internal:typed_adjudication_product_wedge"],
            forbidden_projection_authorities=sorted(_REQUIRED_FORBIDDEN_PROJECTION_AUTHORITIES),
            required_later_authority="product_authority_required",
            operator_action_posture="request_later_review_only",
            non_authority_statement=(
                "This case view is projection only: no ratification, no adoption, no product "
                "authorization, no release authority, no runtime permission, no dispatch "
                "authority, and no external contest authority."
            ),
            limitation_note="Product pressure may request later review only.",
        ),
        RepoOperatorProjectionNonAuthorityGuardrailRow(
            guardrail_ref="guardrail:v74a:self-evidencing:no-authority",
            case_view_refs=["case-view:v74a:self-evidencing:operator-projection"],
            candidate_refs=["candidate:internal:self_evidencing_workflow_type_emergence"],
            forbidden_projection_authorities=sorted(_REQUIRED_FORBIDDEN_PROJECTION_AUTHORITIES),
            required_later_authority="human_ratification_required",
            operator_action_posture="inspect_only",
            non_authority_statement=(
                "This case view is projection only: no ratification, no adoption, no product "
                "authorization, no release authority, no runtime permission, no dispatch "
                "authority, and no external contest authority."
            ),
            limitation_note="Self-evidencing case is visible for human review only.",
        ),
    ]
    payload = {
        "schema": REPO_OPERATOR_PROJECTION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
        "review_id": case_view.review_id,
        "snapshot_id": case_view.snapshot_id,
        "source_set_id": case_view.source_set_id,
        "operator_projection_case_view_id": case_view.operator_projection_case_view_id,
        "guardrail_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.guardrail_ref)
        ],
        "non_authority_summary": (
            "Every case view remains projection only: no ratification, no adoption, no product "
            "authorization, no release authority, no runtime permission, no dispatch authority, "
            "and no external contest authority."
        ),
    }
    payload["operator_projection_non_authority_guardrail_id"] = _surface_id(
        "repo_operator_projection_non_authority_guardrail",
        REPO_OPERATOR_PROJECTION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
        payload,
        "operator_projection_non_authority_guardrail_id",
    )
    return RepoOperatorProjectionNonAuthorityGuardrail.model_validate(payload)


def validate_v74a_operator_projection_bundle(
    *,
    self_improvement_outcome_ledger: RepoSelfImprovementOutcomeLedger,
    operator_cognition_outcome_signal: RepoOperatorCognitionOutcomeSignal,
    outcome_promotion_demotion_recommendation: RepoOutcomePromotionDemotionRecommendation,
    outcome_review_family_closeout_alignment: RepoOutcomeReviewFamilyCloseoutAlignment,
    operator_projection_source_index: RepoOperatorProjectionSourceIndex,
    operator_projection_case_view: RepoOperatorProjectionCaseView,
    operator_projection_non_authority_guardrail: RepoOperatorProjectionNonAuthorityGuardrail,
) -> None:
    if (
        operator_projection_case_view.operator_projection_source_index_id
        != operator_projection_source_index.operator_projection_source_index_id
    ):
        raise ValueError("case view must reference the projection source index")
    if (
        operator_projection_non_authority_guardrail.operator_projection_case_view_id
        != operator_projection_case_view.operator_projection_case_view_id
    ):
        raise ValueError("guardrail must reference the operator projection case view")
    if not (
        operator_projection_source_index.review_id
        == operator_projection_case_view.review_id
        == operator_projection_non_authority_guardrail.review_id
        and operator_projection_source_index.snapshot_id
        == operator_projection_case_view.snapshot_id
        == operator_projection_non_authority_guardrail.snapshot_id
        and operator_projection_source_index.source_set_id
        == operator_projection_case_view.source_set_id
        == operator_projection_non_authority_guardrail.source_set_id
    ):
        raise ValueError("V74-A review_id, snapshot_id, and source_set_id must match")

    source_refs = {row.source_ref for row in operator_projection_source_index.source_rows}
    ledger_rows = {row.ledger_ref: row for row in self_improvement_outcome_ledger.ledger_rows}
    operator_signal_rows = {
        row.operator_signal_ref: row
        for row in operator_cognition_outcome_signal.operator_signal_rows
    }
    recommendation_rows = {
        row.recommendation_ref: row
        for row in outcome_promotion_demotion_recommendation.recommendation_rows
    }
    family_closeout_rows = {
        row.family_ref: row for row in outcome_review_family_closeout_alignment.alignment_rows
    }
    guardrail_rows = {
        row.guardrail_ref: row for row in operator_projection_non_authority_guardrail.guardrail_rows
    }
    case_rows = {row.case_view_ref: row for row in operator_projection_case_view.case_view_rows}

    for case in operator_projection_case_view.case_view_rows:
        missing_sources = sorted(set(case.source_refs) - source_refs)
        if missing_sources:
            raise ValueError(f"case view source refs must be known: {missing_sources}")
        for blocker in case.visible_blocker_rows:
            missing_blocker_sources = sorted(set(blocker.source_refs) - source_refs)
            if missing_blocker_sources:
                raise ValueError(
                    f"visible blocker source refs must be known: {missing_blocker_sources}"
                )
        for ledger_ref in case.ledger_refs:
            ledger = ledger_rows.get(ledger_ref)
            if ledger is None:
                raise ValueError("case views must reference known V73-C ledger rows")
            if ledger.candidate_ref != case.candidate_ref:
                raise ValueError("case view candidate_ref must match ledger candidate_ref")
        for operator_signal_ref in case.operator_signal_refs:
            operator_signal = operator_signal_rows.get(operator_signal_ref)
            if operator_signal is None:
                raise ValueError("case views must reference known operator signal rows")
            if operator_signal.candidate_ref != case.candidate_ref:
                raise ValueError("case view candidate_ref must match operator signal candidate_ref")
        for recommendation_ref in case.recommendation_refs:
            recommendation = recommendation_rows.get(recommendation_ref)
            if recommendation is None:
                raise ValueError("case views must reference known V73-C recommendation rows")
            if recommendation.candidate_ref != case.candidate_ref:
                raise ValueError("case view candidate_ref must match recommendation candidate_ref")
        for family_closeout_ref in case.family_closeout_refs:
            if family_closeout_ref not in family_closeout_rows:
                raise ValueError("case views must reference known V73 family closeout rows")
        for guardrail_ref in case.guardrail_refs:
            guardrail = guardrail_rows.get(guardrail_ref)
            if guardrail is None:
                raise ValueError("case views must reference known projection guardrails")
            if case.case_view_ref not in guardrail.case_view_refs:
                raise ValueError("guardrail rows must reference their case views")
            if case.candidate_ref not in guardrail.candidate_refs:
                raise ValueError("guardrail candidate refs must include case candidate")
        if case.projection_case_kind == "product_pressure_case":
            if not any(
                guardrail_rows[guardrail_ref].required_later_authority
                == "product_authority_required"
                for guardrail_ref in case.guardrail_refs
                if guardrail_ref in guardrail_rows
            ):
                raise ValueError("product-pressure cases require product authority guardrail")

    referenced_guardrails = {
        guardrail_ref
        for case in operator_projection_case_view.case_view_rows
        for guardrail_ref in case.guardrail_refs
    }
    orphan_guardrails = sorted(set(guardrail_rows) - referenced_guardrails)
    if orphan_guardrails:
        raise ValueError(f"guardrail rows must be referenced by case views: {orphan_guardrails}")
    for guardrail in operator_projection_non_authority_guardrail.guardrail_rows:
        for case_view_ref in guardrail.case_view_refs:
            case = case_rows.get(case_view_ref)
            if case is None:
                raise ValueError("guardrail case_view_refs must reference known case views")
            if case.candidate_ref not in guardrail.candidate_refs:
                raise ValueError("guardrail candidate refs must match case views")


def derive_v74a_operator_projection_bundle(
    *,
    repo_root: Path,
) -> tuple[
    RepoSelfImprovementOutcomeLedger,
    RepoOperatorCognitionOutcomeSignal,
    RepoOutcomePromotionDemotionRecommendation,
    RepoOutcomeReviewFamilyCloseoutAlignment,
    RepoOperatorProjectionSourceIndex,
    RepoOperatorProjectionCaseView,
    RepoOperatorProjectionNonAuthorityGuardrail,
]:
    ledger = _load_v73c_ledger(repo_root)
    operator_signal = _load_v73c_operator_signal(repo_root)
    recommendation = _load_v73c_recommendation(repo_root)
    family_closeout = _load_v73c_family_closeout(repo_root)
    source_index = derive_v74a_repo_operator_projection_source_index(repo_root=repo_root)
    case_view = derive_v74a_repo_operator_projection_case_view(
        repo_root=repo_root,
        operator_projection_source_index=source_index,
    )
    guardrail = derive_v74a_repo_operator_projection_non_authority_guardrail(
        repo_root=repo_root,
        operator_projection_case_view=case_view,
    )
    validate_v74a_operator_projection_bundle(
        self_improvement_outcome_ledger=ledger,
        operator_cognition_outcome_signal=operator_signal,
        outcome_promotion_demotion_recommendation=recommendation,
        outcome_review_family_closeout_alignment=family_closeout,
        operator_projection_source_index=source_index,
        operator_projection_case_view=case_view,
        operator_projection_non_authority_guardrail=guardrail,
    )
    return (
        ledger,
        operator_signal,
        recommendation,
        family_closeout,
        source_index,
        case_view,
        guardrail,
    )


def derive_v74b_repo_typed_adjudication_case_view(
    *,
    repo_root: Path,
    operator_projection_case_view: RepoOperatorProjectionCaseView | None = None,
) -> RepoTypedAdjudicationCaseView:
    case_view = operator_projection_case_view or derive_v74a_repo_operator_projection_case_view(
        repo_root=repo_root
    )
    rows = [
        RepoTypedAdjudicationCaseViewRow(
            typed_case_ref="typed-case:v74b:product-wedge:authority-gap",
            source_case_view_refs=["case-view:v74a:product-wedge:future-family"],
            candidate_refs=["candidate:internal:typed_adjudication_product_wedge"],
            conceptual_diff_refs=[_PRODUCT_WEDGE_SUPPORT],
            review_classification_refs=["review-classification:v70:product-wedge:future-family"],
            ratification_refs=[],
            outcome_recommendation_refs=[],
            comparison_projection_refs=[],
            exception_refs=["blocker:v74a:product-wedge:product-authority-gap"],
            typed_case_posture="blocked_by_unresolved_exception",
            odeu_lanes=["deontic", "epistemic", "utility"],
            guardrail_refs=["guardrail:v74a:product-wedge:no-product-authority"],
            limitation_note=(
                "Product wedge typed case is projection only: no ratification, no adoption, "
                "no product authority, no release authority, no runtime permission, and no "
                "dispatch."
            ),
        ),
        RepoTypedAdjudicationCaseViewRow(
            typed_case_ref="typed-case:v74b:self-evidencing:conceptual-diff",
            source_case_view_refs=["case-view:v74a:self-evidencing:operator-projection"],
            candidate_refs=["candidate:internal:self_evidencing_workflow_type_emergence"],
            conceptual_diff_refs=[_CONCEPTUAL_DIFF_SUPPORT],
            review_classification_refs=["review-classification:v70:self-evidencing:bounded"],
            ratification_refs=["ratification:v71:self-evidencing:later-review-only"],
            outcome_recommendation_refs=[
                "recommendation:v73c:self-evidencing:promote-for-later-review"
            ],
            comparison_projection_refs=[
                "comparison-projection:v74b:self-evidencing:model-output-comparison"
            ],
            exception_refs=[],
            typed_case_posture="projection_ready",
            odeu_lanes=["deontic", "epistemic", "utility"],
            guardrail_refs=["guardrail:v74a:self-evidencing:no-authority"],
            limitation_note=(
                "Self-evidencing typed case is projection only: no ratification, no adoption, "
                "no product authority, no release authority, no runtime permission, and no "
                "dispatch."
            ),
        ),
    ]
    payload = {
        "schema": REPO_TYPED_ADJUDICATION_CASE_VIEW_SCHEMA,
        "review_id": "review:v74b:typed-adjudication-projection",
        "snapshot_id": "vNext+207-prestart-on-main",
        "source_set_id": case_view.source_set_id,
        "operator_projection_case_view_id": case_view.operator_projection_case_view_id,
        "typed_case_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.typed_case_ref)
        ],
        "typed_case_boundary_summary": (
            "Typed adjudication case view is projection only: no ratification, no adoption, "
            "no product authorization, no release authority, no runtime permission, and no "
            "dispatch authority."
        ),
    }
    payload["typed_adjudication_case_view_id"] = _surface_id(
        "repo_typed_adjudication_case_view",
        REPO_TYPED_ADJUDICATION_CASE_VIEW_SCHEMA,
        payload,
        "typed_adjudication_case_view_id",
    )
    return RepoTypedAdjudicationCaseView.model_validate(payload)


def derive_v74b_repo_model_output_comparison_projection(
    *,
    repo_root: Path,
    typed_adjudication_case_view: RepoTypedAdjudicationCaseView | None = None,
) -> RepoModelOutputComparisonProjection:
    typed_case_view = typed_adjudication_case_view or derive_v74b_repo_typed_adjudication_case_view(
        repo_root=repo_root
    )
    rows = [
        RepoModelOutputComparisonProjectionRow(
            comparison_projection_ref=(
                "comparison-projection:v74b:self-evidencing:model-output-comparison"
            ),
            typed_case_ref="typed-case:v74b:self-evidencing:conceptual-diff",
            prompt_source_refs=[_V68_V73_DOGFOOD],
            model_output_refs=[
                "model-output:v74b:gpt-5.5-high:conceptual-diff",
                "model-output:v74b:gpt-5.5-xhigh:conceptual-diff",
            ],
            model_output_source_rows=[
                RepoModelOutputSourceRow(
                    model_output_ref="model-output:v74b:gpt-5.5-high:conceptual-diff",
                    prompt_source_ref=_V68_V73_DOGFOOD,
                    model_identity_ref="model:gpt-5.5-high",
                    output_capture_ref=_CONCEPTUAL_DIFF_SUPPORT,
                    run_context_ref="run-context:v74b:fixed-prompt-fixed-repo-substrate",
                    source_presence_posture="present",
                    limitation_note=("Model output provenance is bounded comparison context only."),
                ),
                RepoModelOutputSourceRow(
                    model_output_ref="model-output:v74b:gpt-5.5-xhigh:conceptual-diff",
                    prompt_source_ref=_V68_V73_DOGFOOD,
                    model_identity_ref="model:gpt-5.5-xhigh",
                    output_capture_ref=_CONCEPTUAL_DIFF_SUPPORT,
                    run_context_ref="run-context:v74b:fixed-prompt-fixed-repo-substrate",
                    source_presence_posture="present",
                    limitation_note=("Model output provenance is bounded comparison context only."),
                ),
            ],
            adjudicator_schema_refs=[_CONCEPTUAL_DIFF_SCHEMA_SUPPORT],
            comparison_axis_rows=[
                RepoComparisonAxisRow(
                    axis_ref="axis:v74b:self-evidencing:authority-boundary",
                    axis_kind="authority_boundary_preservation",
                    bounded_claim_horizon=(
                        "Bounded to the V74-B typed projection source rows and the fixed "
                        "conceptual-diff support artifacts."
                    ),
                    axis_source_refs=[_CONCEPTUAL_DIFF_SUPPORT, _V68_V73_DOGFOOD],
                    observed_difference_posture="variants_complementary_on_axis",
                    contradiction_refs=[],
                    complementarity_refs=["complementarity:v74b:high-operational-xhigh-envelope"],
                    exception_refs=[],
                    confidence_posture="moderate_with_limitations",
                    non_benchmark_guardrail=(
                        "This axis is bounded comparison only, not benchmark truth and no model "
                        "selection."
                    ),
                    limitation_note=(
                        "Authority-boundary difference is visible for operator review only."
                    ),
                ),
                RepoComparisonAxisRow(
                    axis_ref="axis:v74b:self-evidencing:operator-legibility",
                    axis_kind="operator_legibility",
                    bounded_claim_horizon=(
                        "Bounded to operator legibility of the existing V68-V73 dogfood and "
                        "conceptual-diff support artifacts."
                    ),
                    axis_source_refs=[_CONCEPTUAL_DIFF_SUPPORT],
                    observed_difference_posture="axis_unchecked",
                    contradiction_refs=[],
                    complementarity_refs=[],
                    exception_refs=["exception:v74b:comparison-axis:operator-legibility-unchecked"],
                    confidence_posture="low_or_inconclusive",
                    non_benchmark_guardrail=(
                        "This unchecked axis is bounded comparison only, not benchmark truth "
                        "and no model selection."
                    ),
                    limitation_note="Operator legibility needs later visibility-contract review.",
                ),
            ],
            contradiction_refs=[],
            complementarity_refs=["complementarity:v74b:high-operational-xhigh-envelope"],
            exception_refs=["exception:v74b:comparison-axis:operator-legibility-unchecked"],
            comparison_projection_posture="blocked_by_unresolved_conflict",
            non_benchmark_guardrail=(
                "The model-output comparison is bounded to fixed sources, not benchmark truth "
                "and no model selection."
            ),
            limitation_note=(
                "Comparison projection is visible for later review only with no ratification, "
                "no product authority, no release authority, no runtime permission, and no "
                "dispatch."
            ),
        )
    ]
    payload = {
        "schema": REPO_MODEL_OUTPUT_COMPARISON_PROJECTION_SCHEMA,
        "review_id": typed_case_view.review_id,
        "snapshot_id": typed_case_view.snapshot_id,
        "source_set_id": typed_case_view.source_set_id,
        "typed_adjudication_case_view_id": typed_case_view.typed_adjudication_case_view_id,
        "comparison_projection_rows": [
            row.model_dump(mode="json")
            for row in sorted(rows, key=lambda row: row.comparison_projection_ref)
        ],
        "comparison_boundary_summary": (
            "Model-output comparison projection is bounded, not benchmark truth, no model "
            "selection, and no dispatch authority."
        ),
    }
    payload["model_output_comparison_projection_id"] = _surface_id(
        "repo_model_output_comparison_projection",
        REPO_MODEL_OUTPUT_COMPARISON_PROJECTION_SCHEMA,
        payload,
        "model_output_comparison_projection_id",
    )
    return RepoModelOutputComparisonProjection.model_validate(payload)


def derive_v74b_repo_projection_exception_visibility_register(
    *,
    repo_root: Path,
    operator_projection_case_view: RepoOperatorProjectionCaseView | None = None,
    typed_adjudication_case_view: RepoTypedAdjudicationCaseView | None = None,
    model_output_comparison_projection: RepoModelOutputComparisonProjection | None = None,
) -> RepoProjectionExceptionVisibilityRegister:
    case_view = operator_projection_case_view or derive_v74a_repo_operator_projection_case_view(
        repo_root=repo_root
    )
    typed_case_view = typed_adjudication_case_view or derive_v74b_repo_typed_adjudication_case_view(
        repo_root=repo_root,
        operator_projection_case_view=case_view,
    )
    comparison_projection = (
        model_output_comparison_projection
        or derive_v74b_repo_model_output_comparison_projection(
            repo_root=repo_root,
            typed_adjudication_case_view=typed_case_view,
        )
    )
    rows = [
        RepoProjectionExceptionVisibilityRow(
            exception_ref="exception:v74b:comparison-axis:operator-legibility-unchecked",
            case_view_refs=["case-view:v74a:self-evidencing:operator-projection"],
            typed_case_refs=["typed-case:v74b:self-evidencing:conceptual-diff"],
            comparison_projection_refs=[
                "comparison-projection:v74b:self-evidencing:model-output-comparison"
            ],
            candidate_refs=["candidate:internal:self_evidencing_workflow_type_emergence"],
            exception_kind="comparison_axis_unchecked",
            source_refs=[_CONCEPTUAL_DIFF_SUPPORT],
            visible_decision_state="recommended_more_evidence",
            blocking_posture="warning_only",
            required_next_surface="v74c_visibility_contract",
            limitation_note=("Operator-legibility axis remains visible and not resolved by V74-B."),
        ),
        RepoProjectionExceptionVisibilityRow(
            exception_ref="blocker:v74a:product-wedge:product-authority-gap",
            case_view_refs=["case-view:v74a:product-wedge:future-family"],
            typed_case_refs=["typed-case:v74b:product-wedge:authority-gap"],
            comparison_projection_refs=[],
            candidate_refs=["candidate:internal:typed_adjudication_product_wedge"],
            exception_kind="product_authority_missing",
            source_refs=[_PRODUCT_WEDGE_SUPPORT],
            visible_decision_state="blocked_pending_authority",
            blocking_posture="blocking",
            required_next_surface="future_product_review",
            limitation_note=("Product authority gap remains visible and not resolved by V74-B."),
        ),
    ]
    payload = {
        "schema": REPO_PROJECTION_EXCEPTION_VISIBILITY_REGISTER_SCHEMA,
        "review_id": typed_case_view.review_id,
        "snapshot_id": typed_case_view.snapshot_id,
        "source_set_id": typed_case_view.source_set_id,
        "operator_projection_case_view_id": case_view.operator_projection_case_view_id,
        "typed_adjudication_case_view_id": typed_case_view.typed_adjudication_case_view_id,
        "model_output_comparison_projection_id": (
            comparison_projection.model_output_comparison_projection_id
        ),
        "exception_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.exception_ref)
        ],
        "exception_visibility_summary": (
            "Exceptions remain visible and not resolved by V74-B: no product authorization, "
            "no release authority, and no dispatch authority."
        ),
    }
    payload["projection_exception_visibility_register_id"] = _surface_id(
        "repo_projection_exception_visibility_register",
        REPO_PROJECTION_EXCEPTION_VISIBILITY_REGISTER_SCHEMA,
        payload,
        "projection_exception_visibility_register_id",
    )
    return RepoProjectionExceptionVisibilityRegister.model_validate(payload)


def validate_v74b_operator_projection_bundle(
    *,
    operator_projection_source_index: RepoOperatorProjectionSourceIndex,
    operator_projection_case_view: RepoOperatorProjectionCaseView,
    operator_projection_non_authority_guardrail: RepoOperatorProjectionNonAuthorityGuardrail,
    typed_adjudication_case_view: RepoTypedAdjudicationCaseView,
    model_output_comparison_projection: RepoModelOutputComparisonProjection,
    projection_exception_visibility_register: RepoProjectionExceptionVisibilityRegister,
) -> None:
    if (
        typed_adjudication_case_view.operator_projection_case_view_id
        != operator_projection_case_view.operator_projection_case_view_id
    ):
        raise ValueError("typed adjudication cases must reference released V74-A case view")
    if (
        model_output_comparison_projection.typed_adjudication_case_view_id
        != typed_adjudication_case_view.typed_adjudication_case_view_id
    ):
        raise ValueError("comparison projection must reference typed adjudication case view")
    if (
        projection_exception_visibility_register.operator_projection_case_view_id
        != operator_projection_case_view.operator_projection_case_view_id
        or projection_exception_visibility_register.typed_adjudication_case_view_id
        != typed_adjudication_case_view.typed_adjudication_case_view_id
        or projection_exception_visibility_register.model_output_comparison_projection_id
        != model_output_comparison_projection.model_output_comparison_projection_id
    ):
        raise ValueError("exception visibility register must reference V74-B surfaces")
    if not (
        typed_adjudication_case_view.review_id
        == model_output_comparison_projection.review_id
        == projection_exception_visibility_register.review_id
        and typed_adjudication_case_view.snapshot_id
        == model_output_comparison_projection.snapshot_id
        == projection_exception_visibility_register.snapshot_id
        and typed_adjudication_case_view.source_set_id
        == model_output_comparison_projection.source_set_id
        == projection_exception_visibility_register.source_set_id
    ):
        raise ValueError("V74-B review_id, snapshot_id, and source_set_id must match")

    known_source_refs = {row.source_ref for row in operator_projection_source_index.source_rows} | {
        _CONCEPTUAL_DIFF_SUPPORT,
        _CONCEPTUAL_DIFF_SCHEMA_SUPPORT,
    }
    case_rows = {row.case_view_ref: row for row in operator_projection_case_view.case_view_rows}
    guardrail_rows = {
        row.guardrail_ref: row for row in operator_projection_non_authority_guardrail.guardrail_rows
    }
    typed_case_rows = {
        row.typed_case_ref: row for row in typed_adjudication_case_view.typed_case_rows
    }
    comparison_rows = {
        row.comparison_projection_ref: row
        for row in model_output_comparison_projection.comparison_projection_rows
    }
    exception_rows = {
        row.exception_ref: row for row in projection_exception_visibility_register.exception_rows
    }

    for typed_case in typed_adjudication_case_view.typed_case_rows:
        for case_ref in typed_case.source_case_view_refs:
            case = case_rows.get(case_ref)
            if case is None:
                raise ValueError("typed adjudication cases must reference known V74-A case views")
            if not set(typed_case.candidate_refs) <= {case.candidate_ref}:
                raise ValueError("typed case candidate refs must match source case candidates")
        for guardrail_ref in typed_case.guardrail_refs:
            if guardrail_ref not in guardrail_rows:
                raise ValueError("typed cases must reference known V74-A guardrails")
        for exception_ref in typed_case.exception_refs:
            if exception_ref not in exception_rows:
                raise ValueError("typed case exception refs must be visible exception rows")
        for comparison_ref in typed_case.comparison_projection_refs:
            if comparison_ref not in comparison_rows:
                raise ValueError("typed case comparison refs must reference comparison rows")
        if "candidate:internal:typed_adjudication_product_wedge" in typed_case.candidate_refs:
            if not any(
                exception_rows[exception_ref].exception_kind == "product_authority_missing"
                for exception_ref in typed_case.exception_refs
                if exception_ref in exception_rows
            ):
                raise ValueError("product wedge typed cases require product authority exception")

    for comparison in model_output_comparison_projection.comparison_projection_rows:
        typed_case = typed_case_rows.get(comparison.typed_case_ref)
        if typed_case is None:
            raise ValueError("comparison projection must reference known typed cases")
        for source_ref in comparison.prompt_source_refs + comparison.adjudicator_schema_refs:
            if source_ref not in known_source_refs:
                raise ValueError("comparison projection source refs must be known")
        for axis in comparison.comparison_axis_rows:
            missing_axis_sources = sorted(set(axis.axis_source_refs) - known_source_refs)
            if missing_axis_sources:
                raise ValueError(
                    f"comparison axis source refs must be known: {missing_axis_sources}"
                )
            for exception_ref in axis.exception_refs:
                if exception_ref not in exception_rows:
                    raise ValueError("comparison axis exception refs must be visible")
        for exception_ref in comparison.exception_refs:
            if exception_ref not in exception_rows:
                raise ValueError("comparison exception refs must be visible")
        if any(
            "global" in axis.bounded_claim_horizon.lower()
            for axis in comparison.comparison_axis_rows
        ):
            raise ValueError("comparison axes must not claim global model ranking")

    for exception in projection_exception_visibility_register.exception_rows:
        missing_exception_sources = sorted(set(exception.source_refs) - known_source_refs)
        if missing_exception_sources:
            raise ValueError(
                f"exception visibility source refs must be known: {missing_exception_sources}"
            )
        for case_ref in exception.case_view_refs:
            if case_ref not in case_rows:
                raise ValueError("exception case refs must reference known V74-A cases")
        for typed_case_ref in exception.typed_case_refs:
            if typed_case_ref not in typed_case_rows:
                raise ValueError("exception typed case refs must reference known typed cases")
        for comparison_ref in exception.comparison_projection_refs:
            if comparison_ref not in comparison_rows:
                raise ValueError("exception comparison refs must reference known comparisons")

    v74a_exception_refs = {
        exception_ref
        for case in operator_projection_case_view.case_view_rows
        for exception_ref in case.exception_refs
    }
    missing_v74a_exceptions = sorted(v74a_exception_refs - set(exception_rows))
    if missing_v74a_exceptions:
        raise ValueError(
            f"known V74-A exceptions must remain visible in V74-B: {missing_v74a_exceptions}"
        )


def derive_v74b_operator_projection_bundle(
    *,
    repo_root: Path,
) -> tuple[
    RepoOperatorProjectionSourceIndex,
    RepoOperatorProjectionCaseView,
    RepoOperatorProjectionNonAuthorityGuardrail,
    RepoTypedAdjudicationCaseView,
    RepoModelOutputComparisonProjection,
    RepoProjectionExceptionVisibilityRegister,
]:
    *_, source_index, case_view, guardrail = derive_v74a_operator_projection_bundle(
        repo_root=repo_root
    )
    typed_case = derive_v74b_repo_typed_adjudication_case_view(
        repo_root=repo_root,
        operator_projection_case_view=case_view,
    )
    comparison_projection = derive_v74b_repo_model_output_comparison_projection(
        repo_root=repo_root,
        typed_adjudication_case_view=typed_case,
    )
    exception_register = derive_v74b_repo_projection_exception_visibility_register(
        repo_root=repo_root,
        operator_projection_case_view=case_view,
        typed_adjudication_case_view=typed_case,
        model_output_comparison_projection=comparison_projection,
    )
    validate_v74b_operator_projection_bundle(
        operator_projection_source_index=source_index,
        operator_projection_case_view=case_view,
        operator_projection_non_authority_guardrail=guardrail,
        typed_adjudication_case_view=typed_case,
        model_output_comparison_projection=comparison_projection,
        projection_exception_visibility_register=exception_register,
    )
    return (
        source_index,
        case_view,
        guardrail,
        typed_case,
        comparison_projection,
        exception_register,
    )


def _human_ratification_requirement() -> RepoProjectionLaterAuthorityRequirementRow:
    return RepoProjectionLaterAuthorityRequirementRow(
        authority_requirement_ref="authority:v74c:self-evidencing:human-ratification",
        authority_kind="human_ratification_required",
        authority_source_refs=[_V74C_LOCK],
        source_presence_posture="present",
        required_before_action="before_ratification_review",
        limitation_note="Human ratification remains required before later review action.",
    )


def _dispatch_authority_requirement() -> RepoProjectionLaterAuthorityRequirementRow:
    return RepoProjectionLaterAuthorityRequirementRow(
        authority_requirement_ref="authority:v74c:self-evidencing:dispatch-review",
        authority_kind="dispatch_authority_required",
        authority_source_refs=[_V74C_LOCK],
        source_presence_posture="present",
        required_before_action="before_dispatch_review",
        limitation_note="Dispatch authority remains required before any later dispatch review.",
    )


def _product_authority_requirement() -> RepoProjectionLaterAuthorityRequirementRow:
    return RepoProjectionLaterAuthorityRequirementRow(
        authority_requirement_ref="authority:v74c:product-wedge:product-review",
        authority_kind="product_authority_required",
        authority_source_refs=[_V74C_LOCK, _PRODUCT_WEDGE_SUPPORT],
        source_presence_posture="present",
        required_before_action="before_product_review",
        limitation_note="Product authority remains required before any later product review.",
    )


def derive_v74c_repo_decision_visibility_contract(
    *,
    repo_root: Path,
    operator_projection_case_view: RepoOperatorProjectionCaseView | None = None,
    typed_adjudication_case_view: RepoTypedAdjudicationCaseView | None = None,
    projection_exception_visibility_register: (
        RepoProjectionExceptionVisibilityRegister | None
    ) = None,
) -> RepoDecisionVisibilityContract:
    del repo_root
    if (
        operator_projection_case_view is None
        or typed_adjudication_case_view is None
        or projection_exception_visibility_register is None
    ):
        raise ValueError("V74-C decision contract derivation requires released V74-A/B inputs")
    rows = [
        RepoDecisionVisibilityContractRow(
            visibility_contract_ref="visibility-contract:v74c:self-evidencing:operator-review",
            case_view_refs=["case-view:v74a:self-evidencing:operator-projection"],
            typed_case_refs=["typed-case:v74b:self-evidencing:conceptual-diff"],
            exception_refs=["exception:v74b:comparison-axis:operator-legibility-unchecked"],
            visible_decision_state="recommended_more_evidence",
            visible_source_refs=sorted(
                [
                    _CONCEPTUAL_DIFF_SUPPORT,
                    _V74A_CLOSEOUT_EVIDENCE,
                    _V74B_CLOSEOUT_EVIDENCE,
                ]
            ),
            visible_exception_refs=["exception:v74b:comparison-axis:operator-legibility-unchecked"],
            visibility_obligation_kinds=sorted(_REQUIRED_VISIBILITY_OBLIGATIONS),
            non_derivable_authority_kinds=sorted(_REQUIRED_NON_DERIVABLE_AUTHORITIES),
            operator_action_postures=["inspect_only", "request_later_review_only"],
            required_later_authority=[
                "dispatch_authority_required",
                "human_ratification_required",
            ],
            required_later_authority_rows=[
                _dispatch_authority_requirement(),
                _human_ratification_requirement(),
            ],
            contract_posture="visibility_contract_ready",
            limitation_note=(
                "Decision visibility contract is visibility only for later review with "
                "no ratification, no product authority, no release authority, no runtime "
                "permission, and no dispatch."
            ),
        ),
        RepoDecisionVisibilityContractRow(
            visibility_contract_ref="visibility-contract:v74c:product-wedge:authority-gap",
            case_view_refs=["case-view:v74a:product-wedge:future-family"],
            typed_case_refs=["typed-case:v74b:product-wedge:authority-gap"],
            exception_refs=["blocker:v74a:product-wedge:product-authority-gap"],
            visible_decision_state="blocked_pending_authority",
            visible_source_refs=sorted([_PRODUCT_WEDGE_SUPPORT, _V74B_CLOSEOUT_EVIDENCE]),
            visible_exception_refs=["blocker:v74a:product-wedge:product-authority-gap"],
            visibility_obligation_kinds=sorted(_REQUIRED_VISIBILITY_OBLIGATIONS),
            non_derivable_authority_kinds=sorted(_REQUIRED_NON_DERIVABLE_AUTHORITIES),
            operator_action_postures=["inspect_only", "request_later_review_only"],
            required_later_authority=["product_authority_required"],
            required_later_authority_rows=[_product_authority_requirement()],
            contract_posture="blocked_by_authority_boundary",
            limitation_note=(
                "Product-pressure visibility is blocked by product authority gap with "
                "no product authority, no release authority, no runtime permission, and no "
                "dispatch."
            ),
        ),
    ]
    payload = {
        "schema": REPO_DECISION_VISIBILITY_CONTRACT_SCHEMA,
        "review_id": typed_adjudication_case_view.review_id,
        "snapshot_id": typed_adjudication_case_view.snapshot_id,
        "source_set_id": typed_adjudication_case_view.source_set_id,
        "operator_projection_case_view_id": (
            operator_projection_case_view.operator_projection_case_view_id
        ),
        "typed_adjudication_case_view_id": (
            typed_adjudication_case_view.typed_adjudication_case_view_id
        ),
        "projection_exception_visibility_register_id": (
            projection_exception_visibility_register.projection_exception_visibility_register_id
        ),
        "visibility_contract_rows": [
            row.model_dump(mode="json")
            for row in sorted(rows, key=lambda row: row.visibility_contract_ref)
        ],
        "decision_visibility_summary": (
            "Decision visibility contract is visibility only: no ratification, no product "
            "authorization, no release authority, no runtime permission, and no dispatch."
        ),
    }
    payload["decision_visibility_contract_id"] = _surface_id(
        "repo_decision_visibility_contract",
        REPO_DECISION_VISIBILITY_CONTRACT_SCHEMA,
        payload,
        "decision_visibility_contract_id",
    )
    return RepoDecisionVisibilityContract.model_validate(payload)


def derive_v74c_repo_ratification_review_workbench_projection(
    *,
    repo_root: Path,
    decision_visibility_contract: RepoDecisionVisibilityContract | None = None,
) -> RepoRatificationReviewWorkbenchProjection:
    del repo_root
    if decision_visibility_contract is None:
        raise ValueError("V74-C workbench derivation requires decision visibility contract")
    rows = [
        RepoRatificationReviewWorkbenchProjectionRow(
            workbench_projection_ref="workbench:v74c:self-evidencing:operator-review",
            visibility_contract_refs=[
                "visibility-contract:v74c:self-evidencing:operator-review"
            ],
            case_view_refs=["case-view:v74a:self-evidencing:operator-projection"],
            candidate_refs=["candidate:internal:self_evidencing_workflow_type_emergence"],
            ratification_refs=[],
            recommendation_refs=["recommendation:v73c:self-evidencing:promote-for-later-review"],
            exception_refs=["exception:v74b:comparison-axis:operator-legibility-unchecked"],
            permitted_operator_action_postures=[
                "annotate_source_gap_only",
                "export_support_report_only",
                "inspect_only",
                "request_later_review_only",
            ],
            forbidden_operator_action_postures=sorted(_REQUIRED_FORBIDDEN_OPERATOR_ACTIONS),
            required_later_authority=[
                "dispatch_authority_required",
                "human_ratification_required",
            ],
            required_later_authority_rows=[
                _dispatch_authority_requirement(),
                _human_ratification_requirement(),
            ],
            workbench_projection_posture="projection_ready_for_operator_review",
            limitation_note=(
                "Ratification-review workbench projection is review visibility only with "
                "no ratification, no product authority, no release authority, no runtime "
                "permission, and no dispatch."
            ),
        ),
        RepoRatificationReviewWorkbenchProjectionRow(
            workbench_projection_ref="workbench:v74c:product-wedge:authority-gap",
            visibility_contract_refs=["visibility-contract:v74c:product-wedge:authority-gap"],
            case_view_refs=["case-view:v74a:product-wedge:future-family"],
            candidate_refs=["candidate:internal:typed_adjudication_product_wedge"],
            ratification_refs=[],
            recommendation_refs=[],
            exception_refs=["blocker:v74a:product-wedge:product-authority-gap"],
            permitted_operator_action_postures=[
                "annotate_source_gap_only",
                "inspect_only",
                "request_later_review_only",
            ],
            forbidden_operator_action_postures=sorted(_REQUIRED_FORBIDDEN_OPERATOR_ACTIONS),
            required_later_authority=["product_authority_required"],
            required_later_authority_rows=[_product_authority_requirement()],
            workbench_projection_posture="blocked_by_authority_boundary",
            limitation_note=(
                "Product-pressure workbench projection is blocked by authority boundary with "
                "no product authority, no release authority, no runtime permission, and no "
                "dispatch."
            ),
        ),
    ]
    payload = {
        "schema": REPO_RATIFICATION_REVIEW_WORKBENCH_PROJECTION_SCHEMA,
        "review_id": decision_visibility_contract.review_id,
        "snapshot_id": decision_visibility_contract.snapshot_id,
        "source_set_id": decision_visibility_contract.source_set_id,
        "decision_visibility_contract_id": (
            decision_visibility_contract.decision_visibility_contract_id
        ),
        "workbench_projection_rows": [
            row.model_dump(mode="json")
            for row in sorted(rows, key=lambda row: row.workbench_projection_ref)
        ],
        "workbench_boundary_summary": (
            "Ratification-review workbench projection is review visibility only: no "
            "ratification, no product authorization, no release authority, no runtime "
            "permission, and no dispatch."
        ),
    }
    payload["ratification_review_workbench_projection_id"] = _surface_id(
        "repo_ratification_review_workbench_projection",
        REPO_RATIFICATION_REVIEW_WORKBENCH_PROJECTION_SCHEMA,
        payload,
        "ratification_review_workbench_projection_id",
    )
    return RepoRatificationReviewWorkbenchProjection.model_validate(payload)


def derive_v74c_repo_post_projection_handoff(
    *,
    repo_root: Path,
    decision_visibility_contract: RepoDecisionVisibilityContract | None = None,
    ratification_review_workbench_projection: (
        RepoRatificationReviewWorkbenchProjection | None
    ) = None,
) -> RepoPostProjectionHandoff:
    del repo_root
    if decision_visibility_contract is None or ratification_review_workbench_projection is None:
        raise ValueError("V74-C handoff derivation requires contract and workbench projection")
    rows = [
        RepoPostProjectionHandoffRow(
            handoff_ref="handoff:v74c:self-evidencing:v75-review-request",
            visibility_contract_refs=[
                "visibility-contract:v74c:self-evidencing:operator-review"
            ],
            workbench_projection_refs=["workbench:v74c:self-evidencing:operator-review"],
            candidate_refs=["candidate:internal:self_evidencing_workflow_type_emergence"],
            handoff_target="v75_dispatch_review",
            handoff_posture="ready_for_later_review",
            carried_exception_refs=[
                "exception:v74b:comparison-axis:operator-legibility-unchecked"
            ],
            required_later_authority=[
                "dispatch_authority_required",
                "human_ratification_required",
            ],
            non_dispatch_guardrail=(
                "This handoff is a request for later review only with no dispatch."
            ),
            limitation_note=(
                "V75 handoff is later-review request only with no runtime permission and no "
                "dispatch."
            ),
        ),
        RepoPostProjectionHandoffRow(
            handoff_ref="handoff:v74c:product-wedge:future-product-review",
            visibility_contract_refs=["visibility-contract:v74c:product-wedge:authority-gap"],
            workbench_projection_refs=["workbench:v74c:product-wedge:authority-gap"],
            candidate_refs=["candidate:internal:typed_adjudication_product_wedge"],
            handoff_target="future_product_review",
            handoff_posture="blocked_by_authority_boundary",
            carried_exception_refs=["blocker:v74a:product-wedge:product-authority-gap"],
            required_later_authority=["product_authority_required"],
            non_dispatch_guardrail=(
                "This handoff is a request for later review only with no dispatch."
            ),
            limitation_note=(
                "Product-pressure handoff stays blocked by authority boundary with no product "
                "authority, no runtime permission, and no dispatch."
            ),
        ),
    ]
    payload = {
        "schema": REPO_POST_PROJECTION_HANDOFF_SCHEMA,
        "review_id": decision_visibility_contract.review_id,
        "snapshot_id": decision_visibility_contract.snapshot_id,
        "source_set_id": decision_visibility_contract.source_set_id,
        "decision_visibility_contract_id": (
            decision_visibility_contract.decision_visibility_contract_id
        ),
        "ratification_review_workbench_projection_id": (
            ratification_review_workbench_projection.ratification_review_workbench_projection_id
        ),
        "handoff_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.handoff_ref)
        ],
        "handoff_boundary_summary": (
            "Post-projection handoff requests later review only: no dispatch, no runtime "
            "permission, no product authorization, and no release authority."
        ),
    }
    payload["post_projection_handoff_id"] = _surface_id(
        "repo_post_projection_handoff",
        REPO_POST_PROJECTION_HANDOFF_SCHEMA,
        payload,
        "post_projection_handoff_id",
    )
    return RepoPostProjectionHandoff.model_validate(payload)


def derive_v74c_repo_operator_projection_family_closeout_alignment(
    *,
    repo_root: Path,
) -> RepoOperatorProjectionFamilyCloseoutAlignment:
    del repo_root
    payload = {
        "schema": REPO_OPERATOR_PROJECTION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
        "family": "V74",
        "closed_by_arc": "vNext+208",
        "closed_slice_ladder": ["V74-A", "V74-B", "V74-C"],
        "shipped_record_shapes": sorted(
            [
                REPO_OPERATOR_PROJECTION_CASE_VIEW_SCHEMA,
                REPO_OPERATOR_PROJECTION_SOURCE_INDEX_SCHEMA,
                REPO_OPERATOR_PROJECTION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
                REPO_TYPED_ADJUDICATION_CASE_VIEW_SCHEMA,
                REPO_MODEL_OUTPUT_COMPARISON_PROJECTION_SCHEMA,
                REPO_PROJECTION_EXCEPTION_VISIBILITY_REGISTER_SCHEMA,
                REPO_DECISION_VISIBILITY_CONTRACT_SCHEMA,
                REPO_RATIFICATION_REVIEW_WORKBENCH_PROJECTION_SCHEMA,
                REPO_POST_PROJECTION_HANDOFF_SCHEMA,
                REPO_OPERATOR_PROJECTION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            ]
        ),
        "consumed_source_families": ["V68", "V69", "V70", "V71", "V72", "V73"],
        "future_family_authority": [
            "V75 dispatch review remains future-family authority",
            "product authorization remains future-family or maintainer authority",
            "release authority remains maintainer or release-lock authority",
        ],
        "unselected_future_surfaces": sorted(
            [
                "external contest participation",
                "live product UI",
                "operator command execution",
                "product authorization",
                "runtime permission",
                "V75 dispatch execution",
            ]
        ),
        "operator_projection_authority_boundary": (
            "V74 closes as operator projection only: no product authorization, no release "
            "authority, no runtime permission, and no dispatch authority."
        ),
        "limitation_note": (
            "Family closeout alignment closes projection visibility only and grants no downstream "
            "authority."
        ),
    }
    payload["operator_projection_family_closeout_alignment_id"] = _surface_id(
        "repo_operator_projection_family_closeout_alignment",
        REPO_OPERATOR_PROJECTION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
        payload,
        "operator_projection_family_closeout_alignment_id",
    )
    return RepoOperatorProjectionFamilyCloseoutAlignment.model_validate(payload)


def validate_v74c_operator_projection_bundle(
    *,
    operator_projection_source_index: RepoOperatorProjectionSourceIndex,
    operator_projection_case_view: RepoOperatorProjectionCaseView,
    typed_adjudication_case_view: RepoTypedAdjudicationCaseView,
    projection_exception_visibility_register: RepoProjectionExceptionVisibilityRegister,
    decision_visibility_contract: RepoDecisionVisibilityContract,
    ratification_review_workbench_projection: RepoRatificationReviewWorkbenchProjection,
    post_projection_handoff: RepoPostProjectionHandoff,
    operator_projection_family_closeout_alignment: RepoOperatorProjectionFamilyCloseoutAlignment,
) -> None:
    if (
        decision_visibility_contract.operator_projection_case_view_id
        != operator_projection_case_view.operator_projection_case_view_id
        or decision_visibility_contract.typed_adjudication_case_view_id
        != typed_adjudication_case_view.typed_adjudication_case_view_id
        or decision_visibility_contract.projection_exception_visibility_register_id
        != projection_exception_visibility_register.projection_exception_visibility_register_id
    ):
        raise ValueError("decision visibility contract must reference released V74-A/B surfaces")
    if (
        ratification_review_workbench_projection.decision_visibility_contract_id
        != decision_visibility_contract.decision_visibility_contract_id
    ):
        raise ValueError("workbench projection must reference decision visibility contract")
    if (
        post_projection_handoff.decision_visibility_contract_id
        != decision_visibility_contract.decision_visibility_contract_id
        or post_projection_handoff.ratification_review_workbench_projection_id
        != ratification_review_workbench_projection.ratification_review_workbench_projection_id
    ):
        raise ValueError("post-projection handoff must reference V74-C contract and workbench")
    if not (
        decision_visibility_contract.review_id
        == ratification_review_workbench_projection.review_id
        == post_projection_handoff.review_id
        and decision_visibility_contract.snapshot_id
        == ratification_review_workbench_projection.snapshot_id
        == post_projection_handoff.snapshot_id
        and decision_visibility_contract.source_set_id
        == ratification_review_workbench_projection.source_set_id
        == post_projection_handoff.source_set_id
    ):
        raise ValueError("V74-C review_id, snapshot_id, and source_set_id must match")

    known_source_refs = {row.source_ref for row in operator_projection_source_index.source_rows} | {
        _CONCEPTUAL_DIFF_SUPPORT,
        _CONCEPTUAL_DIFF_SCHEMA_SUPPORT,
        _V74A_CLOSEOUT_EVIDENCE,
        _V74B_CLOSEOUT_EVIDENCE,
        _V74A_LOCK,
        _V74B_LOCK,
        _V74C_LOCK,
    }
    case_rows = {row.case_view_ref: row for row in operator_projection_case_view.case_view_rows}
    typed_case_rows = {
        row.typed_case_ref: row for row in typed_adjudication_case_view.typed_case_rows
    }
    exception_rows = {
        row.exception_ref: row for row in projection_exception_visibility_register.exception_rows
    }
    contract_rows = {
        row.visibility_contract_ref: row
        for row in decision_visibility_contract.visibility_contract_rows
    }
    workbench_rows = {
        row.workbench_projection_ref: row
        for row in ratification_review_workbench_projection.workbench_projection_rows
    }

    for contract in decision_visibility_contract.visibility_contract_rows:
        for case_ref in contract.case_view_refs:
            if case_ref not in case_rows:
                raise ValueError("visibility contracts must reference known V74-A case refs")
        for typed_case_ref in contract.typed_case_refs:
            if typed_case_ref not in typed_case_rows:
                raise ValueError("visibility contracts must reference known V74-B typed cases")
        for exception_ref in contract.exception_refs:
            if exception_ref not in exception_rows:
                raise ValueError("visibility contracts must reference known V74-B exceptions")
        missing_sources = sorted(set(contract.visible_source_refs) - known_source_refs)
        if missing_sources:
            raise ValueError(f"visibility contract source refs must be known: {missing_sources}")
        for authority_row in contract.required_later_authority_rows:
            missing_authority_sources = sorted(
                set(authority_row.authority_source_refs) - known_source_refs
            )
            if missing_authority_sources:
                raise ValueError(
                    f"authority requirement source refs must be known: {missing_authority_sources}"
                )
        if "candidate:internal:typed_adjudication_product_wedge" in {
            case_rows[case_ref].candidate_ref
            for case_ref in contract.case_view_refs
            if case_ref in case_rows
        } and "product_authority_required" not in contract.required_later_authority:
            raise ValueError("product-pressure contracts require product authority")

    for workbench in ratification_review_workbench_projection.workbench_projection_rows:
        for contract_ref in workbench.visibility_contract_refs:
            if contract_ref not in contract_rows:
                raise ValueError("workbench projections must reference visibility contracts")
        for case_ref in workbench.case_view_refs:
            if case_ref not in case_rows:
                raise ValueError("workbench projections must reference known case views")
        for exception_ref in workbench.exception_refs:
            if exception_ref not in exception_rows:
                raise ValueError("workbench exception refs must be known")
        for authority_row in workbench.required_later_authority_rows:
            missing_authority_sources = sorted(
                set(authority_row.authority_source_refs) - known_source_refs
            )
            if missing_authority_sources:
                raise ValueError(
                    f"workbench authority source refs must be known: {missing_authority_sources}"
                )

    for handoff in post_projection_handoff.handoff_rows:
        for contract_ref in handoff.visibility_contract_refs:
            if contract_ref not in contract_rows:
                raise ValueError("post-projection handoff must reference visibility contracts")
        for workbench_ref in handoff.workbench_projection_refs:
            if workbench_ref not in workbench_rows:
                raise ValueError("post-projection handoff must reference workbench projections")
        for exception_ref in handoff.carried_exception_refs:
            exception = exception_rows.get(exception_ref)
            if exception is None:
                raise ValueError("handoff carried exceptions must be known")
            if (
                exception.blocking_posture == "blocking"
                and handoff.handoff_posture == "ready_for_later_review"
            ):
                raise ValueError("handoff with blocking carried exceptions cannot be ready")
        if handoff.handoff_target == "v75_dispatch_review" and (
            "dispatch_authority_required" not in handoff.required_later_authority
        ):
            raise ValueError("V75 handoff requires dispatch authority")

    if (
        REPO_OPERATOR_PROJECTION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
        not in operator_projection_family_closeout_alignment.shipped_record_shapes
    ):
        raise ValueError("family closeout must include its own alignment surface")


def derive_v74c_operator_projection_bundle(
    *,
    repo_root: Path,
) -> tuple[
    RepoOperatorProjectionSourceIndex,
    RepoOperatorProjectionCaseView,
    RepoOperatorProjectionNonAuthorityGuardrail,
    RepoTypedAdjudicationCaseView,
    RepoModelOutputComparisonProjection,
    RepoProjectionExceptionVisibilityRegister,
    RepoDecisionVisibilityContract,
    RepoRatificationReviewWorkbenchProjection,
    RepoPostProjectionHandoff,
    RepoOperatorProjectionFamilyCloseoutAlignment,
]:
    (
        source_index,
        case_view,
        guardrail,
        typed_case,
        comparison_projection,
        exception_register,
    ) = derive_v74b_operator_projection_bundle(repo_root=repo_root)
    decision_contract = derive_v74c_repo_decision_visibility_contract(
        repo_root=repo_root,
        operator_projection_case_view=case_view,
        typed_adjudication_case_view=typed_case,
        projection_exception_visibility_register=exception_register,
    )
    workbench_projection = derive_v74c_repo_ratification_review_workbench_projection(
        repo_root=repo_root,
        decision_visibility_contract=decision_contract,
    )
    handoff = derive_v74c_repo_post_projection_handoff(
        repo_root=repo_root,
        decision_visibility_contract=decision_contract,
        ratification_review_workbench_projection=workbench_projection,
    )
    family_closeout = derive_v74c_repo_operator_projection_family_closeout_alignment(
        repo_root=repo_root
    )
    validate_v74c_operator_projection_bundle(
        operator_projection_source_index=source_index,
        operator_projection_case_view=case_view,
        typed_adjudication_case_view=typed_case,
        projection_exception_visibility_register=exception_register,
        decision_visibility_contract=decision_contract,
        ratification_review_workbench_projection=workbench_projection,
        post_projection_handoff=handoff,
        operator_projection_family_closeout_alignment=family_closeout,
    )
    return (
        source_index,
        case_view,
        guardrail,
        typed_case,
        comparison_projection,
        exception_register,
        decision_contract,
        workbench_projection,
        handoff,
        family_closeout,
    )
