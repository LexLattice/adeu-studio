from __future__ import annotations

from pathlib import Path
from typing import Literal

from pydantic import Field, model_validator

from .arc_series_cartography import (
    NamespaceKind,
    SourceStatus,
    _CartographyBase,
    _non_empty,
    _repo_ref,
    _sorted_unique,
    _sorted_unique_by_ref,
)
from .candidate_review_classification import _load_json, _surface_id
from .contained_integration_review import (
    RepoCommitReleaseAuthorityPosture,
    RepoContainedIntegrationFamilyCloseoutAlignment,
    RepoContainedIntegrationTrialRecord,
    RepoIntegrationEffectSurfaceRegister,
    RepoIntegrationRollbackReadiness,
    RepoPostIntegrationOutcomeReviewHandoff,
)
from .recursive_candidate_intake import (
    CandidateAuthorityLayer,
    CandidateSourceKind,
    CandidateSourcePresencePosture,
    OdeuLane,
)

REPO_CANDIDATE_OUTCOME_REVIEW_ENTRY_SCHEMA = "repo_candidate_outcome_review_entry@1"
REPO_OUTCOME_EVIDENCE_SOURCE_INDEX_SCHEMA = "repo_outcome_evidence_source_index@1"
REPO_OUTCOME_REVIEW_BOUNDARY_GUARDRAIL_SCHEMA = "repo_outcome_review_boundary_guardrail@1"
REPO_CANDIDATE_OUTCOME_OBSERVATION_RECORD_SCHEMA = "repo_candidate_outcome_observation_record@1"
REPO_OUTCOME_REGRESSION_REGISTER_SCHEMA = "repo_outcome_regression_register@1"
REPO_TOOL_FITNESS_DRIFT_REGISTER_SCHEMA = "repo_tool_fitness_drift_register@1"
REPO_SELF_IMPROVEMENT_OUTCOME_LEDGER_SCHEMA = "repo_self_improvement_outcome_ledger@1"
REPO_OPERATOR_COGNITION_OUTCOME_SIGNAL_SCHEMA = "repo_operator_cognition_outcome_signal@1"
REPO_OUTCOME_PROMOTION_DEMOTION_RECOMMENDATION_SCHEMA = (
    "repo_outcome_promotion_demotion_recommendation@1"
)
REPO_OUTCOME_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA = (
    "repo_outcome_review_family_closeout_alignment@1"
)

OutcomeReviewEntryPosture = Literal[
    "eligible_for_outcome_review",
    "blocked_by_missing_trial_evidence",
    "blocked_by_rollback_gap",
    "blocked_by_effect_gap",
    "blocked_by_authority_boundary",
    "future_family_only",
    "rejected_out_of_scope",
]
OutcomeEvidenceKind = Literal[
    "baseline_evidence",
    "intervention_evidence",
    "evaluation_evidence",
    "trial_evidence",
    "effect_evidence",
    "rollback_evidence",
    "authority_posture_evidence",
    "dogfood_evidence",
    "operator_cognition_evidence",
    "tool_run_evidence",
    "absence_evidence",
]
OutcomeEvidenceRole = Literal[
    "primary_outcome_evidence",
    "auxiliary_trial_context",
    "auxiliary_effect_context",
    "auxiliary_rollback_context",
    "authority_boundary_context",
    "absence_marker",
]
OutcomeHorizonKind = Literal["baseline", "intervention", "evaluation"]
OutcomeHorizonCoveragePosture = Literal[
    "covered",
    "partially_covered",
    "missing_expected_source",
    "not_applicable",
    "future_family_only",
]
OutcomeReviewBoundaryPosture = Literal[
    "no_promotion_authority",
    "no_demotion_authority",
    "no_release_authority",
    "no_product_authorization",
    "no_runtime_permission",
    "no_dispatch_authority",
    "no_external_contest_authority",
]
OutcomeForbiddenDownstreamRole = Literal[
    "promotion_authority",
    "demotion_authority",
    "adoption_authority",
    "commit_release_authority",
    "merge_authority",
    "released_truth",
    "product_authorization",
    "runtime_permission",
    "dispatch_authority",
    "external_contest_authority",
]
OutcomeRequiredLaterAuthority = Literal[
    "human_ratification_required",
    "maintainer_release_authority_required",
    "product_authority_required",
    "runtime_authority_required",
    "dispatch_authority_required",
    "external_contest_authority_required",
    "none_selected_here",
]
OutcomeObservationPosture = Literal[
    "benefit_observed",
    "harm_observed",
    "neutral_or_no_material_change",
    "mixed_outcome_observed",
    "inconclusive_outcome",
    "outcome_blocked_by_missing_evidence",
    "outcome_deferred_to_future_family",
]
OutcomeConfidencePosture = Literal[
    "high_with_bounded_evidence",
    "moderate_with_limitations",
    "low_or_inconclusive",
    "blocked_by_missing_baseline",
    "blocked_by_missing_evaluation",
    "blocked_by_unchecked_regression",
    "not_applicable",
]
OutcomeRegressionPosture = Literal[
    "no_regression_observed",
    "regression_observed",
    "regression_risk_detected",
    "regression_unknown",
    "regression_not_applicable",
]
OutcomeRegressionSurfaceKind = Literal[
    "docs_regression",
    "schema_regression",
    "validator_regression",
    "fixture_regression",
    "test_regression",
    "workflow_regression",
    "tool_applicability_regression",
    "operator_cognition_regression",
    "unknown_or_unchecked_surface",
]
ToolFitnessPosture = Literal[
    "tool_fit_confirmed",
    "tool_fit_limited",
    "tool_fit_stale",
    "tool_fit_misleading",
    "tool_fit_unchecked",
    "tool_fit_not_applicable",
]
OutcomeLedgerPosture = Literal[
    "positive_signal_recorded",
    "negative_signal_recorded",
    "mixed_signal_recorded",
    "inconclusive_signal_recorded",
    "deferred_signal_recorded",
    "out_of_scope_signal_recorded",
]
OperatorCognitionSignalKind = Literal[
    "operator_conceptual_state_changed",
    "workflow_generated_new_task",
    "workflow_exposed_missing_type",
    "reviewer_decision_pressure_changed",
    "no_operator_signal_recorded",
]
OperatorCognitionSignalPosture = Literal[
    "signal_recorded_for_review",
    "signal_requires_later_projection",
    "signal_inconclusive",
    "signal_not_authority",
    "signal_not_applicable",
]
OutcomeRecommendationPosture = Literal[
    "recommend_promote_for_later_review",
    "recommend_demote_or_revert_for_later_review",
    "recommend_repeat_trial",
    "recommend_more_evidence",
    "recommend_future_family_review",
    "recommend_no_action",
    "recommend_reject_out_of_scope",
]
OutcomeRecommendationNextSurface = Literal[
    "v74_operator_projection_review",
    "v72_repeat_trial_review",
    "future_ratification_or_policy_review",
    "future_family_review",
    "deferred_no_selection",
]
OutcomeRecommendationLaterAuthority = Literal[
    "human_ratification_required",
    "maintainer_release_authority_required",
    "product_authority_required",
    "dispatch_authority_required",
    "none_for_no_action",
]
OutcomeFamilyCloseoutPosture = Literal[
    "family_closed_review_machinery_only",
    "family_closeout_deferred_by_gap",
    "family_closeout_blocked",
]

_V72B_TRIAL_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus201/"
    "repo_contained_integration_trial_record_v201_reference.json"
)
_V72B_EFFECT_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus201/"
    "repo_integration_effect_surface_register_v201_reference.json"
)
_V72B_ROLLBACK_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus201/"
    "repo_integration_rollback_readiness_v201_reference.json"
)
_V72C_AUTHORITY_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus202/"
    "repo_commit_release_authority_posture_v202_reference.json"
)
_V72C_HANDOFF_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus202/"
    "repo_post_integration_outcome_review_handoff_v202_reference.json"
)
_V72C_CLOSEOUT_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus202/"
    "repo_contained_integration_family_closeout_alignment_v202_reference.json"
)
_V73A_SOURCE_INDEX_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus203/"
    "repo_outcome_evidence_source_index_v203_reference.json"
)
_V73A_ENTRY_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus203/"
    "repo_candidate_outcome_review_entry_v203_reference.json"
)
_V73A_GUARDRAIL_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus203/"
    "repo_outcome_review_boundary_guardrail_v203_reference.json"
)
_V73B_OBSERVATION_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus204/"
    "repo_candidate_outcome_observation_record_v204_reference.json"
)
_V73B_REGRESSION_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus204/"
    "repo_outcome_regression_register_v204_reference.json"
)
_V73B_TOOL_FITNESS_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus204/"
    "repo_tool_fitness_drift_register_v204_reference.json"
)

_V73A_FORBIDDEN_OUTCOME_TERMS = (
    "benefit observed",
    "harm observed",
    "outcome success",
    "outcome succeeded",
    "regression observed",
    "no regression observed",
    "tool fit confirmed",
    "tool fit misleading",
    "promotion recommended",
    "demotion recommended",
    "promote",
    "demote",
    "adopted",
    "self approval",
    "self-approval",
    "release authorized",
    "released truth",
    "product authorized",
    "runtime authorized",
    "dispatch authorized",
)
_V73A_FORBIDDEN_ROLE_SET: set[OutcomeForbiddenDownstreamRole] = {
    "promotion_authority",
    "demotion_authority",
    "adoption_authority",
    "commit_release_authority",
    "merge_authority",
    "released_truth",
    "product_authorization",
    "runtime_permission",
    "dispatch_authority",
    "external_contest_authority",
}
_V73A_NON_JUDGMENT_SUMMARY = (
    "Outcome review entry is review-only: no benefit judgment, no harm judgment, "
    "no regression verdict, no tool-fitness verdict, no promotion, no demotion, "
    "no adoption, no release, no product authorization, no runtime permission, "
    "and no dispatch authority."
)
_V73A_BOUNDARY_SUMMARY = (
    "Boundary guardrails forbid promotion, demotion, adoption, commit, merge, "
    "release, released truth, product authorization, runtime permission, "
    "dispatch authority, and external contest authority."
)
_V73B_FORBIDDEN_AUTHORITY_TERMS = (
    "promotion recommended",
    "demotion recommended",
    "promote",
    "demote",
    "adopted",
    "adoption authorized",
    "release authorized",
    "released truth",
    "product authorized",
    "runtime authorized",
    "dispatch authorized",
    "external contest authorized",
    "implementation priority",
    "implement next",
    "global applicability",
    "globally applicable",
    "global deprecation",
    "deprecate globally",
)
_V73B_NON_AUTHORITY_SUMMARY = (
    "Outcome observation is bounded evidence for later review only: no promotion, "
    "no demotion, no adoption, no release, no product authorization, no runtime "
    "permission, no dispatch authority, and no external contest authority."
)
_V73B_NON_IMPLEMENTATION_SUMMARY = (
    "Regression rows are review evidence only: no implementation priority, no "
    "promotion, no demotion, no adoption, no release, no product authorization, "
    "no runtime permission, and no dispatch authority."
)
_V73B_TOOL_TARGET_BOUND_SUMMARY = (
    "Tool-fitness drift is target-bound evidence only: no global tool "
    "applicability, no global deprecation, no promotion, no adoption, no release, "
    "no product authorization, no runtime permission, and no dispatch authority."
)
_V73C_FORBIDDEN_AUTHORITY_TERMS = (
    "adopted",
    "adoption authorized",
    "release authorized",
    "released truth",
    "product authorized",
    "product work authorized",
    "runtime authorized",
    "dispatch authorized",
    "dispatch selected",
    "external contest authorized",
    "automatic revert",
    "multi-worker execution",
)
_V73C_LEDGER_SUMMARY = (
    "Self-improvement outcome ledger is review memory only: no self-approval, "
    "no adoption, no release, no product authorization, no runtime permission, "
    "no dispatch authority, and no external contest authority."
)
_V73C_OPERATOR_NON_AUTHORITY_SUMMARY = (
    "Operator-cognition outcome signal is evidence for later review only: "
    "no transcript truth, no lock authority, no release authority, no product "
    "authority, no runtime permission, and no dispatch authority."
)
_V73C_RECOMMENDATION_BOUNDARY_SUMMARY = (
    "Outcome recommendation separates posture, next review surface, and later "
    "authority: no adoption, no release, no automatic revert, no product work, "
    "no runtime permission, no dispatch selection, and no self-approval."
)
_V73C_FAMILY_CLOSEOUT_SUMMARY = (
    "V73 family closeout alignment closes review machinery only: no self-approval, "
    "no adoption, no release, no product authorization, no runtime permission, "
    "no dispatch authority, and no external contest authority."
)
_V73_SURFACE_SET = {
    REPO_CANDIDATE_OUTCOME_REVIEW_ENTRY_SCHEMA,
    REPO_OUTCOME_EVIDENCE_SOURCE_INDEX_SCHEMA,
    REPO_OUTCOME_REVIEW_BOUNDARY_GUARDRAIL_SCHEMA,
    REPO_CANDIDATE_OUTCOME_OBSERVATION_RECORD_SCHEMA,
    REPO_OUTCOME_REGRESSION_REGISTER_SCHEMA,
    REPO_TOOL_FITNESS_DRIFT_REGISTER_SCHEMA,
    REPO_SELF_IMPROVEMENT_OUTCOME_LEDGER_SCHEMA,
    REPO_OPERATOR_COGNITION_OUTCOME_SIGNAL_SCHEMA,
    REPO_OUTCOME_PROMOTION_DEMOTION_RECOMMENDATION_SCHEMA,
    REPO_OUTCOME_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
}


def _v73a_note(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    lowered = normalized.lower()
    if any(term in lowered for term in _V73A_FORBIDDEN_OUTCOME_TERMS):
        raise ValueError(f"{field_name} may not carry outcome judgment or downstream authority")
    return normalized


def _v73a_non_judgment_summary(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    lowered = normalized.lower()
    required = (
        "no benefit judgment",
        "no harm judgment",
        "no regression verdict",
        "no tool-fitness verdict",
        "no promotion",
        "no demotion",
        "no adoption",
        "no release",
        "no product",
        "no runtime",
        "no dispatch",
    )
    missing = [phrase for phrase in required if phrase not in lowered]
    if missing:
        raise ValueError(f"{field_name} must state {', '.join(missing)}")
    if any(term in lowered for term in ("release authorized", "dispatch authorized")):
        raise ValueError(f"{field_name} may not authorize downstream action")
    return normalized


def _v73a_boundary_summary(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    lowered = normalized.lower()
    required = (
        "forbid promotion",
        "demotion",
        "adoption",
        "commit",
        "merge",
        "release",
        "released truth",
        "product",
        "runtime",
        "dispatch",
        "external contest",
    )
    missing = [phrase for phrase in required if phrase not in lowered]
    if missing:
        raise ValueError(f"{field_name} must state {', '.join(missing)}")
    if any(term in lowered for term in ("release authorized", "dispatch authorized")):
        raise ValueError(f"{field_name} may not authorize downstream action")
    return normalized


def _v73b_note(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    lowered = normalized.lower()
    if any(term in lowered for term in _V73B_FORBIDDEN_AUTHORITY_TERMS):
        raise ValueError(f"{field_name} may not carry downstream authority or global policy")
    return normalized


def _v73b_required_summary(value: str, *, field_name: str, required: tuple[str, ...]) -> str:
    normalized = _non_empty(value, field_name=field_name)
    lowered = normalized.lower()
    missing = [phrase for phrase in required if phrase not in lowered]
    if missing:
        raise ValueError(f"{field_name} must state {', '.join(missing)}")
    if any(
        term in lowered
        for term in ("release authorized", "dispatch authorized", "product authorized")
    ):
        raise ValueError(f"{field_name} may not authorize downstream action or global policy")
    if "global applicability" in lowered and "no global tool applicability" not in lowered:
        raise ValueError(f"{field_name} may not authorize downstream action or global policy")
    if "global deprecation" in lowered and "no global deprecation" not in lowered:
        raise ValueError(f"{field_name} may not authorize downstream action or global policy")
    return normalized


def _v73c_note(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    lowered = normalized.lower()
    forbidden_terms = [
        term
        for term in _V73C_FORBIDDEN_AUTHORITY_TERMS
        if not (term == "automatic revert" and "no automatic revert" in lowered)
    ]
    if any(term in lowered for term in forbidden_terms):
        raise ValueError(f"{field_name} may not carry downstream authority or self-approval")
    if "self approval" in lowered and "no self approval" not in lowered:
        raise ValueError(f"{field_name} may not carry downstream authority or self-approval")
    if "self-approval" in lowered and "no self-approval" not in lowered:
        raise ValueError(f"{field_name} may not carry downstream authority or self-approval")
    if "transcript truth" in lowered and "no transcript truth" not in lowered:
        raise ValueError(f"{field_name} may not treat transcript as truth")
    if "lock authority" in lowered and "no lock authority" not in lowered:
        raise ValueError(f"{field_name} may not carry lock authority")
    return normalized


def _v73c_required_summary(value: str, *, field_name: str, required: tuple[str, ...]) -> str:
    normalized = _v73c_note(value, field_name=field_name)
    lowered = normalized.lower()
    missing = [phrase for phrase in required if phrase not in lowered]
    if missing:
        raise ValueError(f"{field_name} must state {', '.join(missing)}")
    return normalized


class RepoOutcomeEvidenceSourceRow(_CartographyBase):
    source_ref: str
    candidate_ref: str
    source_kind: CandidateSourceKind
    authority_layer: CandidateAuthorityLayer
    source_status: SourceStatus
    source_presence_posture: CandidateSourcePresencePosture
    outcome_evidence_kind: OutcomeEvidenceKind
    horizon_refs: list[str] = Field(min_length=1)
    evidence_role: OutcomeEvidenceRole
    limitation_note: str

    @model_validator(mode="after")
    def _validate_source_row(self) -> RepoOutcomeEvidenceSourceRow:
        object.__setattr__(self, "source_ref", _repo_ref(self.source_ref, field_name="source_ref"))
        object.__setattr__(
            self, "candidate_ref", _non_empty(self.candidate_ref, field_name="candidate_ref")
        )
        object.__setattr__(
            self, "horizon_refs", _sorted_unique(self.horizon_refs, field_name="horizon_refs")
        )
        object.__setattr__(
            self,
            "limitation_note",
            _v73a_note(self.limitation_note, field_name="limitation_note"),
        )
        if (
            self.source_status == "integrated_shaping_source"
            and self.source_presence_posture != "present"
        ):
            raise ValueError("integrated outcome sources must have presence posture present")
        if self.source_presence_posture != "present" and self.evidence_role != "absence_marker":
            raise ValueError("missing outcome sources must use absence_marker evidence role")
        if (
            self.outcome_evidence_kind == "absence_evidence"
            and self.evidence_role != "absence_marker"
        ):
            raise ValueError("absence evidence must use absence_marker evidence role")
        if (
            self.outcome_evidence_kind
            in {
                "trial_evidence",
                "effect_evidence",
                "rollback_evidence",
                "authority_posture_evidence",
            }
            and self.evidence_role == "primary_outcome_evidence"
        ):
            raise ValueError("context evidence cannot be primary outcome evidence in V73-A")
        return self


class RepoOutcomeHorizonRow(_CartographyBase):
    horizon_ref: str
    candidate_ref: str
    horizon_kind: OutcomeHorizonKind
    covered_surface_refs: list[str] = Field(default_factory=list)
    source_refs: list[str] = Field(default_factory=list)
    coverage_posture: OutcomeHorizonCoveragePosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_horizon_row(self) -> RepoOutcomeHorizonRow:
        object.__setattr__(
            self, "horizon_ref", _non_empty(self.horizon_ref, field_name="horizon_ref")
        )
        object.__setattr__(
            self, "candidate_ref", _non_empty(self.candidate_ref, field_name="candidate_ref")
        )
        object.__setattr__(
            self,
            "covered_surface_refs",
            sorted(
                _repo_ref(value, field_name="covered_surface_refs")
                for value in self.covered_surface_refs
            ),
        )
        if len(set(self.covered_surface_refs)) != len(self.covered_surface_refs):
            raise ValueError("covered_surface_refs values must be unique")
        object.__setattr__(
            self, "source_refs", _sorted_unique(self.source_refs, field_name="source_refs")
        )
        object.__setattr__(
            self,
            "limitation_note",
            _v73a_note(self.limitation_note, field_name="limitation_note"),
        )
        if self.coverage_posture in {"covered", "partially_covered"} and not self.source_refs:
            raise ValueError("covered outcome horizons require source refs")
        if self.coverage_posture == "missing_expected_source" and not self.source_refs:
            raise ValueError("missing outcome horizons require absence evidence source refs")
        if self.coverage_posture == "future_family_only" and self.horizon_kind != "evaluation":
            raise ValueError("future-family-only horizon posture is only allowed for evaluation")
        return self


class RepoOutcomeEvidenceSourceIndex(_CartographyBase):
    schema: Literal["repo_outcome_evidence_source_index@1"] = (
        REPO_OUTCOME_EVIDENCE_SOURCE_INDEX_SCHEMA
    )
    evidence_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    post_integration_handoff_id: str
    trial_record_id: str
    effect_surface_register_id: str
    rollback_readiness_id: str
    authority_posture_id: str
    source_rows: list[RepoOutcomeEvidenceSourceRow] = Field(min_length=1)
    outcome_horizon_rows: list[RepoOutcomeHorizonRow] = Field(min_length=1)
    non_judgment_summary: str

    @model_validator(mode="after")
    def _validate_source_index(self) -> RepoOutcomeEvidenceSourceIndex:
        for field_name in (
            "evidence_source_index_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "post_integration_handoff_id",
            "trial_record_id",
            "effect_surface_register_id",
            "rollback_readiness_id",
            "authority_posture_id",
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
            "outcome_horizon_rows",
            _sorted_unique_by_ref(
                self.outcome_horizon_rows,
                attr="horizon_ref",
                field_name="outcome_horizon_rows",
            ),
        )
        object.__setattr__(
            self,
            "non_judgment_summary",
            _v73a_non_judgment_summary(
                self.non_judgment_summary, field_name="non_judgment_summary"
            ),
        )
        known_horizons = {row.horizon_ref for row in self.outcome_horizon_rows}
        known_sources = {row.source_ref for row in self.source_rows}
        for source in self.source_rows:
            missing_horizons = sorted(set(source.horizon_refs) - known_horizons)
            if missing_horizons:
                raise ValueError(
                    f"source rows must reference known outcome horizons: {missing_horizons}"
                )
        for horizon in self.outcome_horizon_rows:
            missing_sources = sorted(set(horizon.source_refs) - known_sources)
            if missing_sources:
                raise ValueError(
                    f"horizon rows must reference known outcome sources: {missing_sources}"
                )
            if horizon.coverage_posture == "missing_expected_source" and not any(
                source.outcome_evidence_kind == "absence_evidence"
                and source.evidence_role == "absence_marker"
                for source in self.source_rows
                if source.source_ref in horizon.source_refs
            ):
                raise ValueError("missing horizons require absence evidence source rows")
        expected_id = _surface_id(
            "repo_outcome_evidence_source_index",
            REPO_OUTCOME_EVIDENCE_SOURCE_INDEX_SCHEMA,
            self.model_dump(mode="json"),
            "evidence_source_index_id",
        )
        if self.evidence_source_index_id != expected_id:
            raise ValueError(
                "evidence_source_index_id must match canonical full payload hash identity"
            )
        return self


class RepoCandidateOutcomeReviewEntryRow(_CartographyBase):
    entry_ref: str
    candidate_ref: str
    source_handoff_refs: list[str] = Field(default_factory=list)
    trial_refs: list[str] = Field(default_factory=list)
    effect_refs: list[str] = Field(default_factory=list)
    rollback_refs: list[str] = Field(default_factory=list)
    authority_posture_refs: list[str] = Field(default_factory=list)
    outcome_source_refs: list[str] = Field(default_factory=list)
    baseline_horizon_ref: str
    intervention_horizon_ref: str
    evaluation_horizon_ref: str
    blocking_trial_gap_refs: list[str] = Field(default_factory=list)
    blocking_effect_gap_refs: list[str] = Field(default_factory=list)
    blocking_rollback_gap_refs: list[str] = Field(default_factory=list)
    blocking_authority_boundary_refs: list[str] = Field(default_factory=list)
    entry_posture: OutcomeReviewEntryPosture
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    guardrail_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_entry_row(self) -> RepoCandidateOutcomeReviewEntryRow:
        object.__setattr__(self, "entry_ref", _non_empty(self.entry_ref, field_name="entry_ref"))
        object.__setattr__(
            self, "candidate_ref", _non_empty(self.candidate_ref, field_name="candidate_ref")
        )
        for field_name in (
            "source_handoff_refs",
            "trial_refs",
            "effect_refs",
            "rollback_refs",
            "authority_posture_refs",
            "outcome_source_refs",
            "blocking_trial_gap_refs",
            "blocking_effect_gap_refs",
            "blocking_rollback_gap_refs",
            "blocking_authority_boundary_refs",
            "guardrail_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for field_name in (
            "baseline_horizon_ref",
            "intervention_horizon_ref",
            "evaluation_horizon_ref",
        ):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        object.__setattr__(
            self, "odeu_lanes", _sorted_unique(self.odeu_lanes, field_name="odeu_lanes")
        )
        object.__setattr__(
            self,
            "limitation_note",
            _v73a_note(self.limitation_note, field_name="limitation_note"),
        )
        if self.entry_posture == "eligible_for_outcome_review":
            missing_fields = [
                field_name
                for field_name, values in (
                    ("source_handoff_refs", self.source_handoff_refs),
                    ("trial_refs", self.trial_refs),
                    ("effect_refs", self.effect_refs),
                    ("rollback_refs", self.rollback_refs),
                    ("authority_posture_refs", self.authority_posture_refs),
                    ("outcome_source_refs", self.outcome_source_refs),
                    ("guardrail_refs", self.guardrail_refs),
                )
                if not values
            ]
            if missing_fields:
                raise ValueError(f"eligible outcome-review entries require {missing_fields}")
            if any(
                (
                    self.blocking_trial_gap_refs,
                    self.blocking_effect_gap_refs,
                    self.blocking_rollback_gap_refs,
                    self.blocking_authority_boundary_refs,
                )
            ):
                raise ValueError("eligible outcome-review entries cannot carry blocking refs")
            if self.candidate_ref in {
                "candidate:internal:odeu_conceptual_diff_report@1",
                "candidate:internal:typed_adjudication_product_wedge",
            }:
                raise ValueError("blocked or product candidates cannot be outcome-ready in V73-A")
        required_blocker_fields = {
            "blocked_by_missing_trial_evidence": (
                "blocking_trial_gap_refs",
                self.blocking_trial_gap_refs,
            ),
            "blocked_by_effect_gap": ("blocking_effect_gap_refs", self.blocking_effect_gap_refs),
            "blocked_by_rollback_gap": (
                "blocking_rollback_gap_refs",
                self.blocking_rollback_gap_refs,
            ),
            "blocked_by_authority_boundary": (
                "blocking_authority_boundary_refs",
                self.blocking_authority_boundary_refs,
            ),
        }
        if self.entry_posture in required_blocker_fields:
            field_name, values = required_blocker_fields[self.entry_posture]
            if not values:
                raise ValueError(f"{self.entry_posture} requires {field_name}")
        if self.entry_posture == "future_family_only" and (
            self.trial_refs or self.effect_refs or self.rollback_refs
        ):
            raise ValueError("future-family-only entries cannot carry trial/effect/rollback refs")
        if not self.guardrail_refs:
            raise ValueError("outcome-review entries require guardrail refs")
        return self


class RepoCandidateOutcomeReviewEntry(_CartographyBase):
    schema: Literal["repo_candidate_outcome_review_entry@1"] = (
        REPO_CANDIDATE_OUTCOME_REVIEW_ENTRY_SCHEMA
    )
    outcome_review_entry_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    post_integration_handoff_id: str
    evidence_source_index_id: str
    entry_rows: list[RepoCandidateOutcomeReviewEntryRow] = Field(min_length=1)
    non_judgment_summary: str

    @model_validator(mode="after")
    def _validate_entry(self) -> RepoCandidateOutcomeReviewEntry:
        for field_name in (
            "outcome_review_entry_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "post_integration_handoff_id",
            "evidence_source_index_id",
        ):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        object.__setattr__(
            self,
            "entry_rows",
            _sorted_unique_by_ref(self.entry_rows, attr="entry_ref", field_name="entry_rows"),
        )
        object.__setattr__(
            self,
            "non_judgment_summary",
            _v73a_non_judgment_summary(
                self.non_judgment_summary, field_name="non_judgment_summary"
            ),
        )
        expected_id = _surface_id(
            "repo_candidate_outcome_review_entry",
            REPO_CANDIDATE_OUTCOME_REVIEW_ENTRY_SCHEMA,
            self.model_dump(mode="json"),
            "outcome_review_entry_id",
        )
        if self.outcome_review_entry_id != expected_id:
            raise ValueError(
                "outcome_review_entry_id must match canonical full payload hash identity"
            )
        return self


class RepoOutcomeReviewBoundaryGuardrailRow(_CartographyBase):
    guardrail_ref: str
    candidate_ref: str
    entry_refs: list[str] = Field(min_length=1)
    forbidden_downstream_roles: list[OutcomeForbiddenDownstreamRole] = Field(min_length=1)
    boundary_posture: list[OutcomeReviewBoundaryPosture] = Field(min_length=1)
    required_later_authority: list[OutcomeRequiredLaterAuthority] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_guardrail_row(self) -> RepoOutcomeReviewBoundaryGuardrailRow:
        object.__setattr__(
            self, "guardrail_ref", _non_empty(self.guardrail_ref, field_name="guardrail_ref")
        )
        object.__setattr__(
            self, "candidate_ref", _non_empty(self.candidate_ref, field_name="candidate_ref")
        )
        object.__setattr__(
            self, "entry_refs", _sorted_unique(self.entry_refs, field_name="entry_refs")
        )
        object.__setattr__(
            self,
            "forbidden_downstream_roles",
            _sorted_unique(
                self.forbidden_downstream_roles,
                field_name="forbidden_downstream_roles",
            ),
        )
        object.__setattr__(
            self,
            "boundary_posture",
            _sorted_unique(self.boundary_posture, field_name="boundary_posture"),
        )
        object.__setattr__(
            self,
            "required_later_authority",
            _sorted_unique(
                self.required_later_authority,
                field_name="required_later_authority",
            ),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _v73a_note(self.limitation_note, field_name="limitation_note"),
        )
        missing_roles = sorted(_V73A_FORBIDDEN_ROLE_SET - set(self.forbidden_downstream_roles))
        if missing_roles:
            raise ValueError(f"guardrails must forbid downstream roles: {missing_roles}")
        if "none_selected_here" not in self.required_later_authority:
            raise ValueError("V73-A guardrails must include none_selected_here later authority")
        return self


class RepoOutcomeReviewBoundaryGuardrail(_CartographyBase):
    schema: Literal["repo_outcome_review_boundary_guardrail@1"] = (
        REPO_OUTCOME_REVIEW_BOUNDARY_GUARDRAIL_SCHEMA
    )
    boundary_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    outcome_review_entry_id: str
    guardrail_rows: list[RepoOutcomeReviewBoundaryGuardrailRow] = Field(min_length=1)
    boundary_summary: str

    @model_validator(mode="after")
    def _validate_guardrail(self) -> RepoOutcomeReviewBoundaryGuardrail:
        for field_name in (
            "boundary_guardrail_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "outcome_review_entry_id",
        ):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        object.__setattr__(
            self,
            "guardrail_rows",
            _sorted_unique_by_ref(
                self.guardrail_rows,
                attr="guardrail_ref",
                field_name="guardrail_rows",
            ),
        )
        object.__setattr__(
            self,
            "boundary_summary",
            _v73a_boundary_summary(self.boundary_summary, field_name="boundary_summary"),
        )
        expected_id = _surface_id(
            "repo_outcome_review_boundary_guardrail",
            REPO_OUTCOME_REVIEW_BOUNDARY_GUARDRAIL_SCHEMA,
            self.model_dump(mode="json"),
            "boundary_guardrail_id",
        )
        if self.boundary_guardrail_id != expected_id:
            raise ValueError(
                "boundary_guardrail_id must match canonical full payload hash identity"
            )
        return self


class RepoCandidateOutcomeObservationRow(_CartographyBase):
    observation_ref: str
    candidate_ref: str
    entry_refs: list[str] = Field(min_length=1)
    outcome_source_refs: list[str] = Field(default_factory=list)
    baseline_refs: list[str] = Field(default_factory=list)
    intervention_refs: list[str] = Field(default_factory=list)
    evaluation_refs: list[str] = Field(default_factory=list)
    outcome_observation_posture: OutcomeObservationPosture
    confidence_posture: OutcomeConfidencePosture
    carried_forward_gap_refs: list[str] = Field(default_factory=list)
    regression_refs: list[str] = Field(default_factory=list)
    tool_fitness_refs: list[str] = Field(default_factory=list)
    non_promotion_guardrail_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_observation_row(self) -> RepoCandidateOutcomeObservationRow:
        object.__setattr__(
            self, "observation_ref", _non_empty(self.observation_ref, field_name="observation_ref")
        )
        object.__setattr__(
            self, "candidate_ref", _non_empty(self.candidate_ref, field_name="candidate_ref")
        )
        for field_name in (
            "entry_refs",
            "outcome_source_refs",
            "baseline_refs",
            "intervention_refs",
            "evaluation_refs",
            "carried_forward_gap_refs",
            "regression_refs",
            "tool_fitness_refs",
            "non_promotion_guardrail_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "limitation_note",
            _v73b_note(self.limitation_note, field_name="limitation_note"),
        )
        if self.outcome_observation_posture == "benefit_observed":
            missing_fields = [
                field_name
                for field_name, values in (
                    ("outcome_source_refs", self.outcome_source_refs),
                    ("baseline_refs", self.baseline_refs),
                    ("intervention_refs", self.intervention_refs),
                    ("evaluation_refs", self.evaluation_refs),
                    ("non_promotion_guardrail_refs", self.non_promotion_guardrail_refs),
                )
                if not values
            ]
            if missing_fields:
                raise ValueError(f"benefit observations require {missing_fields}")
        if self.outcome_observation_posture == "outcome_blocked_by_missing_evidence" and (
            self.confidence_posture
            not in {
                "blocked_by_missing_baseline",
                "blocked_by_missing_evaluation",
                "low_or_inconclusive",
            }
        ):
            raise ValueError("missing-evidence observations require blocked confidence posture")
        if self.outcome_observation_posture == "outcome_deferred_to_future_family" and (
            self.confidence_posture != "not_applicable"
        ):
            raise ValueError("future-family observations require not_applicable confidence posture")
        return self


class RepoCandidateOutcomeObservationRecord(_CartographyBase):
    schema: Literal["repo_candidate_outcome_observation_record@1"] = (
        REPO_CANDIDATE_OUTCOME_OBSERVATION_RECORD_SCHEMA
    )
    outcome_observation_record_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    outcome_review_entry_id: str
    evidence_source_index_id: str
    boundary_guardrail_id: str
    observation_rows: list[RepoCandidateOutcomeObservationRow] = Field(min_length=1)
    non_authority_summary: str

    @model_validator(mode="after")
    def _validate_observation_record(self) -> RepoCandidateOutcomeObservationRecord:
        for field_name in (
            "outcome_observation_record_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "outcome_review_entry_id",
            "evidence_source_index_id",
            "boundary_guardrail_id",
        ):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        object.__setattr__(
            self,
            "observation_rows",
            _sorted_unique_by_ref(
                self.observation_rows,
                attr="observation_ref",
                field_name="observation_rows",
            ),
        )
        object.__setattr__(
            self,
            "non_authority_summary",
            _v73b_required_summary(
                self.non_authority_summary,
                field_name="non_authority_summary",
                required=(
                    "bounded evidence",
                    "no promotion",
                    "no demotion",
                    "no adoption",
                    "no release",
                    "no product",
                    "no runtime",
                    "no dispatch",
                    "no external contest",
                ),
            ),
        )
        expected_id = _surface_id(
            "repo_candidate_outcome_observation_record",
            REPO_CANDIDATE_OUTCOME_OBSERVATION_RECORD_SCHEMA,
            self.model_dump(mode="json"),
            "outcome_observation_record_id",
        )
        if self.outcome_observation_record_id != expected_id:
            raise ValueError(
                "outcome_observation_record_id must match canonical full payload hash identity"
            )
        return self


class RepoOutcomeRegressionRow(_CartographyBase):
    regression_ref: str
    candidate_ref: str
    observation_refs: list[str] = Field(min_length=1)
    regression_posture: OutcomeRegressionPosture
    regression_surface_kind: OutcomeRegressionSurfaceKind
    checked_evaluation_refs: list[str] = Field(default_factory=list)
    negative_control_refs: list[str] = Field(default_factory=list)
    blocking_for_recommendation: bool
    limitation_note: str

    @model_validator(mode="after")
    def _validate_regression_row(self) -> RepoOutcomeRegressionRow:
        object.__setattr__(
            self, "regression_ref", _non_empty(self.regression_ref, field_name="regression_ref")
        )
        object.__setattr__(
            self, "candidate_ref", _non_empty(self.candidate_ref, field_name="candidate_ref")
        )
        for field_name in ("observation_refs", "checked_evaluation_refs", "negative_control_refs"):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "limitation_note",
            _v73b_note(self.limitation_note, field_name="limitation_note"),
        )
        if self.regression_posture == "no_regression_observed" and not (
            self.checked_evaluation_refs or self.negative_control_refs
        ):
            raise ValueError(
                "no_regression_observed requires checked evaluation refs or negative controls"
            )
        if self.regression_surface_kind == "unknown_or_unchecked_surface" and (
            self.regression_posture == "no_regression_observed"
        ):
            raise ValueError("unknown surfaces cannot claim no_regression_observed")
        return self


class RepoOutcomeRegressionRegister(_CartographyBase):
    schema: Literal["repo_outcome_regression_register@1"] = REPO_OUTCOME_REGRESSION_REGISTER_SCHEMA
    outcome_regression_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    outcome_observation_record_id: str
    regression_rows: list[RepoOutcomeRegressionRow] = Field(min_length=1)
    non_implementation_summary: str

    @model_validator(mode="after")
    def _validate_regression_register(self) -> RepoOutcomeRegressionRegister:
        for field_name in (
            "outcome_regression_register_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "outcome_observation_record_id",
        ):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        object.__setattr__(
            self,
            "regression_rows",
            _sorted_unique_by_ref(
                self.regression_rows,
                attr="regression_ref",
                field_name="regression_rows",
            ),
        )
        object.__setattr__(
            self,
            "non_implementation_summary",
            _v73b_required_summary(
                self.non_implementation_summary,
                field_name="non_implementation_summary",
                required=(
                    "review evidence",
                    "no implementation priority",
                    "no promotion",
                    "no demotion",
                    "no adoption",
                    "no release",
                    "no product",
                    "no runtime",
                    "no dispatch",
                ),
            ),
        )
        expected_id = _surface_id(
            "repo_outcome_regression_register",
            REPO_OUTCOME_REGRESSION_REGISTER_SCHEMA,
            self.model_dump(mode="json"),
            "outcome_regression_register_id",
        )
        if self.outcome_regression_register_id != expected_id:
            raise ValueError(
                "outcome_regression_register_id must match canonical full payload hash identity"
            )
        return self


class RepoToolFitnessDriftRow(_CartographyBase):
    tool_fitness_ref: str
    candidate_ref: str
    observation_refs: list[str] = Field(min_length=1)
    tool_id: str
    tool_target_claim_refs: list[str] = Field(default_factory=list)
    tool_target_horizon_refs: list[str] = Field(default_factory=list)
    target_namespace_kind: NamespaceKind
    prior_applicability_refs: list[str] = Field(default_factory=list)
    tool_fitness_posture: ToolFitnessPosture
    observed_result_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_tool_fitness_row(self) -> RepoToolFitnessDriftRow:
        for field_name in ("tool_fitness_ref", "candidate_ref", "tool_id"):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        for field_name in (
            "observation_refs",
            "tool_target_claim_refs",
            "tool_target_horizon_refs",
            "prior_applicability_refs",
            "observed_result_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "limitation_note",
            _v73b_note(self.limitation_note, field_name="limitation_note"),
        )
        if self.tool_fitness_posture in {"tool_fit_confirmed", "tool_fit_misleading"}:
            missing_fields = [
                field_name
                for field_name, values in (
                    ("tool_target_claim_refs", self.tool_target_claim_refs),
                    ("tool_target_horizon_refs", self.tool_target_horizon_refs),
                    ("prior_applicability_refs", self.prior_applicability_refs),
                    ("observed_result_refs", self.observed_result_refs),
                )
                if not values
            ]
            if missing_fields:
                raise ValueError(
                    f"{self.tool_fitness_posture} requires target-bound evidence: {missing_fields}"
                )
        return self


class RepoToolFitnessDriftRegister(_CartographyBase):
    schema: Literal["repo_tool_fitness_drift_register@1"] = REPO_TOOL_FITNESS_DRIFT_REGISTER_SCHEMA
    tool_fitness_drift_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    outcome_observation_record_id: str
    tool_fitness_rows: list[RepoToolFitnessDriftRow] = Field(min_length=1)
    target_bound_summary: str

    @model_validator(mode="after")
    def _validate_tool_fitness_register(self) -> RepoToolFitnessDriftRegister:
        for field_name in (
            "tool_fitness_drift_register_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "outcome_observation_record_id",
        ):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        object.__setattr__(
            self,
            "tool_fitness_rows",
            _sorted_unique_by_ref(
                self.tool_fitness_rows,
                attr="tool_fitness_ref",
                field_name="tool_fitness_rows",
            ),
        )
        object.__setattr__(
            self,
            "target_bound_summary",
            _v73b_required_summary(
                self.target_bound_summary,
                field_name="target_bound_summary",
                required=(
                    "target-bound evidence",
                    "no global tool applicability",
                    "no global deprecation",
                    "no promotion",
                    "no adoption",
                    "no release",
                    "no product",
                    "no runtime",
                    "no dispatch",
                ),
            ),
        )
        expected_id = _surface_id(
            "repo_tool_fitness_drift_register",
            REPO_TOOL_FITNESS_DRIFT_REGISTER_SCHEMA,
            self.model_dump(mode="json"),
            "tool_fitness_drift_register_id",
        )
        if self.tool_fitness_drift_register_id != expected_id:
            raise ValueError(
                "tool_fitness_drift_register_id must match canonical full payload hash identity"
            )
        return self


class RepoSelfImprovementOutcomeLedgerRow(_CartographyBase):
    ledger_ref: str
    candidate_ref: str
    entry_refs: list[str] = Field(min_length=1)
    observation_refs: list[str] = Field(min_length=1)
    regression_refs: list[str] = Field(default_factory=list)
    tool_fitness_refs: list[str] = Field(default_factory=list)
    operator_cognition_signal_refs: list[str] = Field(default_factory=list)
    outcome_ledger_posture: OutcomeLedgerPosture
    carried_forward_gap_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_ledger_row(self) -> RepoSelfImprovementOutcomeLedgerRow:
        object.__setattr__(
            self, "ledger_ref", _non_empty(self.ledger_ref, field_name="ledger_ref")
        )
        object.__setattr__(
            self, "candidate_ref", _non_empty(self.candidate_ref, field_name="candidate_ref")
        )
        for field_name in (
            "entry_refs",
            "observation_refs",
            "regression_refs",
            "tool_fitness_refs",
            "operator_cognition_signal_refs",
            "carried_forward_gap_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "limitation_note",
            _v73c_note(self.limitation_note, field_name="limitation_note"),
        )
        if self.outcome_ledger_posture == "positive_signal_recorded" and not (
            self.regression_refs and self.tool_fitness_refs
        ):
            raise ValueError("positive ledger signals require regression and tool-fitness refs")
        if self.outcome_ledger_posture == "out_of_scope_signal_recorded" and (
            self.regression_refs or self.tool_fitness_refs
        ):
            raise ValueError("out-of-scope ledger signals cannot carry evaluation refs")
        return self


class RepoSelfImprovementOutcomeLedger(_CartographyBase):
    schema: Literal["repo_self_improvement_outcome_ledger@1"] = (
        REPO_SELF_IMPROVEMENT_OUTCOME_LEDGER_SCHEMA
    )
    self_improvement_outcome_ledger_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    outcome_observation_record_id: str
    outcome_regression_register_id: str
    tool_fitness_drift_register_id: str
    ledger_rows: list[RepoSelfImprovementOutcomeLedgerRow] = Field(min_length=1)
    non_self_approval_summary: str

    @model_validator(mode="after")
    def _validate_ledger(self) -> RepoSelfImprovementOutcomeLedger:
        for field_name in (
            "self_improvement_outcome_ledger_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "outcome_observation_record_id",
            "outcome_regression_register_id",
            "tool_fitness_drift_register_id",
        ):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        object.__setattr__(
            self,
            "ledger_rows",
            _sorted_unique_by_ref(self.ledger_rows, attr="ledger_ref", field_name="ledger_rows"),
        )
        object.__setattr__(
            self,
            "non_self_approval_summary",
            _v73c_required_summary(
                self.non_self_approval_summary,
                field_name="non_self_approval_summary",
                required=(
                    "review memory",
                    "no self-approval",
                    "no adoption",
                    "no release",
                    "no product",
                    "no runtime",
                    "no dispatch",
                    "no external contest",
                ),
            ),
        )
        expected_id = _surface_id(
            "repo_self_improvement_outcome_ledger",
            REPO_SELF_IMPROVEMENT_OUTCOME_LEDGER_SCHEMA,
            self.model_dump(mode="json"),
            "self_improvement_outcome_ledger_id",
        )
        if self.self_improvement_outcome_ledger_id != expected_id:
            raise ValueError(
                "self_improvement_outcome_ledger_id must match canonical full payload hash identity"
            )
        return self


class RepoOperatorCognitionOutcomeSignalRow(_CartographyBase):
    operator_signal_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    signal_kind: OperatorCognitionSignalKind
    signal_posture: OperatorCognitionSignalPosture
    workflow_residue_refs: list[str] = Field(default_factory=list)
    non_authority_guardrail: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_operator_signal_row(self) -> RepoOperatorCognitionOutcomeSignalRow:
        object.__setattr__(
            self,
            "operator_signal_ref",
            _non_empty(self.operator_signal_ref, field_name="operator_signal_ref"),
        )
        object.__setattr__(
            self, "candidate_ref", _non_empty(self.candidate_ref, field_name="candidate_ref")
        )
        object.__setattr__(
            self, "source_refs", _sorted_unique(self.source_refs, field_name="source_refs")
        )
        object.__setattr__(
            self,
            "workflow_residue_refs",
            _sorted_unique(self.workflow_residue_refs, field_name="workflow_residue_refs"),
        )
        object.__setattr__(
            self,
            "non_authority_guardrail",
            _v73c_required_summary(
                self.non_authority_guardrail,
                field_name="non_authority_guardrail",
                required=(
                    "no transcript truth",
                    "no lock authority",
                    "no release",
                    "no product",
                    "no runtime",
                    "no dispatch",
                ),
            ),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _v73c_note(self.limitation_note, field_name="limitation_note"),
        )
        if self.signal_kind == "no_operator_signal_recorded" and (
            self.signal_posture != "signal_not_applicable"
        ):
            raise ValueError("no operator signal rows require signal_not_applicable posture")
        if self.signal_kind != "no_operator_signal_recorded" and (
            self.signal_posture == "signal_not_applicable"
        ):
            raise ValueError("recorded operator signal rows cannot be signal_not_applicable")
        return self


class RepoOperatorCognitionOutcomeSignal(_CartographyBase):
    schema: Literal["repo_operator_cognition_outcome_signal@1"] = (
        REPO_OPERATOR_COGNITION_OUTCOME_SIGNAL_SCHEMA
    )
    operator_cognition_outcome_signal_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    outcome_observation_record_id: str
    operator_signal_rows: list[RepoOperatorCognitionOutcomeSignalRow] = Field(min_length=1)
    non_authority_summary: str

    @model_validator(mode="after")
    def _validate_operator_signal(self) -> RepoOperatorCognitionOutcomeSignal:
        for field_name in (
            "operator_cognition_outcome_signal_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "outcome_observation_record_id",
        ):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        object.__setattr__(
            self,
            "operator_signal_rows",
            _sorted_unique_by_ref(
                self.operator_signal_rows,
                attr="operator_signal_ref",
                field_name="operator_signal_rows",
            ),
        )
        object.__setattr__(
            self,
            "non_authority_summary",
            _v73c_required_summary(
                self.non_authority_summary,
                field_name="non_authority_summary",
                required=(
                    "later review",
                    "no transcript truth",
                    "no lock authority",
                    "no release",
                    "no product",
                    "no runtime",
                    "no dispatch",
                ),
            ),
        )
        expected_id = _surface_id(
            "repo_operator_cognition_outcome_signal",
            REPO_OPERATOR_COGNITION_OUTCOME_SIGNAL_SCHEMA,
            self.model_dump(mode="json"),
            "operator_cognition_outcome_signal_id",
        )
        if self.operator_cognition_outcome_signal_id != expected_id:
            raise ValueError(
                "operator_cognition_outcome_signal_id must match canonical full payload "
                "hash identity"
            )
        return self


class RepoOutcomePromotionDemotionRecommendationRow(_CartographyBase):
    recommendation_ref: str
    candidate_ref: str
    ledger_refs: list[str] = Field(min_length=1)
    observation_refs: list[str] = Field(default_factory=list)
    regression_refs: list[str] = Field(default_factory=list)
    tool_fitness_refs: list[str] = Field(default_factory=list)
    operator_signal_refs: list[str] = Field(default_factory=list)
    recommendation_posture: OutcomeRecommendationPosture
    required_next_surface: OutcomeRecommendationNextSurface
    required_later_authority: OutcomeRecommendationLaterAuthority
    forbidden_downstream_roles: list[OutcomeForbiddenDownstreamRole] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_recommendation_row(self) -> RepoOutcomePromotionDemotionRecommendationRow:
        object.__setattr__(
            self,
            "recommendation_ref",
            _non_empty(self.recommendation_ref, field_name="recommendation_ref"),
        )
        object.__setattr__(
            self, "candidate_ref", _non_empty(self.candidate_ref, field_name="candidate_ref")
        )
        for field_name in (
            "ledger_refs",
            "observation_refs",
            "regression_refs",
            "tool_fitness_refs",
            "operator_signal_refs",
            "forbidden_downstream_roles",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "limitation_note",
            _v73c_note(self.limitation_note, field_name="limitation_note"),
        )
        missing_roles = sorted(_V73A_FORBIDDEN_ROLE_SET - set(self.forbidden_downstream_roles))
        if missing_roles:
            raise ValueError(f"recommendations must forbid downstream roles: {missing_roles}")
        if (
            self.recommendation_posture == "recommend_promote_for_later_review"
            and self.required_later_authority == "none_for_no_action"
        ):
            raise ValueError("promotion recommendations require later authority posture")
        if (
            self.recommendation_posture == "recommend_demote_or_revert_for_later_review"
            and self.required_later_authority == "none_for_no_action"
        ):
            raise ValueError("demotion recommendations require later authority posture")
        if (
            self.recommendation_posture == "recommend_no_action"
            and self.required_later_authority != "none_for_no_action"
        ):
            raise ValueError("no-action recommendations require none_for_no_action authority")
        if (
            self.required_later_authority == "product_authority_required"
            and self.required_next_surface != "v74_operator_projection_review"
        ):
            raise ValueError("product recommendations require V74 review")
        return self


class RepoOutcomePromotionDemotionRecommendation(_CartographyBase):
    schema: Literal["repo_outcome_promotion_demotion_recommendation@1"] = (
        REPO_OUTCOME_PROMOTION_DEMOTION_RECOMMENDATION_SCHEMA
    )
    outcome_promotion_demotion_recommendation_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    self_improvement_outcome_ledger_id: str
    operator_cognition_outcome_signal_id: str
    recommendation_rows: list[RepoOutcomePromotionDemotionRecommendationRow] = Field(min_length=1)
    recommendation_boundary_summary: str

    @model_validator(mode="after")
    def _validate_recommendation(self) -> RepoOutcomePromotionDemotionRecommendation:
        for field_name in (
            "outcome_promotion_demotion_recommendation_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "self_improvement_outcome_ledger_id",
            "operator_cognition_outcome_signal_id",
        ):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        object.__setattr__(
            self,
            "recommendation_rows",
            _sorted_unique_by_ref(
                self.recommendation_rows,
                attr="recommendation_ref",
                field_name="recommendation_rows",
            ),
        )
        object.__setattr__(
            self,
            "recommendation_boundary_summary",
            _v73c_required_summary(
                self.recommendation_boundary_summary,
                field_name="recommendation_boundary_summary",
                required=(
                    "separates posture",
                    "next review surface",
                    "later authority",
                    "no adoption",
                    "no release",
                    "no automatic revert",
                    "no product work",
                    "no runtime",
                    "no dispatch selection",
                    "no self-approval",
                ),
            ),
        )
        expected_id = _surface_id(
            "repo_outcome_promotion_demotion_recommendation",
            REPO_OUTCOME_PROMOTION_DEMOTION_RECOMMENDATION_SCHEMA,
            self.model_dump(mode="json"),
            "outcome_promotion_demotion_recommendation_id",
        )
        if self.outcome_promotion_demotion_recommendation_id != expected_id:
            raise ValueError(
                "outcome_promotion_demotion_recommendation_id must match canonical full "
                "payload hash identity"
            )
        return self


class RepoOutcomeReviewFamilyCloseoutAlignmentRow(_CartographyBase):
    family_ref: str
    closed_slice_refs: list[str] = Field(min_length=1)
    emitted_surface_refs: list[str] = Field(min_length=1)
    reviewed_candidate_refs: list[str] = Field(min_length=1)
    ledger_refs: list[str] = Field(min_length=1)
    operator_signal_refs: list[str] = Field(default_factory=list)
    recommendation_refs: list[str] = Field(min_length=1)
    non_authority_guardrail_refs: list[str] = Field(min_length=1)
    future_family_refs: list[str] = Field(default_factory=list)
    closeout_alignment_posture: OutcomeFamilyCloseoutPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_family_alignment_row(self) -> RepoOutcomeReviewFamilyCloseoutAlignmentRow:
        object.__setattr__(
            self, "family_ref", _non_empty(self.family_ref, field_name="family_ref")
        )
        for field_name in (
            "closed_slice_refs",
            "emitted_surface_refs",
            "reviewed_candidate_refs",
            "ledger_refs",
            "operator_signal_refs",
            "recommendation_refs",
            "non_authority_guardrail_refs",
            "future_family_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "limitation_note",
            _v73c_note(self.limitation_note, field_name="limitation_note"),
        )
        missing_slices = sorted({"V73-A", "V73-B", "V73-C"} - set(self.closed_slice_refs))
        if missing_slices:
            raise ValueError(f"V73 closeout alignment must list closed slices: {missing_slices}")
        missing_surfaces = sorted(_V73_SURFACE_SET - set(self.emitted_surface_refs))
        if missing_surfaces:
            raise ValueError(
                f"V73 closeout alignment must list emitted surfaces: {missing_surfaces}"
            )
        if self.closeout_alignment_posture == "family_closed_review_machinery_only" and (
            "V74" not in self.future_family_refs
        ):
            raise ValueError("V73 closeout alignment must carry V74 as a future family ref")
        return self


class RepoOutcomeReviewFamilyCloseoutAlignment(_CartographyBase):
    schema: Literal["repo_outcome_review_family_closeout_alignment@1"] = (
        REPO_OUTCOME_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
    )
    outcome_review_family_closeout_alignment_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    self_improvement_outcome_ledger_id: str
    outcome_promotion_demotion_recommendation_id: str
    alignment_rows: list[RepoOutcomeReviewFamilyCloseoutAlignmentRow] = Field(min_length=1)
    family_closeout_boundary_summary: str

    @model_validator(mode="after")
    def _validate_family_alignment(self) -> RepoOutcomeReviewFamilyCloseoutAlignment:
        for field_name in (
            "outcome_review_family_closeout_alignment_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "self_improvement_outcome_ledger_id",
            "outcome_promotion_demotion_recommendation_id",
        ):
            object.__setattr__(
                self, field_name, _non_empty(getattr(self, field_name), field_name=field_name)
            )
        object.__setattr__(
            self,
            "alignment_rows",
            _sorted_unique_by_ref(
                self.alignment_rows,
                attr="family_ref",
                field_name="alignment_rows",
            ),
        )
        object.__setattr__(
            self,
            "family_closeout_boundary_summary",
            _v73c_required_summary(
                self.family_closeout_boundary_summary,
                field_name="family_closeout_boundary_summary",
                required=(
                    "review machinery",
                    "no self-approval",
                    "no adoption",
                    "no release",
                    "no product",
                    "no runtime",
                    "no dispatch",
                    "no external contest",
                ),
            ),
        )
        expected_id = _surface_id(
            "repo_outcome_review_family_closeout_alignment",
            REPO_OUTCOME_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            self.model_dump(mode="json"),
            "outcome_review_family_closeout_alignment_id",
        )
        if self.outcome_review_family_closeout_alignment_id != expected_id:
            raise ValueError(
                "outcome_review_family_closeout_alignment_id must match canonical full payload "
                "hash identity"
            )
        return self


def _load_v72b_trial_record(repo_root: Path) -> RepoContainedIntegrationTrialRecord:
    return RepoContainedIntegrationTrialRecord.model_validate(
        _load_json(repo_root, _V72B_TRIAL_FIXTURE)
    )


def _load_v72b_effect_surface(repo_root: Path) -> RepoIntegrationEffectSurfaceRegister:
    return RepoIntegrationEffectSurfaceRegister.model_validate(
        _load_json(repo_root, _V72B_EFFECT_FIXTURE)
    )


def _load_v72b_rollback_readiness(repo_root: Path) -> RepoIntegrationRollbackReadiness:
    return RepoIntegrationRollbackReadiness.model_validate(
        _load_json(repo_root, _V72B_ROLLBACK_FIXTURE)
    )


def _load_v72c_authority_posture(repo_root: Path) -> RepoCommitReleaseAuthorityPosture:
    return RepoCommitReleaseAuthorityPosture.model_validate(
        _load_json(repo_root, _V72C_AUTHORITY_FIXTURE)
    )


def _load_v72c_handoff(repo_root: Path) -> RepoPostIntegrationOutcomeReviewHandoff:
    return RepoPostIntegrationOutcomeReviewHandoff.model_validate(
        _load_json(repo_root, _V72C_HANDOFF_FIXTURE)
    )


def _load_v72c_closeout(repo_root: Path) -> RepoContainedIntegrationFamilyCloseoutAlignment:
    return RepoContainedIntegrationFamilyCloseoutAlignment.model_validate(
        _load_json(repo_root, _V72C_CLOSEOUT_FIXTURE)
    )


def _load_v73a_source_index(repo_root: Path) -> RepoOutcomeEvidenceSourceIndex:
    return RepoOutcomeEvidenceSourceIndex.model_validate(
        _load_json(repo_root, _V73A_SOURCE_INDEX_FIXTURE)
    )


def _load_v73a_entry(repo_root: Path) -> RepoCandidateOutcomeReviewEntry:
    return RepoCandidateOutcomeReviewEntry.model_validate(
        _load_json(repo_root, _V73A_ENTRY_FIXTURE)
    )


def _load_v73a_guardrail(repo_root: Path) -> RepoOutcomeReviewBoundaryGuardrail:
    return RepoOutcomeReviewBoundaryGuardrail.model_validate(
        _load_json(repo_root, _V73A_GUARDRAIL_FIXTURE)
    )


def _load_v73b_observation(repo_root: Path) -> RepoCandidateOutcomeObservationRecord:
    return RepoCandidateOutcomeObservationRecord.model_validate(
        _load_json(repo_root, _V73B_OBSERVATION_FIXTURE)
    )


def _load_v73b_regression(repo_root: Path) -> RepoOutcomeRegressionRegister:
    return RepoOutcomeRegressionRegister.model_validate(
        _load_json(repo_root, _V73B_REGRESSION_FIXTURE)
    )


def _load_v73b_tool_fitness(repo_root: Path) -> RepoToolFitnessDriftRegister:
    return RepoToolFitnessDriftRegister.model_validate(
        _load_json(repo_root, _V73B_TOOL_FITNESS_FIXTURE)
    )


def derive_v73a_repo_outcome_evidence_source_index(
    *,
    repo_root: Path,
    contained_integration_trial_record: RepoContainedIntegrationTrialRecord | None = None,
    integration_effect_surface_register: RepoIntegrationEffectSurfaceRegister | None = None,
    integration_rollback_readiness: RepoIntegrationRollbackReadiness | None = None,
    commit_release_authority_posture: RepoCommitReleaseAuthorityPosture | None = None,
    post_integration_outcome_review_handoff: RepoPostIntegrationOutcomeReviewHandoff | None = None,
) -> RepoOutcomeEvidenceSourceIndex:
    trial = contained_integration_trial_record or _load_v72b_trial_record(repo_root)
    effect = integration_effect_surface_register or _load_v72b_effect_surface(repo_root)
    rollback = integration_rollback_readiness or _load_v72b_rollback_readiness(repo_root)
    authority = commit_release_authority_posture or _load_v72c_authority_posture(repo_root)
    handoff = post_integration_outcome_review_handoff or _load_v72c_handoff(repo_root)
    candidate_ref = "candidate:internal:self_evidencing_workflow_type_emergence"
    baseline_ref = "horizon:v73a:self-evidencing:baseline"
    intervention_ref = "horizon:v73a:self-evidencing:intervention"
    evaluation_ref = "horizon:v73a:self-evidencing:evaluation"
    rows = [
        RepoOutcomeEvidenceSourceRow(
            source_ref=_V72B_TRIAL_FIXTURE,
            candidate_ref=candidate_ref,
            source_kind="fixture_file",
            authority_layer="fixture",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            outcome_evidence_kind="trial_evidence",
            horizon_refs=[intervention_ref],
            evidence_role="auxiliary_trial_context",
            limitation_note="Trial record is context for later outcome review only.",
        ),
        RepoOutcomeEvidenceSourceRow(
            source_ref=_V72B_EFFECT_FIXTURE,
            candidate_ref=candidate_ref,
            source_kind="fixture_file",
            authority_layer="fixture",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            outcome_evidence_kind="effect_evidence",
            horizon_refs=[evaluation_ref],
            evidence_role="auxiliary_effect_context",
            limitation_note="Effect record is context and does not judge outcome.",
        ),
        RepoOutcomeEvidenceSourceRow(
            source_ref=_V72B_ROLLBACK_FIXTURE,
            candidate_ref=candidate_ref,
            source_kind="fixture_file",
            authority_layer="fixture",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            outcome_evidence_kind="rollback_evidence",
            horizon_refs=[evaluation_ref],
            evidence_role="auxiliary_rollback_context",
            limitation_note="Rollback readiness is context and not an outcome verdict.",
        ),
        RepoOutcomeEvidenceSourceRow(
            source_ref=_V72C_AUTHORITY_FIXTURE,
            candidate_ref=candidate_ref,
            source_kind="fixture_file",
            authority_layer="fixture",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            outcome_evidence_kind="authority_posture_evidence",
            horizon_refs=[evaluation_ref],
            evidence_role="authority_boundary_context",
            limitation_note="Authority posture is boundary context for later review.",
        ),
        RepoOutcomeEvidenceSourceRow(
            source_ref=_V72C_HANDOFF_FIXTURE,
            candidate_ref=candidate_ref,
            source_kind="fixture_file",
            authority_layer="fixture",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            outcome_evidence_kind="intervention_evidence",
            horizon_refs=[intervention_ref],
            evidence_role="primary_outcome_evidence",
            limitation_note="Handoff identifies the bounded later outcome-review entry.",
        ),
        RepoOutcomeEvidenceSourceRow(
            source_ref=(
                "docs/support/arc_series_mapping/V68_V69_V70_V71_V72_COMBINED_DOGFOOD_TEST_v0.json"
            ),
            candidate_ref=candidate_ref,
            source_kind="support_doc",
            authority_layer="support",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            outcome_evidence_kind="dogfood_evidence",
            horizon_refs=[baseline_ref, evaluation_ref],
            evidence_role="primary_outcome_evidence",
            limitation_note="Dogfood source frames baseline and evaluation context only.",
        ),
    ]
    horizons = [
        RepoOutcomeHorizonRow(
            horizon_ref=baseline_ref,
            candidate_ref=candidate_ref,
            horizon_kind="baseline",
            covered_surface_refs=[
                "docs/support/arc_series_mapping/V68_V69_V70_V71_V72_COMBINED_DOGFOOD_TEST_v0.json"
            ],
            source_refs=[
                "docs/support/arc_series_mapping/V68_V69_V70_V71_V72_COMBINED_DOGFOOD_TEST_v0.json"
            ],
            coverage_posture="covered",
            limitation_note="Baseline is the pre-V73 combined dogfood context.",
        ),
        RepoOutcomeHorizonRow(
            horizon_ref=intervention_ref,
            candidate_ref=candidate_ref,
            horizon_kind="intervention",
            covered_surface_refs=[_V72B_TRIAL_FIXTURE, _V72C_HANDOFF_FIXTURE],
            source_refs=[_V72B_TRIAL_FIXTURE, _V72C_HANDOFF_FIXTURE],
            coverage_posture="covered",
            limitation_note="Intervention horizon covers the contained trial and V73 handoff.",
        ),
        RepoOutcomeHorizonRow(
            horizon_ref=evaluation_ref,
            candidate_ref=candidate_ref,
            horizon_kind="evaluation",
            covered_surface_refs=[
                _V72B_EFFECT_FIXTURE,
                _V72B_ROLLBACK_FIXTURE,
                _V72C_AUTHORITY_FIXTURE,
                "docs/support/arc_series_mapping/V68_V69_V70_V71_V72_COMBINED_DOGFOOD_TEST_v0.json",
            ],
            source_refs=[
                _V72B_EFFECT_FIXTURE,
                _V72B_ROLLBACK_FIXTURE,
                _V72C_AUTHORITY_FIXTURE,
                "docs/support/arc_series_mapping/V68_V69_V70_V71_V72_COMBINED_DOGFOOD_TEST_v0.json",
            ],
            coverage_posture="partially_covered",
            limitation_note="Evaluation horizon is entry-only and does not judge the outcome.",
        ),
    ]
    payload = {
        "schema": REPO_OUTCOME_EVIDENCE_SOURCE_INDEX_SCHEMA,
        "review_id": "review:v73a:outcome-entry",
        "snapshot_id": handoff.snapshot_id,
        "source_set_id": handoff.source_set_id,
        "post_integration_handoff_id": handoff.post_integration_handoff_id,
        "trial_record_id": trial.trial_record_id,
        "effect_surface_register_id": effect.effect_surface_register_id,
        "rollback_readiness_id": rollback.rollback_readiness_id,
        "authority_posture_id": authority.authority_posture_id,
        "source_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.source_ref)
        ],
        "outcome_horizon_rows": [
            row.model_dump(mode="json") for row in sorted(horizons, key=lambda row: row.horizon_ref)
        ],
        "non_judgment_summary": _V73A_NON_JUDGMENT_SUMMARY,
    }
    payload["evidence_source_index_id"] = _surface_id(
        "repo_outcome_evidence_source_index",
        REPO_OUTCOME_EVIDENCE_SOURCE_INDEX_SCHEMA,
        payload,
        "evidence_source_index_id",
    )
    return RepoOutcomeEvidenceSourceIndex.model_validate(payload)


def derive_v73a_repo_candidate_outcome_review_entry(
    *,
    repo_root: Path,
    outcome_evidence_source_index: RepoOutcomeEvidenceSourceIndex | None = None,
    post_integration_outcome_review_handoff: RepoPostIntegrationOutcomeReviewHandoff | None = None,
) -> RepoCandidateOutcomeReviewEntry:
    source_index = outcome_evidence_source_index or derive_v73a_repo_outcome_evidence_source_index(
        repo_root=repo_root
    )
    handoff = post_integration_outcome_review_handoff or _load_v72c_handoff(repo_root)
    rows = [
        RepoCandidateOutcomeReviewEntryRow(
            entry_ref="entry:v73a:self-evidencing:outcome-review",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            source_handoff_refs=["handoff:v72c:self-evidencing:v73-review"],
            trial_refs=["trial:v72b:self-evidencing:dry-run"],
            effect_refs=["effect:v72b:self-evidencing:schema-surface"],
            rollback_refs=["rollback:v72b:self-evidencing:plan-present"],
            authority_posture_refs=["authority:v72c:self-evidencing:maintainer-required"],
            outcome_source_refs=[row.source_ref for row in source_index.source_rows],
            baseline_horizon_ref="horizon:v73a:self-evidencing:baseline",
            intervention_horizon_ref="horizon:v73a:self-evidencing:intervention",
            evaluation_horizon_ref="horizon:v73a:self-evidencing:evaluation",
            blocking_trial_gap_refs=[],
            blocking_effect_gap_refs=[],
            blocking_rollback_gap_refs=[],
            blocking_authority_boundary_refs=[],
            entry_posture="eligible_for_outcome_review",
            odeu_lanes=["deontic", "epistemic", "utility"],
            guardrail_refs=["guardrail:v73a:self-evidencing:no-authority"],
            limitation_note="Entry opens bounded V73 review without judging outcome.",
        )
    ]
    payload = {
        "schema": REPO_CANDIDATE_OUTCOME_REVIEW_ENTRY_SCHEMA,
        "review_id": source_index.review_id,
        "snapshot_id": source_index.snapshot_id,
        "source_set_id": source_index.source_set_id,
        "post_integration_handoff_id": handoff.post_integration_handoff_id,
        "evidence_source_index_id": source_index.evidence_source_index_id,
        "entry_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.entry_ref)
        ],
        "non_judgment_summary": _V73A_NON_JUDGMENT_SUMMARY,
    }
    payload["outcome_review_entry_id"] = _surface_id(
        "repo_candidate_outcome_review_entry",
        REPO_CANDIDATE_OUTCOME_REVIEW_ENTRY_SCHEMA,
        payload,
        "outcome_review_entry_id",
    )
    return RepoCandidateOutcomeReviewEntry.model_validate(payload)


def derive_v73a_repo_outcome_review_boundary_guardrail(
    *,
    repo_root: Path,
    candidate_outcome_review_entry: RepoCandidateOutcomeReviewEntry | None = None,
) -> RepoOutcomeReviewBoundaryGuardrail:
    entry = candidate_outcome_review_entry or derive_v73a_repo_candidate_outcome_review_entry(
        repo_root=repo_root
    )
    rows = [
        RepoOutcomeReviewBoundaryGuardrailRow(
            guardrail_ref="guardrail:v73a:self-evidencing:no-authority",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            entry_refs=["entry:v73a:self-evidencing:outcome-review"],
            forbidden_downstream_roles=sorted(_V73A_FORBIDDEN_ROLE_SET),
            boundary_posture=[
                "no_demotion_authority",
                "no_dispatch_authority",
                "no_external_contest_authority",
                "no_product_authorization",
                "no_promotion_authority",
                "no_release_authority",
                "no_runtime_permission",
            ],
            required_later_authority=["none_selected_here"],
            limitation_note="Guardrail preserves entry-only review without downstream authority.",
        )
    ]
    payload = {
        "schema": REPO_OUTCOME_REVIEW_BOUNDARY_GUARDRAIL_SCHEMA,
        "review_id": entry.review_id,
        "snapshot_id": entry.snapshot_id,
        "source_set_id": entry.source_set_id,
        "outcome_review_entry_id": entry.outcome_review_entry_id,
        "guardrail_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.guardrail_ref)
        ],
        "boundary_summary": _V73A_BOUNDARY_SUMMARY,
    }
    payload["boundary_guardrail_id"] = _surface_id(
        "repo_outcome_review_boundary_guardrail",
        REPO_OUTCOME_REVIEW_BOUNDARY_GUARDRAIL_SCHEMA,
        payload,
        "boundary_guardrail_id",
    )
    return RepoOutcomeReviewBoundaryGuardrail.model_validate(payload)


def validate_v73a_candidate_outcome_review_bundle(
    *,
    contained_integration_trial_record: RepoContainedIntegrationTrialRecord,
    integration_effect_surface_register: RepoIntegrationEffectSurfaceRegister,
    integration_rollback_readiness: RepoIntegrationRollbackReadiness,
    commit_release_authority_posture: RepoCommitReleaseAuthorityPosture,
    post_integration_outcome_review_handoff: RepoPostIntegrationOutcomeReviewHandoff,
    contained_integration_family_closeout_alignment: (
        RepoContainedIntegrationFamilyCloseoutAlignment
    ),
    outcome_evidence_source_index: RepoOutcomeEvidenceSourceIndex,
    candidate_outcome_review_entry: RepoCandidateOutcomeReviewEntry,
    outcome_review_boundary_guardrail: RepoOutcomeReviewBoundaryGuardrail,
) -> None:
    if (
        post_integration_outcome_review_handoff.trial_record_id
        != contained_integration_trial_record.trial_record_id
    ):
        raise ValueError("V72-C handoff must reference V72-B trial record")
    if (
        post_integration_outcome_review_handoff.effect_surface_register_id
        != integration_effect_surface_register.effect_surface_register_id
    ):
        raise ValueError("V72-C handoff must reference V72-B effect surface register")
    if (
        post_integration_outcome_review_handoff.rollback_readiness_id
        != integration_rollback_readiness.rollback_readiness_id
    ):
        raise ValueError("V72-C handoff must reference V72-B rollback readiness")
    if (
        post_integration_outcome_review_handoff.authority_posture_id
        != commit_release_authority_posture.authority_posture_id
    ):
        raise ValueError("V72-C handoff must reference commit/release authority posture")
    if (
        contained_integration_family_closeout_alignment.post_integration_handoff_id
        != post_integration_outcome_review_handoff.post_integration_handoff_id
    ):
        raise ValueError("V72 family closeout must reference post-integration handoff")
    if (
        outcome_evidence_source_index.post_integration_handoff_id
        != post_integration_outcome_review_handoff.post_integration_handoff_id
    ):
        raise ValueError("outcome source index must reference V72-C handoff")
    if (
        outcome_evidence_source_index.trial_record_id
        != contained_integration_trial_record.trial_record_id
    ):
        raise ValueError("outcome source index must reference V72-B trial record")
    if (
        outcome_evidence_source_index.effect_surface_register_id
        != integration_effect_surface_register.effect_surface_register_id
    ):
        raise ValueError("outcome source index must reference V72-B effect surface register")
    if (
        outcome_evidence_source_index.rollback_readiness_id
        != integration_rollback_readiness.rollback_readiness_id
    ):
        raise ValueError("outcome source index must reference V72-B rollback readiness")
    if (
        outcome_evidence_source_index.authority_posture_id
        != commit_release_authority_posture.authority_posture_id
    ):
        raise ValueError("outcome source index must reference commit/release authority posture")
    if (
        candidate_outcome_review_entry.post_integration_handoff_id
        != post_integration_outcome_review_handoff.post_integration_handoff_id
    ):
        raise ValueError("outcome entry must reference V72-C handoff")
    if (
        candidate_outcome_review_entry.evidence_source_index_id
        != outcome_evidence_source_index.evidence_source_index_id
    ):
        raise ValueError("outcome entry must reference evidence source index")
    if (
        outcome_review_boundary_guardrail.outcome_review_entry_id
        != candidate_outcome_review_entry.outcome_review_entry_id
    ):
        raise ValueError("boundary guardrail must reference outcome entry")
    if not (
        outcome_evidence_source_index.review_id
        == candidate_outcome_review_entry.review_id
        == outcome_review_boundary_guardrail.review_id
        and outcome_evidence_source_index.snapshot_id
        == candidate_outcome_review_entry.snapshot_id
        == outcome_review_boundary_guardrail.snapshot_id
        and outcome_evidence_source_index.source_set_id
        == candidate_outcome_review_entry.source_set_id
        == outcome_review_boundary_guardrail.source_set_id
    ):
        raise ValueError(
            "V73-A review_id, snapshot_id, and source_set_id must match across surfaces"
        )

    handoff_rows = {
        row.handoff_ref: row for row in post_integration_outcome_review_handoff.handoff_rows
    }
    trial_rows = {row.trial_ref: row for row in contained_integration_trial_record.trial_rows}
    effect_rows = {row.effect_ref: row for row in integration_effect_surface_register.effect_rows}
    rollback_rows = {row.rollback_ref: row for row in integration_rollback_readiness.rollback_rows}
    authority_rows = {
        row.authority_posture_ref: row
        for row in commit_release_authority_posture.authority_posture_rows
    }
    source_rows = {row.source_ref: row for row in outcome_evidence_source_index.source_rows}
    horizon_rows = {
        row.horizon_ref: row for row in outcome_evidence_source_index.outcome_horizon_rows
    }
    guardrail_rows = {
        row.guardrail_ref: row for row in outcome_review_boundary_guardrail.guardrail_rows
    }

    represented_handoff_refs: set[str] = set()
    seen_guardrails: set[str] = set()
    for entry in candidate_outcome_review_entry.entry_rows:
        for handoff_ref in entry.source_handoff_refs:
            handoff = handoff_rows.get(handoff_ref)
            if handoff is None:
                raise ValueError("entry rows must reference known V72-C handoff rows")
            represented_handoff_refs.add(handoff_ref)
            if handoff.candidate_ref != entry.candidate_ref:
                raise ValueError("entry candidate_ref must match V72-C handoff candidate")
            if (
                handoff.handoff_posture == "ready_for_v73_review"
                and entry.entry_posture != "eligible_for_outcome_review"
            ):
                raise ValueError("ready V72-C handoffs require eligible outcome-review entries")
            if (
                handoff.handoff_posture != "ready_for_v73_review"
                and entry.entry_posture == "eligible_for_outcome_review"
            ):
                raise ValueError("non-ready V72-C handoffs cannot become eligible")
            if handoff.carried_forward_gap_refs and entry.entry_posture not in {
                "blocked_by_missing_trial_evidence",
                "blocked_by_effect_gap",
                "blocked_by_rollback_gap",
                "blocked_by_authority_boundary",
                "future_family_only",
            }:
                raise ValueError("gap-bearing V72-C handoffs must remain blocked or future-family")
            entry_blocker_refs = set(
                entry.blocking_trial_gap_refs
                + entry.blocking_effect_gap_refs
                + entry.blocking_rollback_gap_refs
                + entry.blocking_authority_boundary_refs
            )
            missing_handoff_gap_refs = sorted(
                set(handoff.carried_forward_gap_refs) - entry_blocker_refs
            )
            if missing_handoff_gap_refs:
                raise ValueError(
                    "V72-C carried-forward gap refs must be represented by entry blocker refs: "
                    f"{missing_handoff_gap_refs}"
                )
            if handoff.carried_forward_dissent_refs and entry.entry_posture != "future_family_only":
                raise ValueError("dissent-bearing V72-C handoffs must remain future-family")
        for trial_ref in entry.trial_refs:
            trial = trial_rows.get(trial_ref)
            if trial is None:
                raise ValueError("entry rows must reference known trial rows")
            if trial.candidate_ref != entry.candidate_ref:
                raise ValueError("trial candidate_ref must match entry candidate_ref")
        for effect_ref in entry.effect_refs:
            effect = effect_rows.get(effect_ref)
            if effect is None:
                raise ValueError("entry rows must reference known effect rows")
            if effect.candidate_ref != entry.candidate_ref:
                raise ValueError("effect candidate_ref must match entry candidate_ref")
        for rollback_ref in entry.rollback_refs:
            rollback = rollback_rows.get(rollback_ref)
            if rollback is None:
                raise ValueError("entry rows must reference known rollback rows")
            if rollback.candidate_ref != entry.candidate_ref:
                raise ValueError("rollback candidate_ref must match entry candidate_ref")
        for authority_ref in entry.authority_posture_refs:
            authority = authority_rows.get(authority_ref)
            if authority is None:
                raise ValueError("entry rows must reference known authority posture rows")
            if authority.candidate_ref != entry.candidate_ref:
                raise ValueError("authority candidate_ref must match entry candidate_ref")
        for source_ref in entry.outcome_source_refs:
            source = source_rows.get(source_ref)
            if source is None:
                raise ValueError("entry rows must reference known outcome sources")
            if source.candidate_ref != entry.candidate_ref:
                raise ValueError("source candidate_ref must match entry candidate_ref")
        horizon_refs = {
            entry.baseline_horizon_ref,
            entry.intervention_horizon_ref,
            entry.evaluation_horizon_ref,
        }
        if len(horizon_refs) != 3:
            raise ValueError(
                "eligible entries require distinct baseline/intervention/evaluation horizons"
            )
        expected_horizon_kinds = {
            entry.baseline_horizon_ref: "baseline",
            entry.intervention_horizon_ref: "intervention",
            entry.evaluation_horizon_ref: "evaluation",
        }
        expected_outcome_source_refs: set[str] = set()
        for horizon_ref, horizon_kind in expected_horizon_kinds.items():
            horizon = horizon_rows.get(horizon_ref)
            if horizon is None:
                raise ValueError("entry rows must reference known outcome horizons")
            if horizon.candidate_ref != entry.candidate_ref:
                raise ValueError("horizon candidate_ref must match entry candidate_ref")
            if horizon.horizon_kind != horizon_kind:
                raise ValueError(
                    "entry horizon refs must match baseline/intervention/evaluation kinds"
                )
            expected_outcome_source_refs.update(horizon.source_refs)
        if set(entry.outcome_source_refs) != expected_outcome_source_refs:
            raise ValueError(
                "entry outcome_source_refs must equal the union of referenced horizon sources"
            )
        for guardrail_ref in entry.guardrail_refs:
            guardrail = guardrail_rows.get(guardrail_ref)
            if guardrail is None:
                raise ValueError("entry rows must reference known guardrails")
            seen_guardrails.add(guardrail_ref)
            if guardrail.candidate_ref != entry.candidate_ref:
                raise ValueError("guardrail candidate_ref must match entry candidate_ref")
            if entry.entry_ref not in guardrail.entry_refs:
                raise ValueError("guardrail rows must reference entry rows")

    orphan_guardrails = sorted(set(guardrail_rows) - seen_guardrails)
    if orphan_guardrails:
        raise ValueError(f"guardrail rows must be referenced by entries: {orphan_guardrails}")
    omitted_handoff_refs = sorted(set(handoff_rows) - represented_handoff_refs)
    if omitted_handoff_refs:
        raise ValueError(
            "every V72-C handoff row must be represented by an outcome entry: "
            f"{omitted_handoff_refs}"
        )


def derive_v73a_repo_candidate_outcome_review_bundle(
    *,
    repo_root: Path,
) -> tuple[
    RepoContainedIntegrationTrialRecord,
    RepoIntegrationEffectSurfaceRegister,
    RepoIntegrationRollbackReadiness,
    RepoCommitReleaseAuthorityPosture,
    RepoPostIntegrationOutcomeReviewHandoff,
    RepoContainedIntegrationFamilyCloseoutAlignment,
    RepoOutcomeEvidenceSourceIndex,
    RepoCandidateOutcomeReviewEntry,
    RepoOutcomeReviewBoundaryGuardrail,
]:
    trial = _load_v72b_trial_record(repo_root)
    effect = _load_v72b_effect_surface(repo_root)
    rollback = _load_v72b_rollback_readiness(repo_root)
    authority = _load_v72c_authority_posture(repo_root)
    handoff = _load_v72c_handoff(repo_root)
    closeout = _load_v72c_closeout(repo_root)
    source_index = derive_v73a_repo_outcome_evidence_source_index(
        repo_root=repo_root,
        contained_integration_trial_record=trial,
        integration_effect_surface_register=effect,
        integration_rollback_readiness=rollback,
        commit_release_authority_posture=authority,
        post_integration_outcome_review_handoff=handoff,
    )
    entry = derive_v73a_repo_candidate_outcome_review_entry(
        repo_root=repo_root,
        outcome_evidence_source_index=source_index,
        post_integration_outcome_review_handoff=handoff,
    )
    guardrail = derive_v73a_repo_outcome_review_boundary_guardrail(
        repo_root=repo_root,
        candidate_outcome_review_entry=entry,
    )
    return trial, effect, rollback, authority, handoff, closeout, source_index, entry, guardrail


def derive_v73b_repo_outcome_regression_register(
    *,
    repo_root: Path,
    candidate_outcome_observation_record: RepoCandidateOutcomeObservationRecord | None = None,
) -> RepoOutcomeRegressionRegister:
    observation = (
        candidate_outcome_observation_record
        or derive_v73b_repo_candidate_outcome_observation_record(repo_root=repo_root)
    )
    rows = [
        RepoOutcomeRegressionRow(
            regression_ref="regression:v73b:self-evidencing:no-schema-regression",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            observation_refs=["observation:v73b:self-evidencing:bounded-benefit"],
            regression_posture="no_regression_observed",
            regression_surface_kind="schema_regression",
            checked_evaluation_refs=["horizon:v73a:self-evidencing:evaluation"],
            negative_control_refs=["negative-control:v73b:schema-export-deterministic"],
            blocking_for_recommendation=False,
            limitation_note=(
                "No schema regression is observed within the bounded evaluation horizon."
            ),
        )
    ]
    payload = {
        "schema": REPO_OUTCOME_REGRESSION_REGISTER_SCHEMA,
        "review_id": observation.review_id,
        "snapshot_id": observation.snapshot_id,
        "source_set_id": observation.source_set_id,
        "outcome_observation_record_id": observation.outcome_observation_record_id,
        "regression_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.regression_ref)
        ],
        "non_implementation_summary": _V73B_NON_IMPLEMENTATION_SUMMARY,
    }
    payload["outcome_regression_register_id"] = _surface_id(
        "repo_outcome_regression_register",
        REPO_OUTCOME_REGRESSION_REGISTER_SCHEMA,
        payload,
        "outcome_regression_register_id",
    )
    return RepoOutcomeRegressionRegister.model_validate(payload)


def derive_v73b_repo_tool_fitness_drift_register(
    *,
    repo_root: Path,
    candidate_outcome_observation_record: RepoCandidateOutcomeObservationRecord | None = None,
) -> RepoToolFitnessDriftRegister:
    observation = (
        candidate_outcome_observation_record
        or derive_v73b_repo_candidate_outcome_observation_record(repo_root=repo_root)
    )
    rows = [
        RepoToolFitnessDriftRow(
            tool_fitness_ref="tool-fitness:v73b:arc-closeout-check:target-bound",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            observation_refs=["observation:v73b:self-evidencing:bounded-benefit"],
            tool_id="make arc-closeout-check",
            tool_target_claim_refs=["claim:v73b:v203-closeout-doc-artifacts"],
            tool_target_horizon_refs=["horizon:v73a:self-evidencing:evaluation"],
            target_namespace_kind="closeout_arc_id",
            prior_applicability_refs=["tool-applicability:v68c:arc-closeout-check:closeout-docs"],
            tool_fitness_posture="tool_fit_confirmed",
            observed_result_refs=[
                "artifacts/agent_harness/v203/evidence_inputs/"
                "v73a_candidate_outcome_review_entry_evidence_v203.json"
            ],
            limitation_note="Tool fit is confirmed only for the v203 closeout-doc artifact target.",
        )
    ]
    payload = {
        "schema": REPO_TOOL_FITNESS_DRIFT_REGISTER_SCHEMA,
        "review_id": observation.review_id,
        "snapshot_id": observation.snapshot_id,
        "source_set_id": observation.source_set_id,
        "outcome_observation_record_id": observation.outcome_observation_record_id,
        "tool_fitness_rows": [
            row.model_dump(mode="json")
            for row in sorted(rows, key=lambda row: row.tool_fitness_ref)
        ],
        "target_bound_summary": _V73B_TOOL_TARGET_BOUND_SUMMARY,
    }
    payload["tool_fitness_drift_register_id"] = _surface_id(
        "repo_tool_fitness_drift_register",
        REPO_TOOL_FITNESS_DRIFT_REGISTER_SCHEMA,
        payload,
        "tool_fitness_drift_register_id",
    )
    return RepoToolFitnessDriftRegister.model_validate(payload)


def derive_v73b_repo_candidate_outcome_observation_record(
    *,
    repo_root: Path,
    candidate_outcome_review_entry: RepoCandidateOutcomeReviewEntry | None = None,
    outcome_evidence_source_index: RepoOutcomeEvidenceSourceIndex | None = None,
    outcome_review_boundary_guardrail: RepoOutcomeReviewBoundaryGuardrail | None = None,
) -> RepoCandidateOutcomeObservationRecord:
    entry = candidate_outcome_review_entry or _load_v73a_entry(repo_root)
    source_index = outcome_evidence_source_index or _load_v73a_source_index(repo_root)
    guardrail = outcome_review_boundary_guardrail or _load_v73a_guardrail(repo_root)
    rows = [
        RepoCandidateOutcomeObservationRow(
            observation_ref="observation:v73b:self-evidencing:bounded-benefit",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            entry_refs=["entry:v73a:self-evidencing:outcome-review"],
            outcome_source_refs=[row.source_ref for row in source_index.source_rows],
            baseline_refs=["horizon:v73a:self-evidencing:baseline"],
            intervention_refs=["horizon:v73a:self-evidencing:intervention"],
            evaluation_refs=["horizon:v73a:self-evidencing:evaluation"],
            outcome_observation_posture="benefit_observed",
            confidence_posture="moderate_with_limitations",
            carried_forward_gap_refs=[],
            regression_refs=["regression:v73b:self-evidencing:no-schema-regression"],
            tool_fitness_refs=["tool-fitness:v73b:arc-closeout-check:target-bound"],
            non_promotion_guardrail_refs=["guardrail:v73a:self-evidencing:no-authority"],
            limitation_note="Observation records bounded benefit evidence for later review only.",
        )
    ]
    payload = {
        "schema": REPO_CANDIDATE_OUTCOME_OBSERVATION_RECORD_SCHEMA,
        "review_id": entry.review_id,
        "snapshot_id": entry.snapshot_id,
        "source_set_id": entry.source_set_id,
        "outcome_review_entry_id": entry.outcome_review_entry_id,
        "evidence_source_index_id": source_index.evidence_source_index_id,
        "boundary_guardrail_id": guardrail.boundary_guardrail_id,
        "observation_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.observation_ref)
        ],
        "non_authority_summary": _V73B_NON_AUTHORITY_SUMMARY,
    }
    payload["outcome_observation_record_id"] = _surface_id(
        "repo_candidate_outcome_observation_record",
        REPO_CANDIDATE_OUTCOME_OBSERVATION_RECORD_SCHEMA,
        payload,
        "outcome_observation_record_id",
    )
    return RepoCandidateOutcomeObservationRecord.model_validate(payload)


def validate_v73b_candidate_outcome_review_bundle(
    *,
    outcome_evidence_source_index: RepoOutcomeEvidenceSourceIndex,
    candidate_outcome_review_entry: RepoCandidateOutcomeReviewEntry,
    outcome_review_boundary_guardrail: RepoOutcomeReviewBoundaryGuardrail,
    candidate_outcome_observation_record: RepoCandidateOutcomeObservationRecord,
    outcome_regression_register: RepoOutcomeRegressionRegister,
    tool_fitness_drift_register: RepoToolFitnessDriftRegister,
) -> None:
    if (
        candidate_outcome_observation_record.outcome_review_entry_id
        != candidate_outcome_review_entry.outcome_review_entry_id
    ):
        raise ValueError("observation record must reference V73-A outcome entry")
    if (
        candidate_outcome_observation_record.evidence_source_index_id
        != outcome_evidence_source_index.evidence_source_index_id
    ):
        raise ValueError("observation record must reference V73-A source index")
    if (
        candidate_outcome_observation_record.boundary_guardrail_id
        != outcome_review_boundary_guardrail.boundary_guardrail_id
    ):
        raise ValueError("observation record must reference V73-A guardrail")
    if (
        outcome_regression_register.outcome_observation_record_id
        != candidate_outcome_observation_record.outcome_observation_record_id
    ):
        raise ValueError("regression register must reference observation record")
    if (
        tool_fitness_drift_register.outcome_observation_record_id
        != candidate_outcome_observation_record.outcome_observation_record_id
    ):
        raise ValueError("tool-fitness register must reference observation record")
    if not (
        outcome_evidence_source_index.review_id
        == candidate_outcome_review_entry.review_id
        == outcome_review_boundary_guardrail.review_id
        == candidate_outcome_observation_record.review_id
        == outcome_regression_register.review_id
        == tool_fitness_drift_register.review_id
        and outcome_evidence_source_index.snapshot_id
        == candidate_outcome_review_entry.snapshot_id
        == outcome_review_boundary_guardrail.snapshot_id
        == candidate_outcome_observation_record.snapshot_id
        == outcome_regression_register.snapshot_id
        == tool_fitness_drift_register.snapshot_id
        and outcome_evidence_source_index.source_set_id
        == candidate_outcome_review_entry.source_set_id
        == outcome_review_boundary_guardrail.source_set_id
        == candidate_outcome_observation_record.source_set_id
        == outcome_regression_register.source_set_id
        == tool_fitness_drift_register.source_set_id
    ):
        raise ValueError("V73-B review_id, snapshot_id, and source_set_id must match")

    entry_rows = {row.entry_ref: row for row in candidate_outcome_review_entry.entry_rows}
    source_rows = {row.source_ref: row for row in outcome_evidence_source_index.source_rows}
    horizon_rows = {
        row.horizon_ref: row for row in outcome_evidence_source_index.outcome_horizon_rows
    }
    guardrail_rows = {
        row.guardrail_ref: row for row in outcome_review_boundary_guardrail.guardrail_rows
    }
    observation_rows = {
        row.observation_ref: row for row in candidate_outcome_observation_record.observation_rows
    }
    regression_rows = {
        row.regression_ref: row for row in outcome_regression_register.regression_rows
    }
    tool_fitness_rows = {
        row.tool_fitness_ref: row for row in tool_fitness_drift_register.tool_fitness_rows
    }

    for observation in candidate_outcome_observation_record.observation_rows:
        for entry_ref in observation.entry_refs:
            entry = entry_rows.get(entry_ref)
            if entry is None:
                raise ValueError("observation rows must reference known V73-A entries")
            if entry.entry_posture != "eligible_for_outcome_review":
                raise ValueError("observation rows require eligible V73-A entries")
            if entry.candidate_ref != observation.candidate_ref:
                raise ValueError("observation candidate_ref must match V73-A entry")
        for source_ref in observation.outcome_source_refs:
            source = source_rows.get(source_ref)
            if source is None:
                raise ValueError("observation rows must reference known outcome sources")
            if source.candidate_ref != observation.candidate_ref:
                raise ValueError("observation source candidate_ref must match observation")
        for field_name, expected_kind in (
            ("baseline_refs", "baseline"),
            ("intervention_refs", "intervention"),
            ("evaluation_refs", "evaluation"),
        ):
            for horizon_ref in getattr(observation, field_name):
                horizon = horizon_rows.get(horizon_ref)
                if horizon is None:
                    raise ValueError("observation rows must reference known outcome horizons")
                if horizon.horizon_kind != expected_kind:
                    raise ValueError("observation horizon refs must match their horizon kind")
                if horizon.candidate_ref != observation.candidate_ref:
                    raise ValueError("observation horizon candidate_ref must match observation")
        for guardrail_ref in observation.non_promotion_guardrail_refs:
            guardrail = guardrail_rows.get(guardrail_ref)
            if guardrail is None:
                raise ValueError("observation rows must reference known guardrails")
            if guardrail.candidate_ref != observation.candidate_ref:
                raise ValueError("observation guardrail candidate_ref must match observation")
            if "promotion_authority" not in guardrail.forbidden_downstream_roles:
                raise ValueError("non-promotion guardrails must forbid promotion authority")
        for regression_ref in observation.regression_refs:
            regression = regression_rows.get(regression_ref)
            if regression is None:
                raise ValueError("observation rows must reference known regression rows")
            if regression.candidate_ref != observation.candidate_ref:
                raise ValueError("regression candidate_ref must match observation")
            if observation.observation_ref not in regression.observation_refs:
                raise ValueError("regression rows must point back to observation rows")
            if (
                observation.outcome_observation_posture == "benefit_observed"
                and regression.blocking_for_recommendation
                and regression.regression_ref not in observation.carried_forward_gap_refs
            ):
                raise ValueError("benefit observations must carry forward blocking regression refs")
        for tool_fitness_ref in observation.tool_fitness_refs:
            tool_fitness = tool_fitness_rows.get(tool_fitness_ref)
            if tool_fitness is None:
                raise ValueError("observation rows must reference known tool-fitness rows")
            if tool_fitness.candidate_ref != observation.candidate_ref:
                raise ValueError("tool-fitness candidate_ref must match observation")
            if observation.observation_ref not in tool_fitness.observation_refs:
                raise ValueError("tool-fitness rows must point back to observation rows")

    for regression in outcome_regression_register.regression_rows:
        for observation_ref in regression.observation_refs:
            observation = observation_rows.get(observation_ref)
            if observation is None:
                raise ValueError("regression rows must reference known observations")
            if observation.candidate_ref != regression.candidate_ref:
                raise ValueError("regression observation candidate_ref must match regression")
            if regression.regression_ref not in observation.regression_refs:
                raise ValueError("observation rows must point back to regression rows")
            if (
                observation.outcome_observation_posture == "benefit_observed"
                and regression.blocking_for_recommendation
                and regression.regression_ref not in observation.carried_forward_gap_refs
            ):
                raise ValueError("benefit observations must carry forward blocking regression refs")
        for horizon_ref in regression.checked_evaluation_refs:
            horizon = horizon_rows.get(horizon_ref)
            if horizon is None:
                raise ValueError("regression rows must reference known evaluation horizons")
            if horizon.horizon_kind != "evaluation":
                raise ValueError("regression checked horizons must be evaluation horizons")
            if horizon.candidate_ref != regression.candidate_ref:
                raise ValueError("regression horizon candidate_ref must match regression")

    for tool_fitness in tool_fitness_drift_register.tool_fitness_rows:
        for observation_ref in tool_fitness.observation_refs:
            observation = observation_rows.get(observation_ref)
            if observation is None:
                raise ValueError("tool-fitness rows must reference known observations")
            if observation.candidate_ref != tool_fitness.candidate_ref:
                raise ValueError("tool-fitness observation candidate_ref must match row")
        for horizon_ref in tool_fitness.tool_target_horizon_refs:
            horizon = horizon_rows.get(horizon_ref)
            if horizon is None:
                raise ValueError("tool-fitness rows must reference known target horizons")
            if horizon.candidate_ref != tool_fitness.candidate_ref:
                raise ValueError("tool-fitness horizon candidate_ref must match row")


def derive_v73b_repo_candidate_outcome_review_bundle(
    *,
    repo_root: Path,
) -> tuple[
    RepoOutcomeEvidenceSourceIndex,
    RepoCandidateOutcomeReviewEntry,
    RepoOutcomeReviewBoundaryGuardrail,
    RepoCandidateOutcomeObservationRecord,
    RepoOutcomeRegressionRegister,
    RepoToolFitnessDriftRegister,
]:
    source_index = _load_v73a_source_index(repo_root)
    entry = _load_v73a_entry(repo_root)
    guardrail = _load_v73a_guardrail(repo_root)
    observation = derive_v73b_repo_candidate_outcome_observation_record(
        repo_root=repo_root,
        candidate_outcome_review_entry=entry,
        outcome_evidence_source_index=source_index,
        outcome_review_boundary_guardrail=guardrail,
    )
    regression = derive_v73b_repo_outcome_regression_register(
        repo_root=repo_root,
        candidate_outcome_observation_record=observation,
    )
    tool_fitness = derive_v73b_repo_tool_fitness_drift_register(
        repo_root=repo_root,
        candidate_outcome_observation_record=observation,
    )
    validate_v73b_candidate_outcome_review_bundle(
        outcome_evidence_source_index=source_index,
        candidate_outcome_review_entry=entry,
        outcome_review_boundary_guardrail=guardrail,
        candidate_outcome_observation_record=observation,
        outcome_regression_register=regression,
        tool_fitness_drift_register=tool_fitness,
    )
    return source_index, entry, guardrail, observation, regression, tool_fitness


def derive_v73c_repo_self_improvement_outcome_ledger(
    *,
    repo_root: Path,
    candidate_outcome_observation_record: RepoCandidateOutcomeObservationRecord | None = None,
    outcome_regression_register: RepoOutcomeRegressionRegister | None = None,
    tool_fitness_drift_register: RepoToolFitnessDriftRegister | None = None,
) -> RepoSelfImprovementOutcomeLedger:
    observation = candidate_outcome_observation_record or _load_v73b_observation(repo_root)
    regression = outcome_regression_register or _load_v73b_regression(repo_root)
    tool_fitness = tool_fitness_drift_register or _load_v73b_tool_fitness(repo_root)
    rows = [
        RepoSelfImprovementOutcomeLedgerRow(
            ledger_ref="ledger:v73c:self-evidencing:positive-review-signal",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            entry_refs=["entry:v73a:self-evidencing:outcome-review"],
            observation_refs=["observation:v73b:self-evidencing:bounded-benefit"],
            regression_refs=["regression:v73b:self-evidencing:no-schema-regression"],
            tool_fitness_refs=["tool-fitness:v73b:arc-closeout-check:target-bound"],
            operator_cognition_signal_refs=[
                "operator-signal:v73c:self-evidencing:workflow-type-emergence"
            ],
            outcome_ledger_posture="positive_signal_recorded",
            carried_forward_gap_refs=[],
            limitation_note="Ledger records a bounded positive review signal for later review.",
        )
    ]
    payload = {
        "schema": REPO_SELF_IMPROVEMENT_OUTCOME_LEDGER_SCHEMA,
        "review_id": observation.review_id,
        "snapshot_id": observation.snapshot_id,
        "source_set_id": observation.source_set_id,
        "outcome_observation_record_id": observation.outcome_observation_record_id,
        "outcome_regression_register_id": regression.outcome_regression_register_id,
        "tool_fitness_drift_register_id": tool_fitness.tool_fitness_drift_register_id,
        "ledger_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.ledger_ref)
        ],
        "non_self_approval_summary": _V73C_LEDGER_SUMMARY,
    }
    payload["self_improvement_outcome_ledger_id"] = _surface_id(
        "repo_self_improvement_outcome_ledger",
        REPO_SELF_IMPROVEMENT_OUTCOME_LEDGER_SCHEMA,
        payload,
        "self_improvement_outcome_ledger_id",
    )
    return RepoSelfImprovementOutcomeLedger.model_validate(payload)


def derive_v73c_repo_operator_cognition_outcome_signal(
    *,
    repo_root: Path,
    candidate_outcome_observation_record: RepoCandidateOutcomeObservationRecord | None = None,
) -> RepoOperatorCognitionOutcomeSignal:
    observation = candidate_outcome_observation_record or _load_v73b_observation(repo_root)
    rows = [
        RepoOperatorCognitionOutcomeSignalRow(
            operator_signal_ref=(
                "operator-signal:v73c:self-evidencing:workflow-type-emergence"
            ),
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            source_refs=[
                "docs/DRAFT_ADEU_CANDIDATE_OUTCOME_REVIEW_V73C_IMPLEMENTATION_MAPPING_v0.md",
                "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS204.md",
            ],
            signal_kind="workflow_exposed_missing_type",
            signal_posture="signal_recorded_for_review",
            workflow_residue_refs=["residue:self-evidencing-workflow-type-emergence"],
            non_authority_guardrail=(
                "Operator signal is no transcript truth, no lock authority, no release "
                "authority, no product authority, no runtime permission, and no dispatch "
                "authority."
            ),
            limitation_note=(
                "Operator cognition signal is evidence for later review only and stays bounded."
            ),
        )
    ]
    payload = {
        "schema": REPO_OPERATOR_COGNITION_OUTCOME_SIGNAL_SCHEMA,
        "review_id": observation.review_id,
        "snapshot_id": observation.snapshot_id,
        "source_set_id": observation.source_set_id,
        "outcome_observation_record_id": observation.outcome_observation_record_id,
        "operator_signal_rows": [
            row.model_dump(mode="json")
            for row in sorted(rows, key=lambda row: row.operator_signal_ref)
        ],
        "non_authority_summary": _V73C_OPERATOR_NON_AUTHORITY_SUMMARY,
    }
    payload["operator_cognition_outcome_signal_id"] = _surface_id(
        "repo_operator_cognition_outcome_signal",
        REPO_OPERATOR_COGNITION_OUTCOME_SIGNAL_SCHEMA,
        payload,
        "operator_cognition_outcome_signal_id",
    )
    return RepoOperatorCognitionOutcomeSignal.model_validate(payload)


def derive_v73c_repo_outcome_promotion_demotion_recommendation(
    *,
    repo_root: Path,
    self_improvement_outcome_ledger: RepoSelfImprovementOutcomeLedger | None = None,
    operator_cognition_outcome_signal: RepoOperatorCognitionOutcomeSignal | None = None,
) -> RepoOutcomePromotionDemotionRecommendation:
    ledger = self_improvement_outcome_ledger or derive_v73c_repo_self_improvement_outcome_ledger(
        repo_root=repo_root
    )
    operator_signal = (
        operator_cognition_outcome_signal
        or derive_v73c_repo_operator_cognition_outcome_signal(repo_root=repo_root)
    )
    rows = [
        RepoOutcomePromotionDemotionRecommendationRow(
            recommendation_ref="recommendation:v73c:self-evidencing:promote-for-later-review",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            ledger_refs=["ledger:v73c:self-evidencing:positive-review-signal"],
            observation_refs=["observation:v73b:self-evidencing:bounded-benefit"],
            regression_refs=["regression:v73b:self-evidencing:no-schema-regression"],
            tool_fitness_refs=["tool-fitness:v73b:arc-closeout-check:target-bound"],
            operator_signal_refs=[
                "operator-signal:v73c:self-evidencing:workflow-type-emergence"
            ],
            recommendation_posture="recommend_promote_for_later_review",
            required_next_surface="v74_operator_projection_review",
            required_later_authority="human_ratification_required",
            forbidden_downstream_roles=sorted(_V73A_FORBIDDEN_ROLE_SET),
            limitation_note=(
                "Recommend promote for later review only; no downstream authority is granted."
            ),
        )
    ]
    payload = {
        "schema": REPO_OUTCOME_PROMOTION_DEMOTION_RECOMMENDATION_SCHEMA,
        "review_id": ledger.review_id,
        "snapshot_id": ledger.snapshot_id,
        "source_set_id": ledger.source_set_id,
        "self_improvement_outcome_ledger_id": ledger.self_improvement_outcome_ledger_id,
        "operator_cognition_outcome_signal_id": (
            operator_signal.operator_cognition_outcome_signal_id
        ),
        "recommendation_rows": [
            row.model_dump(mode="json")
            for row in sorted(rows, key=lambda row: row.recommendation_ref)
        ],
        "recommendation_boundary_summary": _V73C_RECOMMENDATION_BOUNDARY_SUMMARY,
    }
    payload["outcome_promotion_demotion_recommendation_id"] = _surface_id(
        "repo_outcome_promotion_demotion_recommendation",
        REPO_OUTCOME_PROMOTION_DEMOTION_RECOMMENDATION_SCHEMA,
        payload,
        "outcome_promotion_demotion_recommendation_id",
    )
    return RepoOutcomePromotionDemotionRecommendation.model_validate(payload)


def derive_v73c_repo_outcome_review_family_closeout_alignment(
    *,
    repo_root: Path,
    self_improvement_outcome_ledger: RepoSelfImprovementOutcomeLedger | None = None,
    outcome_promotion_demotion_recommendation: (
        RepoOutcomePromotionDemotionRecommendation | None
    ) = None,
) -> RepoOutcomeReviewFamilyCloseoutAlignment:
    ledger = self_improvement_outcome_ledger or derive_v73c_repo_self_improvement_outcome_ledger(
        repo_root=repo_root
    )
    recommendation = (
        outcome_promotion_demotion_recommendation
        or derive_v73c_repo_outcome_promotion_demotion_recommendation(
            repo_root=repo_root,
            self_improvement_outcome_ledger=ledger,
        )
    )
    rows = [
        RepoOutcomeReviewFamilyCloseoutAlignmentRow(
            family_ref="V73",
            closed_slice_refs=["V73-A", "V73-B", "V73-C"],
            emitted_surface_refs=sorted(_V73_SURFACE_SET),
            reviewed_candidate_refs=["candidate:internal:self_evidencing_workflow_type_emergence"],
            ledger_refs=["ledger:v73c:self-evidencing:positive-review-signal"],
            operator_signal_refs=[
                "operator-signal:v73c:self-evidencing:workflow-type-emergence"
            ],
            recommendation_refs=[
                "recommendation:v73c:self-evidencing:promote-for-later-review"
            ],
            non_authority_guardrail_refs=["guardrail:v73c:family-closeout:no-authority"],
            future_family_refs=["V43", "V74", "V75"],
            closeout_alignment_posture="family_closed_review_machinery_only",
            limitation_note="Family closeout records review machinery closure only.",
        )
    ]
    payload = {
        "schema": REPO_OUTCOME_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
        "review_id": ledger.review_id,
        "snapshot_id": ledger.snapshot_id,
        "source_set_id": ledger.source_set_id,
        "self_improvement_outcome_ledger_id": ledger.self_improvement_outcome_ledger_id,
        "outcome_promotion_demotion_recommendation_id": (
            recommendation.outcome_promotion_demotion_recommendation_id
        ),
        "alignment_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.family_ref)
        ],
        "family_closeout_boundary_summary": _V73C_FAMILY_CLOSEOUT_SUMMARY,
    }
    payload["outcome_review_family_closeout_alignment_id"] = _surface_id(
        "repo_outcome_review_family_closeout_alignment",
        REPO_OUTCOME_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
        payload,
        "outcome_review_family_closeout_alignment_id",
    )
    return RepoOutcomeReviewFamilyCloseoutAlignment.model_validate(payload)


def validate_v73c_candidate_outcome_review_closeout_bundle(
    *,
    candidate_outcome_observation_record: RepoCandidateOutcomeObservationRecord,
    outcome_regression_register: RepoOutcomeRegressionRegister,
    tool_fitness_drift_register: RepoToolFitnessDriftRegister,
    self_improvement_outcome_ledger: RepoSelfImprovementOutcomeLedger,
    operator_cognition_outcome_signal: RepoOperatorCognitionOutcomeSignal,
    outcome_promotion_demotion_recommendation: RepoOutcomePromotionDemotionRecommendation,
    outcome_review_family_closeout_alignment: RepoOutcomeReviewFamilyCloseoutAlignment,
) -> None:
    if (
        self_improvement_outcome_ledger.outcome_observation_record_id
        != candidate_outcome_observation_record.outcome_observation_record_id
    ):
        raise ValueError("ledger must reference released V73-B observation record")
    if (
        self_improvement_outcome_ledger.outcome_regression_register_id
        != outcome_regression_register.outcome_regression_register_id
    ):
        raise ValueError("ledger must reference released V73-B regression register")
    if (
        self_improvement_outcome_ledger.tool_fitness_drift_register_id
        != tool_fitness_drift_register.tool_fitness_drift_register_id
    ):
        raise ValueError("ledger must reference released V73-B tool-fitness register")
    if (
        operator_cognition_outcome_signal.outcome_observation_record_id
        != candidate_outcome_observation_record.outcome_observation_record_id
    ):
        raise ValueError("operator signals must reference released V73-B observation record")
    if (
        outcome_promotion_demotion_recommendation.self_improvement_outcome_ledger_id
        != self_improvement_outcome_ledger.self_improvement_outcome_ledger_id
    ):
        raise ValueError("recommendations must reference self-improvement ledger")
    if (
        outcome_promotion_demotion_recommendation.operator_cognition_outcome_signal_id
        != operator_cognition_outcome_signal.operator_cognition_outcome_signal_id
    ):
        raise ValueError("recommendations must reference operator-cognition signal surface")
    if (
        outcome_review_family_closeout_alignment.self_improvement_outcome_ledger_id
        != self_improvement_outcome_ledger.self_improvement_outcome_ledger_id
    ):
        raise ValueError("family closeout alignment must reference self-improvement ledger")
    if (
        outcome_review_family_closeout_alignment.outcome_promotion_demotion_recommendation_id
        != outcome_promotion_demotion_recommendation.outcome_promotion_demotion_recommendation_id
    ):
        raise ValueError("family closeout alignment must reference recommendation surface")
    if not (
        candidate_outcome_observation_record.review_id
        == outcome_regression_register.review_id
        == tool_fitness_drift_register.review_id
        == self_improvement_outcome_ledger.review_id
        == operator_cognition_outcome_signal.review_id
        == outcome_promotion_demotion_recommendation.review_id
        == outcome_review_family_closeout_alignment.review_id
        and candidate_outcome_observation_record.snapshot_id
        == outcome_regression_register.snapshot_id
        == tool_fitness_drift_register.snapshot_id
        == self_improvement_outcome_ledger.snapshot_id
        == operator_cognition_outcome_signal.snapshot_id
        == outcome_promotion_demotion_recommendation.snapshot_id
        == outcome_review_family_closeout_alignment.snapshot_id
        and candidate_outcome_observation_record.source_set_id
        == outcome_regression_register.source_set_id
        == tool_fitness_drift_register.source_set_id
        == self_improvement_outcome_ledger.source_set_id
        == operator_cognition_outcome_signal.source_set_id
        == outcome_promotion_demotion_recommendation.source_set_id
        == outcome_review_family_closeout_alignment.source_set_id
    ):
        raise ValueError("V73-C review_id, snapshot_id, and source_set_id must match")

    observations = {
        row.observation_ref: row for row in candidate_outcome_observation_record.observation_rows
    }
    regressions = {row.regression_ref: row for row in outcome_regression_register.regression_rows}
    tool_fitness_rows = {
        row.tool_fitness_ref: row for row in tool_fitness_drift_register.tool_fitness_rows
    }
    ledger_rows = {row.ledger_ref: row for row in self_improvement_outcome_ledger.ledger_rows}
    operator_rows = {
        row.operator_signal_ref: row
        for row in operator_cognition_outcome_signal.operator_signal_rows
    }
    recommendation_rows = {
        row.recommendation_ref: row
        for row in outcome_promotion_demotion_recommendation.recommendation_rows
    }

    for ledger in self_improvement_outcome_ledger.ledger_rows:
        for observation_ref in ledger.observation_refs:
            observation = observations.get(observation_ref)
            if observation is None:
                raise ValueError("ledger rows must reference known released V73-B observation refs")
            if observation.candidate_ref != ledger.candidate_ref:
                raise ValueError("ledger candidate_ref must match observation candidate_ref")
        blocking_regressions = [
            regression
            for regression in regressions.values()
            if regression.candidate_ref == ledger.candidate_ref
            and regression.blocking_for_recommendation
        ]
        hidden_blockers = sorted(
            regression.regression_ref
            for regression in blocking_regressions
            if regression.regression_ref not in ledger.carried_forward_gap_refs
        )
        if ledger.outcome_ledger_posture == "positive_signal_recorded" and hidden_blockers:
            raise ValueError(
                "positive ledger signals must carry forward blocking regression refs: "
                f"{hidden_blockers}"
            )
        for regression_ref in ledger.regression_refs:
            regression = regressions.get(regression_ref)
            if regression is None:
                raise ValueError("ledger rows must reference known released V73-B regression refs")
            if regression.candidate_ref != ledger.candidate_ref:
                raise ValueError("ledger candidate_ref must match regression candidate_ref")
        for tool_fitness_ref in ledger.tool_fitness_refs:
            tool_fitness = tool_fitness_rows.get(tool_fitness_ref)
            if tool_fitness is None:
                raise ValueError(
                    "ledger rows must reference known released V73-B tool-fitness refs"
                )
            if tool_fitness.candidate_ref != ledger.candidate_ref:
                raise ValueError("ledger candidate_ref must match tool-fitness candidate_ref")
        for operator_signal_ref in ledger.operator_cognition_signal_refs:
            operator_signal = operator_rows.get(operator_signal_ref)
            if operator_signal is None:
                raise ValueError("ledger rows must reference known operator signal refs")
            if operator_signal.candidate_ref != ledger.candidate_ref:
                raise ValueError("ledger candidate_ref must match operator signal candidate_ref")

    for recommendation in outcome_promotion_demotion_recommendation.recommendation_rows:
        for ledger_ref in recommendation.ledger_refs:
            ledger = ledger_rows.get(ledger_ref)
            if ledger is None:
                raise ValueError("recommendation rows must reference known ledger rows")
            if ledger.candidate_ref != recommendation.candidate_ref:
                raise ValueError("recommendation candidate_ref must match ledger candidate_ref")
        for operator_signal_ref in recommendation.operator_signal_refs:
            operator_signal = operator_rows.get(operator_signal_ref)
            if operator_signal is None:
                raise ValueError("recommendation rows must reference known operator signal rows")
            if operator_signal.candidate_ref != recommendation.candidate_ref:
                raise ValueError(
                    "recommendation candidate_ref must match operator signal candidate_ref"
                )
        if (
            recommendation.recommendation_posture == "recommend_promote_for_later_review"
            and recommendation.required_next_surface == "deferred_no_selection"
        ):
            raise ValueError("promotion recommendations require a later review surface")
        if (
            recommendation.required_later_authority == "product_authority_required"
            and recommendation.required_next_surface != "v74_operator_projection_review"
        ):
            raise ValueError("product recommendations require V74 review")

    for alignment in outcome_review_family_closeout_alignment.alignment_rows:
        for ledger_ref in alignment.ledger_refs:
            if ledger_ref not in ledger_rows:
                raise ValueError("family closeout alignment must reference known ledger rows")
        for operator_signal_ref in alignment.operator_signal_refs:
            if operator_signal_ref not in operator_rows:
                raise ValueError(
                    "family closeout alignment must reference known operator signal rows"
                )
        for recommendation_ref in alignment.recommendation_refs:
            if recommendation_ref not in recommendation_rows:
                raise ValueError(
                    "family closeout alignment must reference known recommendation rows"
                )


def derive_v73c_repo_candidate_outcome_review_closeout_bundle(
    *,
    repo_root: Path,
) -> tuple[
    RepoCandidateOutcomeObservationRecord,
    RepoOutcomeRegressionRegister,
    RepoToolFitnessDriftRegister,
    RepoSelfImprovementOutcomeLedger,
    RepoOperatorCognitionOutcomeSignal,
    RepoOutcomePromotionDemotionRecommendation,
    RepoOutcomeReviewFamilyCloseoutAlignment,
]:
    observation = _load_v73b_observation(repo_root)
    regression = _load_v73b_regression(repo_root)
    tool_fitness = _load_v73b_tool_fitness(repo_root)
    ledger = derive_v73c_repo_self_improvement_outcome_ledger(
        repo_root=repo_root,
        candidate_outcome_observation_record=observation,
        outcome_regression_register=regression,
        tool_fitness_drift_register=tool_fitness,
    )
    operator_signal = derive_v73c_repo_operator_cognition_outcome_signal(
        repo_root=repo_root,
        candidate_outcome_observation_record=observation,
    )
    recommendation = derive_v73c_repo_outcome_promotion_demotion_recommendation(
        repo_root=repo_root,
        self_improvement_outcome_ledger=ledger,
        operator_cognition_outcome_signal=operator_signal,
    )
    alignment = derive_v73c_repo_outcome_review_family_closeout_alignment(
        repo_root=repo_root,
        self_improvement_outcome_ledger=ledger,
        outcome_promotion_demotion_recommendation=recommendation,
    )
    validate_v73c_candidate_outcome_review_closeout_bundle(
        candidate_outcome_observation_record=observation,
        outcome_regression_register=regression,
        tool_fitness_drift_register=tool_fitness,
        self_improvement_outcome_ledger=ledger,
        operator_cognition_outcome_signal=operator_signal,
        outcome_promotion_demotion_recommendation=recommendation,
        outcome_review_family_closeout_alignment=alignment,
    )
    return observation, regression, tool_fitness, ledger, operator_signal, recommendation, alignment
