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
    "docs/support/arc_series_mapping/"
    "V68_V69_V70_V71_V72_V73_COMBINED_DOGFOOD_TEST_v0.json"
)
_PRODUCT_WEDGE_SUPPORT = (
    "docs/support/arc_series_mapping/DRAFT_ADEU_TYPED_ADJUDICATION_PRODUCT_WEDGE_v0.md"
)

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


def _v74a_note(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    lowered = normalized.lower()
    for phrase in _FORBIDDEN_AUTHORITY_PHRASES:
        if phrase in lowered and f"no {phrase}" not in lowered:
            raise ValueError(f"{field_name} may not carry projection authority")
    if "case view is source truth" in lowered:
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
            if self.projection_posture not in {"future_family_only", "rejected_out_of_scope"} and (
                self.visible_authority_state != "product_authority_missing"
            ):
                raise ValueError("product-pressure cases require missing product authority")
            if self.projection_posture == "future_family_only" and (
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
            _REQUIRED_FORBIDDEN_PROJECTION_AUTHORITIES
            - set(self.forbidden_projection_authorities)
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
        row.guardrail_ref: row
        for row in operator_projection_non_authority_guardrail.guardrail_rows
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
