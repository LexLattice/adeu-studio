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
from .candidate_ratification_review import (
    RepoCandidateRatificationFamilyCloseoutAlignment,
    RepoPostRatificationHandoff,
    RepoRatificationAmendmentScopeBoundary,
)
from .candidate_review_classification import _load_json, _surface_id
from .recursive_candidate_intake import (
    CandidateAuthorityLayer,
    CandidateSourceKind,
    CandidateSourcePresencePosture,
    OdeuLane,
)

REPO_CONTAINED_INTEGRATION_CANDIDATE_PLAN_SCHEMA = "repo_contained_integration_candidate_plan@1"
REPO_INTEGRATION_TARGET_BOUNDARY_SCHEMA = "repo_integration_target_boundary@1"
REPO_INTEGRATION_NON_RELEASE_GUARDRAIL_SCHEMA = "repo_integration_non_release_guardrail@1"
REPO_CONTAINED_INTEGRATION_TRIAL_RECORD_SCHEMA = "repo_contained_integration_trial_record@1"
REPO_INTEGRATION_EFFECT_SURFACE_REGISTER_SCHEMA = "repo_integration_effect_surface_register@1"
REPO_INTEGRATION_ROLLBACK_READINESS_SCHEMA = "repo_integration_rollback_readiness@1"

ContainmentPlanPosture = Literal[
    "eligible_for_containment_planning",
    "blocked_by_dissent",
    "blocked_by_evidence_gap",
    "blocked_by_scope_boundary",
    "future_family_only",
    "rejected_out_of_scope",
]
RequiredTrialPosture = Literal[
    "no_trial_selected_in_v72a",
    "dry_run_required_later",
    "local_trial_required_later",
    "trial_blocked_until_source_gap_resolved",
    "trial_blocked_until_dissent_resolved",
    "future_family_trial_only",
]
IntegrationTargetBoundaryKind = Literal[
    "docs_support_surface",
    "schema_surface",
    "validator_surface",
    "fixture_surface",
    "test_surface",
    "workflow_surface",
    "package_surface",
    "no_target_boundary",
]
IntegrationTargetResolutionKind = Literal[
    "concrete_file_ref",
    "concrete_schema_ref",
    "concrete_fixture_ref",
    "concrete_test_ref",
    "concrete_doc_ref",
    "bounded_package_surface_with_child_refs",
    "no_target_boundary",
]
IntegrationTargetPosture = Literal[
    "single_surface_bounded",
    "multi_surface_bounded",
    "target_requires_review",
    "target_blocked",
    "target_absent",
]
IntegrationChangeKind = Literal[
    "docs_support_update",
    "schema_shape_update",
    "model_validator_update",
    "fixture_reference_update",
    "test_coverage_update",
    "workflow_record_update",
    "runtime_behavior_change",
    "commit_or_release_action",
    "product_surface_change",
    "dispatch_or_runtime_permission",
    "external_contest_action",
]
IntegrationForbiddenDownstreamRole = Literal[
    "implementation_task",
    "commit_release_authority",
    "merge_authority",
    "released_truth",
    "product_authorization",
    "runtime_permission",
    "dispatch_authority",
    "external_contest_authority",
]
IntegrationNonReleasePosture = Literal[
    "no_commit_or_release_authority",
    "no_product_authorization",
    "no_runtime_permission",
    "no_dispatch_authority",
    "no_external_contest_authority",
]
ContainedIntegrationTrialPosture = Literal[
    "planned_not_executed",
    "dry_run_recorded",
    "local_trial_recorded",
    "trial_blocked",
    "trial_reverted",
    "trial_ready_for_outcome_review",
]
ContainedIntegrationTrialDiffPosture = Literal[
    "no_diff_recorded",
    "proposed_diff_recorded",
    "local_diff_observed",
    "diff_reverted",
    "diff_accepted_for_review_only",
    "diff_rejected",
    "diff_requires_later_authority",
]
IntegrationEffectSurfaceKind = Literal[
    "docs_effect",
    "schema_effect",
    "validator_effect",
    "fixture_effect",
    "test_effect",
    "workflow_effect",
    "package_effect",
    "unknown_effect",
]
IntegrationEffectPosture = Literal[
    "no_effect_observed",
    "effect_expected_not_checked",
    "effect_observed",
    "effect_blocked",
    "effect_reverted",
    "effect_requires_later_review",
]
IntegrationRollbackPosture = Literal[
    "rollback_not_required_for_docs_only",
    "rollback_plan_required",
    "rollback_plan_present",
    "rollback_verified",
    "rollback_blocked",
    "rollback_not_applicable",
]

_V71C_AMENDMENT_SCOPE_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus199/"
    "repo_ratification_amendment_scope_boundary_v199_reference.json"
)
_V71C_HANDOFF_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus199/"
    "repo_post_ratification_handoff_v199_reference.json"
)
_V71C_CLOSEOUT_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus199/"
    "repo_candidate_ratification_family_closeout_alignment_v199_reference.json"
)

_FORBIDDEN_V72A_AUTHORITY_TERMS = (
    "trial executed",
    "dry run recorded",
    "local trial recorded",
    "local write accepted",
    "accepted diff",
    "diff accepted",
    "commit authority",
    "merge authority",
    "release authority",
    "released truth",
    "product authorization",
    "runtime permission",
    "dispatch authority",
    "external contest authority",
)
_V72A_FORBIDDEN_DOWNSTREAM_SET: set[IntegrationForbiddenDownstreamRole] = {
    "implementation_task",
    "commit_release_authority",
    "merge_authority",
    "released_truth",
    "product_authorization",
    "runtime_permission",
    "dispatch_authority",
    "external_contest_authority",
}
_V72A_NON_TRIAL_SUMMARY = (
    "No trial execution, no accepted diff, no commit, no release, no product "
    "authorization, no runtime permission, and no dispatch authority."
)
_V72A_NON_RELEASE_SUMMARY = (
    "No commit, no merge, no release, no released truth, no product authorization, "
    "no runtime permission, no dispatch authority, and no external contest authority."
)
_V72B_FORBIDDEN_AUTHORITY_TERMS = (
    "commit authority",
    "commit authorized",
    "merge authority",
    "merge authorized",
    "release authority",
    "release authorized",
    "released truth",
    "product authorization",
    "runtime permission",
    "dispatch authority",
    "external contest authority",
    "outcome judgment",
    "outcome review complete",
)
_V72B_NON_AUTHORITY_SUMMARY = (
    "Trial records are review-only: no accepted repository truth, no commit, "
    "no merge, no release, no product authorization, no runtime permission, "
    "no dispatch authority, and no V73 outcome review."
)


def _v72a_note(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    lowered = normalized.lower()
    if any(term in lowered for term in _FORBIDDEN_V72A_AUTHORITY_TERMS):
        raise ValueError(f"{field_name} may not carry trial or downstream authority")
    return normalized


def _v72a_non_trial_summary(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    lowered = normalized.lower()
    required = ("no trial", "no accepted diff", "no commit", "no release", "no product")
    missing = [phrase for phrase in required if phrase not in lowered]
    if missing:
        raise ValueError(f"{field_name} must state {', '.join(missing)}")
    if "trial executed" in lowered or "release authorized" in lowered:
        raise ValueError(f"{field_name} may not claim trial execution or release")
    return normalized


def _v72a_non_release_summary(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    lowered = normalized.lower()
    required = (
        "no commit",
        "no merge",
        "no release",
        "no released truth",
        "no product",
        "no runtime",
        "no dispatch",
    )
    missing = [phrase for phrase in required if phrase not in lowered]
    if missing:
        raise ValueError(f"{field_name} must state {', '.join(missing)}")
    if "release authorized" in lowered or "merge authorized" in lowered:
        raise ValueError(f"{field_name} may not authorize release or merge")
    return normalized


def _v72b_note(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    lowered = normalized.lower()
    if any(term in lowered for term in _V72B_FORBIDDEN_AUTHORITY_TERMS):
        raise ValueError(f"{field_name} may not carry downstream authority")
    return normalized


def _v72b_non_authority_summary(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    lowered = normalized.lower()
    required = (
        "no accepted repository truth",
        "no commit",
        "no merge",
        "no release",
        "no product",
        "no runtime",
        "no dispatch",
        "no v73 outcome review",
    )
    missing = [phrase for phrase in required if phrase not in lowered]
    if missing:
        raise ValueError(f"{field_name} must state {', '.join(missing)}")
    if any(term in lowered for term in ("commit authorized", "release authorized")):
        raise ValueError(f"{field_name} may not authorize downstream action")
    return normalized


class RepoIntegrationSourceRow(_CartographyBase):
    source_ref: str
    source_kind: CandidateSourceKind
    authority_layer: CandidateAuthorityLayer
    source_status: SourceStatus
    source_presence_posture: CandidateSourcePresencePosture
    source_horizon: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_source(self) -> RepoIntegrationSourceRow:
        object.__setattr__(self, "source_ref", _repo_ref(self.source_ref, field_name="source_ref"))
        object.__setattr__(
            self,
            "source_horizon",
            _v72a_note(self.source_horizon, field_name="source_horizon"),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _v72a_note(self.limitation_note, field_name="limitation_note"),
        )
        if (
            self.source_status == "integrated_shaping_source"
            and self.source_presence_posture != "present"
        ):
            raise ValueError("integrated integration sources must have presence posture present")
        if self.source_ref.startswith("docs/support/") and self.authority_layer == "lock":
            raise ValueError("support-layer source cannot be marked as lock authority")
        return self


class RepoContainedIntegrationCandidatePlanRow(_CartographyBase):
    plan_ref: str
    candidate_ref: str
    integration_source_refs: list[str] = Field(min_length=1)
    source_handoff_refs: list[str] = Field(default_factory=list)
    ratification_refs: list[str] = Field(default_factory=list)
    amendment_scope_refs: list[str] = Field(default_factory=list)
    target_boundary_refs: list[str] = Field(default_factory=list)
    containment_plan_posture: ContainmentPlanPosture
    required_trial_posture: RequiredTrialPosture
    rollback_requirement: str
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    guardrail_refs: list[str] = Field(default_factory=list)
    blocker_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_plan_row(self) -> RepoContainedIntegrationCandidatePlanRow:
        object.__setattr__(self, "plan_ref", _non_empty(self.plan_ref, field_name="plan_ref"))
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        object.__setattr__(
            self,
            "integration_source_refs",
            _sorted_unique(self.integration_source_refs, field_name="integration_source_refs"),
        )
        object.__setattr__(
            self,
            "source_handoff_refs",
            _sorted_unique(self.source_handoff_refs, field_name="source_handoff_refs"),
        )
        object.__setattr__(
            self,
            "ratification_refs",
            _sorted_unique(self.ratification_refs, field_name="ratification_refs"),
        )
        object.__setattr__(
            self,
            "amendment_scope_refs",
            _sorted_unique(self.amendment_scope_refs, field_name="amendment_scope_refs"),
        )
        object.__setattr__(
            self,
            "target_boundary_refs",
            _sorted_unique(self.target_boundary_refs, field_name="target_boundary_refs"),
        )
        object.__setattr__(
            self, "odeu_lanes", _sorted_unique(self.odeu_lanes, field_name="odeu_lanes")
        )
        object.__setattr__(
            self, "guardrail_refs", _sorted_unique(self.guardrail_refs, field_name="guardrail_refs")
        )
        object.__setattr__(
            self, "blocker_refs", _sorted_unique(self.blocker_refs, field_name="blocker_refs")
        )
        object.__setattr__(
            self,
            "rollback_requirement",
            _v72a_note(self.rollback_requirement, field_name="rollback_requirement"),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _v72a_note(self.limitation_note, field_name="limitation_note"),
        )
        if self.containment_plan_posture == "eligible_for_containment_planning":
            missing_fields = [
                field_name
                for field_name, values in (
                    ("source_handoff_refs", self.source_handoff_refs),
                    ("ratification_refs", self.ratification_refs),
                    ("amendment_scope_refs", self.amendment_scope_refs),
                    ("target_boundary_refs", self.target_boundary_refs),
                    ("guardrail_refs", self.guardrail_refs),
                )
                if not values
            ]
            if missing_fields:
                raise ValueError(f"eligible containment plans require {missing_fields}")
            if not self.rollback_requirement:
                raise ValueError("eligible containment plans require rollback requirement")
            if self.required_trial_posture not in {
                "dry_run_required_later",
                "local_trial_required_later",
            }:
                raise ValueError("eligible containment plans require a later trial requirement")
            if self.blocker_refs:
                raise ValueError("eligible containment plans cannot carry blocker refs")
        if not self.guardrail_refs:
            raise ValueError("containment plans require guardrail refs")
        if self.containment_plan_posture == "blocked_by_dissent":
            if not self.blocker_refs and "dissent" not in self.limitation_note.lower():
                raise ValueError("blocked plans must identify blocker refs or blocker note")
            if self.required_trial_posture != "trial_blocked_until_dissent_resolved":
                raise ValueError("dissent-blocked plans must block trial until dissent resolves")
        if self.containment_plan_posture == "blocked_by_evidence_gap":
            if not self.blocker_refs and "gap" not in self.limitation_note.lower():
                raise ValueError("blocked plans must identify blocker refs or blocker note")
            if self.required_trial_posture != "trial_blocked_until_source_gap_resolved":
                raise ValueError("gap-blocked plans must block trial until source gaps resolve")
        if self.containment_plan_posture == "blocked_by_scope_boundary":
            if not self.blocker_refs and "scope" not in self.limitation_note.lower():
                raise ValueError("blocked plans must identify blocker refs or blocker note")
            if self.required_trial_posture not in {
                "no_trial_selected_in_v72a",
                "future_family_trial_only",
            }:
                raise ValueError("scope-blocked plans cannot select a later local trial")
        if self.containment_plan_posture == "future_family_only":
            if self.required_trial_posture not in {
                "future_family_trial_only",
                "no_trial_selected_in_v72a",
            }:
                raise ValueError("future-family-only plans cannot select V72-A trial posture")
        return self


class RepoContainedIntegrationCandidatePlan(_CartographyBase):
    schema: Literal["repo_contained_integration_candidate_plan@1"] = (
        REPO_CONTAINED_INTEGRATION_CANDIDATE_PLAN_SCHEMA
    )
    containment_plan_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    upstream_handoff_register_id: str
    amendment_scope_boundary_id: str
    family_closeout_alignment_id: str
    integration_source_rows: list[RepoIntegrationSourceRow] = Field(min_length=1)
    candidate_input_refs: list[str] = Field(min_length=1)
    plan_rows: list[RepoContainedIntegrationCandidatePlanRow] = Field(min_length=1)
    non_trial_summary: str

    @model_validator(mode="after")
    def _validate_plan(self) -> RepoContainedIntegrationCandidatePlan:
        object.__setattr__(
            self,
            "containment_plan_id",
            _non_empty(self.containment_plan_id, field_name="containment_plan_id"),
        )
        object.__setattr__(self, "review_id", _non_empty(self.review_id, field_name="review_id"))
        object.__setattr__(
            self, "snapshot_id", _non_empty(self.snapshot_id, field_name="snapshot_id")
        )
        object.__setattr__(
            self, "source_set_id", _non_empty(self.source_set_id, field_name="source_set_id")
        )
        object.__setattr__(
            self,
            "upstream_handoff_register_id",
            _non_empty(
                self.upstream_handoff_register_id,
                field_name="upstream_handoff_register_id",
            ),
        )
        object.__setattr__(
            self,
            "amendment_scope_boundary_id",
            _non_empty(self.amendment_scope_boundary_id, field_name="amendment_scope_boundary_id"),
        )
        object.__setattr__(
            self,
            "family_closeout_alignment_id",
            _non_empty(
                self.family_closeout_alignment_id,
                field_name="family_closeout_alignment_id",
            ),
        )
        object.__setattr__(
            self,
            "integration_source_rows",
            _sorted_unique_by_ref(
                self.integration_source_rows,
                attr="source_ref",
                field_name="integration_source_rows",
            ),
        )
        object.__setattr__(
            self,
            "candidate_input_refs",
            _sorted_unique(self.candidate_input_refs, field_name="candidate_input_refs"),
        )
        object.__setattr__(
            self,
            "plan_rows",
            _sorted_unique_by_ref(self.plan_rows, attr="plan_ref", field_name="plan_rows"),
        )
        object.__setattr__(
            self,
            "non_trial_summary",
            _v72a_non_trial_summary(self.non_trial_summary, field_name="non_trial_summary"),
        )
        known_sources = {row.source_ref for row in self.integration_source_rows}
        for row in self.plan_rows:
            missing_sources = sorted(set(row.integration_source_refs) - known_sources)
            if missing_sources:
                raise ValueError(
                    f"plan rows must reference known integration sources: {missing_sources}"
                )
            if row.candidate_ref not in self.candidate_input_refs:
                raise ValueError("plan rows must reference candidate_input_refs")
            if (
                row.candidate_ref == "candidate:internal:typed_adjudication_product_wedge"
                and row.containment_plan_posture == "eligible_for_containment_planning"
            ):
                raise ValueError("product wedge cannot be routed to contained integration")
        expected_id = _surface_id(
            "repo_contained_integration_candidate_plan",
            REPO_CONTAINED_INTEGRATION_CANDIDATE_PLAN_SCHEMA,
            self.model_dump(mode="json"),
            "containment_plan_id",
        )
        if self.containment_plan_id != expected_id:
            raise ValueError("containment_plan_id must match canonical full payload hash identity")
        return self


class RepoIntegrationTargetBoundaryRow(_CartographyBase):
    target_boundary_ref: str
    candidate_ref: str
    target_boundary_kind: IntegrationTargetBoundaryKind
    target_resolution_kind: IntegrationTargetResolutionKind
    target_refs: list[str] = Field(default_factory=list)
    target_posture: IntegrationTargetPosture
    allowed_change_kinds: list[IntegrationChangeKind] = Field(default_factory=list)
    forbidden_change_kinds: list[IntegrationChangeKind] = Field(min_length=1)
    source_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_target_boundary_row(self) -> RepoIntegrationTargetBoundaryRow:
        object.__setattr__(
            self,
            "target_boundary_ref",
            _non_empty(self.target_boundary_ref, field_name="target_boundary_ref"),
        )
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        object.__setattr__(
            self,
            "target_refs",
            sorted(_repo_ref(value, field_name="target_refs") for value in self.target_refs),
        )
        if len(set(self.target_refs)) != len(self.target_refs):
            raise ValueError("target_refs values must be unique")
        object.__setattr__(
            self,
            "allowed_change_kinds",
            _sorted_unique(self.allowed_change_kinds, field_name="allowed_change_kinds"),
        )
        object.__setattr__(
            self,
            "forbidden_change_kinds",
            _sorted_unique(self.forbidden_change_kinds, field_name="forbidden_change_kinds"),
        )
        object.__setattr__(
            self, "source_refs", _sorted_unique(self.source_refs, field_name="source_refs")
        )
        object.__setattr__(
            self,
            "limitation_note",
            _v72a_note(self.limitation_note, field_name="limitation_note"),
        )
        if self.target_boundary_kind == "no_target_boundary":
            if self.target_resolution_kind != "no_target_boundary":
                raise ValueError("no_target_boundary rows require no_target_boundary resolution")
            if self.target_refs:
                raise ValueError("no_target_boundary rows cannot carry concrete target refs")
            if self.target_posture != "target_absent":
                raise ValueError("no_target_boundary rows require target_absent posture")
        else:
            if not self.target_refs:
                raise ValueError("non-empty target_refs required for selected target boundary")
            if self.target_resolution_kind == "no_target_boundary":
                raise ValueError(
                    "selected target boundary cannot use no_target_boundary resolution"
                )
            if not self.forbidden_change_kinds:
                raise ValueError("target boundaries require forbidden change kinds")
        if self.target_boundary_kind == "package_surface":
            if self.target_resolution_kind != "bounded_package_surface_with_child_refs":
                raise ValueError("package_surface requires bounded child target resolution")
            if not self.target_refs:
                raise ValueError("package_surface requires concrete child refs")
        return self


class RepoIntegrationTargetBoundary(_CartographyBase):
    schema: Literal["repo_integration_target_boundary@1"] = REPO_INTEGRATION_TARGET_BOUNDARY_SCHEMA
    target_boundary_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    containment_plan_id: str
    target_boundary_rows: list[RepoIntegrationTargetBoundaryRow] = Field(min_length=1)
    non_trial_summary: str

    @model_validator(mode="after")
    def _validate_target_boundary(self) -> RepoIntegrationTargetBoundary:
        object.__setattr__(
            self,
            "target_boundary_id",
            _non_empty(self.target_boundary_id, field_name="target_boundary_id"),
        )
        object.__setattr__(self, "review_id", _non_empty(self.review_id, field_name="review_id"))
        object.__setattr__(
            self, "snapshot_id", _non_empty(self.snapshot_id, field_name="snapshot_id")
        )
        object.__setattr__(
            self, "source_set_id", _non_empty(self.source_set_id, field_name="source_set_id")
        )
        object.__setattr__(
            self,
            "containment_plan_id",
            _non_empty(self.containment_plan_id, field_name="containment_plan_id"),
        )
        object.__setattr__(
            self,
            "target_boundary_rows",
            _sorted_unique_by_ref(
                self.target_boundary_rows,
                attr="target_boundary_ref",
                field_name="target_boundary_rows",
            ),
        )
        object.__setattr__(
            self,
            "non_trial_summary",
            _v72a_non_trial_summary(self.non_trial_summary, field_name="non_trial_summary"),
        )
        expected_id = _surface_id(
            "repo_integration_target_boundary",
            REPO_INTEGRATION_TARGET_BOUNDARY_SCHEMA,
            self.model_dump(mode="json"),
            "target_boundary_id",
        )
        if self.target_boundary_id != expected_id:
            raise ValueError("target_boundary_id must match canonical full payload hash identity")
        return self


class RepoIntegrationNonReleaseGuardrailRow(_CartographyBase):
    guardrail_ref: str
    candidate_ref: str
    plan_refs: list[str] = Field(min_length=1)
    forbidden_downstream_roles: list[IntegrationForbiddenDownstreamRole] = Field(min_length=1)
    non_release_posture: IntegrationNonReleasePosture
    required_later_authority: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_guardrail_row(self) -> RepoIntegrationNonReleaseGuardrailRow:
        object.__setattr__(
            self, "guardrail_ref", _non_empty(self.guardrail_ref, field_name="guardrail_ref")
        )
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        object.__setattr__(
            self, "plan_refs", _sorted_unique(self.plan_refs, field_name="plan_refs")
        )
        object.__setattr__(
            self,
            "forbidden_downstream_roles",
            _sorted_unique(
                self.forbidden_downstream_roles, field_name="forbidden_downstream_roles"
            ),
        )
        object.__setattr__(
            self,
            "required_later_authority",
            _v72a_note(self.required_later_authority, field_name="required_later_authority"),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _v72a_note(self.limitation_note, field_name="limitation_note"),
        )
        missing_forbidden = sorted(
            _V72A_FORBIDDEN_DOWNSTREAM_SET - set(self.forbidden_downstream_roles)
        )
        if missing_forbidden:
            raise ValueError(f"guardrails must forbid downstream roles: {missing_forbidden}")
        return self


class RepoIntegrationNonReleaseGuardrail(_CartographyBase):
    schema: Literal["repo_integration_non_release_guardrail@1"] = (
        REPO_INTEGRATION_NON_RELEASE_GUARDRAIL_SCHEMA
    )
    non_release_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    containment_plan_id: str
    guardrail_rows: list[RepoIntegrationNonReleaseGuardrailRow] = Field(min_length=1)
    non_release_summary: str

    @model_validator(mode="after")
    def _validate_guardrail(self) -> RepoIntegrationNonReleaseGuardrail:
        object.__setattr__(
            self,
            "non_release_guardrail_id",
            _non_empty(self.non_release_guardrail_id, field_name="non_release_guardrail_id"),
        )
        object.__setattr__(self, "review_id", _non_empty(self.review_id, field_name="review_id"))
        object.__setattr__(
            self, "snapshot_id", _non_empty(self.snapshot_id, field_name="snapshot_id")
        )
        object.__setattr__(
            self, "source_set_id", _non_empty(self.source_set_id, field_name="source_set_id")
        )
        object.__setattr__(
            self,
            "containment_plan_id",
            _non_empty(self.containment_plan_id, field_name="containment_plan_id"),
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
            "non_release_summary",
            _v72a_non_release_summary(self.non_release_summary, field_name="non_release_summary"),
        )
        expected_id = _surface_id(
            "repo_integration_non_release_guardrail",
            REPO_INTEGRATION_NON_RELEASE_GUARDRAIL_SCHEMA,
            self.model_dump(mode="json"),
            "non_release_guardrail_id",
        )
        if self.non_release_guardrail_id != expected_id:
            raise ValueError(
                "non_release_guardrail_id must match canonical full payload hash identity"
            )
        return self


def validate_v72a_contained_integration_review_bundle(
    *,
    amendment_scope_boundary: RepoRatificationAmendmentScopeBoundary,
    post_ratification_handoff: RepoPostRatificationHandoff,
    family_closeout_alignment: RepoCandidateRatificationFamilyCloseoutAlignment,
    contained_integration_candidate_plan: RepoContainedIntegrationCandidatePlan,
    integration_target_boundary: RepoIntegrationTargetBoundary,
    integration_non_release_guardrail: RepoIntegrationNonReleaseGuardrail,
) -> None:
    if (
        post_ratification_handoff.amendment_scope_boundary_id
        != amendment_scope_boundary.amendment_scope_boundary_id
    ):
        raise ValueError("V71-C handoff must reference amendment scope boundary")
    if (
        contained_integration_candidate_plan.upstream_handoff_register_id
        != post_ratification_handoff.post_ratification_handoff_id
    ):
        raise ValueError("containment plan must reference V71-C handoff register")
    if (
        contained_integration_candidate_plan.amendment_scope_boundary_id
        != amendment_scope_boundary.amendment_scope_boundary_id
    ):
        raise ValueError("containment plan must reference V71-C amendment scope boundary")
    if (
        contained_integration_candidate_plan.family_closeout_alignment_id
        != family_closeout_alignment.family_closeout_alignment_id
    ):
        raise ValueError("containment plan must reference V71 family closeout alignment")
    if (
        integration_target_boundary.containment_plan_id
        != contained_integration_candidate_plan.containment_plan_id
    ):
        raise ValueError("target boundary must reference containment plan id")
    if (
        integration_non_release_guardrail.containment_plan_id
        != contained_integration_candidate_plan.containment_plan_id
    ):
        raise ValueError("guardrail must reference containment plan id")
    if not (
        integration_target_boundary.source_set_id
        == contained_integration_candidate_plan.source_set_id
        == integration_non_release_guardrail.source_set_id
        and integration_target_boundary.review_id
        == contained_integration_candidate_plan.review_id
        == integration_non_release_guardrail.review_id
        and integration_target_boundary.snapshot_id
        == contained_integration_candidate_plan.snapshot_id
        == integration_non_release_guardrail.snapshot_id
    ):
        raise ValueError(
            "V72-A review_id, snapshot_id, and source_set_id must match across surfaces"
        )

    handoff_rows = {row.handoff_ref: row for row in post_ratification_handoff.handoff_rows}
    amendment_rows = {
        row.amendment_scope_ref: row for row in amendment_scope_boundary.amendment_scope_rows
    }
    closeout_rows = {row.candidate_ref: row for row in family_closeout_alignment.candidate_rows}
    target_rows = {
        row.target_boundary_ref: row for row in integration_target_boundary.target_boundary_rows
    }
    guardrail_rows = {
        row.guardrail_ref: row for row in integration_non_release_guardrail.guardrail_rows
    }
    integration_source_refs = {
        row.source_ref for row in contained_integration_candidate_plan.integration_source_rows
    }
    for target in integration_target_boundary.target_boundary_rows:
        missing_sources = sorted(set(target.source_refs) - integration_source_refs)
        if missing_sources:
            raise ValueError(
                f"target boundary rows must reference known integration sources: {missing_sources}"
            )

    seen_handoffs: set[str] = set()
    seen_targets: set[str] = set()
    seen_guardrails: set[str] = set()
    for plan in contained_integration_candidate_plan.plan_rows:
        if plan.candidate_ref not in closeout_rows:
            raise ValueError("containment plans must reference V71-C family closeout candidates")
        if plan.target_boundary_refs != sorted(plan.target_boundary_refs):
            raise ValueError("target_boundary_refs must be lexicographically sorted")
        if plan.guardrail_refs != sorted(plan.guardrail_refs):
            raise ValueError("guardrail_refs must be lexicographically sorted")
        if not plan.guardrail_refs:
            raise ValueError("containment plans require guardrail refs")
        missing_targets = sorted(set(plan.target_boundary_refs) - set(target_rows))
        if missing_targets:
            raise ValueError(f"plan rows must reference known target boundaries: {missing_targets}")
        missing_guardrails = sorted(set(plan.guardrail_refs) - set(guardrail_rows))
        if missing_guardrails:
            raise ValueError(f"plan rows must reference known guardrails: {missing_guardrails}")

        for handoff_ref in plan.source_handoff_refs:
            handoff = handoff_rows.get(handoff_ref)
            if handoff is None:
                raise ValueError("plan rows must reference known V71-C handoff rows")
            seen_handoffs.add(handoff_ref)
            if plan.candidate_ref != handoff.candidate_ref:
                raise ValueError("plan candidate_ref must match V71-C handoff candidate")
            if (
                handoff.handoff_posture == "ready_for_v72_review"
                and plan.containment_plan_posture != "eligible_for_containment_planning"
            ):
                raise ValueError("ready V71-C handoffs require eligible containment plans")
            if (
                handoff.handoff_posture != "ready_for_v72_review"
                and plan.containment_plan_posture == "eligible_for_containment_planning"
            ):
                raise ValueError("non-ready V71-C handoffs cannot become eligible")
            if handoff.carried_forward_dissent_refs and plan.containment_plan_posture not in {
                "blocked_by_dissent",
                "future_family_only",
            }:
                raise ValueError("dissent-bearing handoffs must remain blocked or future-family")
            if handoff.carried_forward_gap_refs and plan.containment_plan_posture not in {
                "blocked_by_dissent",
                "blocked_by_evidence_gap",
                "future_family_only",
            }:
                raise ValueError("gap-bearing handoffs must remain blocked or future-family")
        for amendment_ref in plan.amendment_scope_refs:
            amendment = amendment_rows.get(amendment_ref)
            if amendment is None:
                raise ValueError("plan rows must reference known amendment scope rows")
            if amendment.candidate_ref != plan.candidate_ref:
                raise ValueError("plan candidate_ref must match amendment scope candidate")
        for target_ref in plan.target_boundary_refs:
            seen_targets.add(target_ref)
            target = target_rows[target_ref]
            if target.candidate_ref != plan.candidate_ref:
                raise ValueError("target boundary candidate_ref must match plan candidate_ref")
            if plan.containment_plan_posture == "future_family_only" and (
                target.target_boundary_kind != "no_target_boundary"
                or target.target_posture != "target_absent"
            ):
                raise ValueError("future-family-only plans cannot carry concrete target boundary")
            if plan.containment_plan_posture == "eligible_for_containment_planning" and (
                target.target_boundary_kind == "no_target_boundary"
                or target.target_posture == "target_absent"
            ):
                raise ValueError("eligible containment plans require concrete target boundary")
        for guardrail_ref in plan.guardrail_refs:
            seen_guardrails.add(guardrail_ref)
            guardrail = guardrail_rows[guardrail_ref]
            if guardrail.candidate_ref != plan.candidate_ref:
                raise ValueError("guardrail candidate_ref must match plan candidate_ref")
            if plan.plan_ref not in guardrail.plan_refs:
                raise ValueError("guardrail plan_refs must include the plan row")

    missing_handoffs = sorted(set(handoff_rows) - seen_handoffs)
    if missing_handoffs:
        raise ValueError(f"containment plans must cover every V71-C handoff: {missing_handoffs}")
    orphan_targets = sorted(set(target_rows) - seen_targets)
    if orphan_targets:
        raise ValueError(f"target boundary rows must be referenced by plan rows: {orphan_targets}")
    orphan_guardrails = sorted(set(guardrail_rows) - seen_guardrails)
    if orphan_guardrails:
        raise ValueError(f"guardrail rows must be referenced by plan rows: {orphan_guardrails}")


def _integration_source_rows() -> list[RepoIntegrationSourceRow]:
    return [
        RepoIntegrationSourceRow(
            source_ref="apps/api/fixtures/repo_description/vnext_plus199/repo_candidate_ratification_family_closeout_alignment_v199_reference.json",
            source_kind="fixture_file",
            authority_layer="fixture",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            source_horizon="V71-C family closeout alignment fixture.",
            limitation_note="Fixture is consumed as source-bound V72-A input only.",
        ),
        RepoIntegrationSourceRow(
            source_ref="apps/api/fixtures/repo_description/vnext_plus199/repo_post_ratification_handoff_v199_reference.json",
            source_kind="fixture_file",
            authority_layer="fixture",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            source_horizon="V71-C post-ratification handoff fixture.",
            limitation_note="Fixture is consumed as source-bound V72-A input only.",
        ),
        RepoIntegrationSourceRow(
            source_ref="apps/api/fixtures/repo_description/vnext_plus199/repo_ratification_amendment_scope_boundary_v199_reference.json",
            source_kind="fixture_file",
            authority_layer="fixture",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            source_horizon="V71-C amendment-scope fixture.",
            limitation_note="Fixture is consumed as source-bound V72-A input only.",
        ),
        RepoIntegrationSourceRow(
            source_ref="artifacts/agent_harness/v199/evidence_inputs/v71_family_closeout_alignment_v199.json",
            source_kind="evidence_artifact",
            authority_layer="closeout_evidence",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            source_horizon="V71 family closeout alignment evidence.",
            limitation_note="Closeout evidence is consumed without granting V72 execution.",
        ),
        RepoIntegrationSourceRow(
            source_ref="artifacts/agent_harness/v199/evidence_inputs/v71c_candidate_ratification_closeout_evidence_v199.json",
            source_kind="evidence_artifact",
            authority_layer="closeout_evidence",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            source_horizon="V71-C candidate ratification closeout evidence.",
            limitation_note="Closeout evidence is consumed without granting V72 execution.",
        ),
        RepoIntegrationSourceRow(
            source_ref="docs/support/arc_series_mapping/V68_V69_V70_V71_COMBINED_DOGFOOD_TEST_v0.json",
            source_kind="support_doc",
            authority_layer="support",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            source_horizon="Combined V68-V71 dogfood support result.",
            limitation_note="Support result shapes V72-A without lock authority.",
        ),
    ]


def _load_v71c_amendment_scope(repo_root: Path) -> RepoRatificationAmendmentScopeBoundary:
    return RepoRatificationAmendmentScopeBoundary.model_validate(
        _load_json(repo_root, _V71C_AMENDMENT_SCOPE_FIXTURE)
    )


def _load_v71c_handoff(repo_root: Path) -> RepoPostRatificationHandoff:
    return RepoPostRatificationHandoff.model_validate(_load_json(repo_root, _V71C_HANDOFF_FIXTURE))


def _load_v71c_closeout(repo_root: Path) -> RepoCandidateRatificationFamilyCloseoutAlignment:
    return RepoCandidateRatificationFamilyCloseoutAlignment.model_validate(
        _load_json(repo_root, _V71C_CLOSEOUT_FIXTURE)
    )


def derive_v72a_repo_contained_integration_candidate_plan(
    *,
    repo_root: Path,
    amendment_scope_boundary: RepoRatificationAmendmentScopeBoundary | None = None,
    post_ratification_handoff: RepoPostRatificationHandoff | None = None,
    family_closeout_alignment: RepoCandidateRatificationFamilyCloseoutAlignment | None = None,
) -> RepoContainedIntegrationCandidatePlan:
    amendment_scope = amendment_scope_boundary or _load_v71c_amendment_scope(repo_root)
    handoff = post_ratification_handoff or _load_v71c_handoff(repo_root)
    closeout = family_closeout_alignment or _load_v71c_closeout(repo_root)
    source_refs = [row.source_ref for row in _integration_source_rows()]
    rows = [
        RepoContainedIntegrationCandidatePlanRow(
            plan_ref="plan:v72a:odeu-diff:blocked-by-dissent",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            integration_source_refs=source_refs,
            source_handoff_refs=["handoff:v71c:odeu-diff:blocked-by-dissent"],
            ratification_refs=["ratification:v71b:odeu-diff:deferred-with-dissent"],
            amendment_scope_refs=["amendment:v71c:odeu-diff:blocked-by-dissent"],
            target_boundary_refs=["target:v72a:odeu-diff:no-target"],
            containment_plan_posture="blocked_by_dissent",
            required_trial_posture="trial_blocked_until_dissent_resolved",
            rollback_requirement="No trial selected while dissent remains unresolved.",
            odeu_lanes=["deontic", "epistemic", "ontological"],
            guardrail_refs=["guardrail:v72a:odeu-diff:no-integration"],
            blocker_refs=[
                "dissent:v71b:odeu-diff:minority-preserved",
                "gap:v70b:odeu-diff:missing-counterevidence",
            ],
            limitation_note="Dissent and evidence gap block containment planning.",
        ),
        RepoContainedIntegrationCandidatePlanRow(
            plan_ref="plan:v72a:product-wedge:future-family",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            integration_source_refs=source_refs,
            source_handoff_refs=["handoff:v71c:product-wedge:future-family"],
            ratification_refs=["ratification:v71b:product-wedge:future-family"],
            amendment_scope_refs=["amendment:v71c:product-wedge:future-family"],
            target_boundary_refs=["target:v72a:product-wedge:no-target"],
            containment_plan_posture="future_family_only",
            required_trial_posture="future_family_trial_only",
            rollback_requirement="No V72-A trial selected for future-family product pressure.",
            odeu_lanes=["deontic", "epistemic", "ontological", "utility"],
            guardrail_refs=["guardrail:v72a:product-wedge:future-family"],
            blocker_refs=[
                "gap:v70b:product-wedge:single-source-overclaim",
                "gap:v70b:product-wedge:v74-boundary",
            ],
            limitation_note="Product pressure remains future-family only.",
        ),
        RepoContainedIntegrationCandidatePlanRow(
            plan_ref="plan:v72a:self-evidencing:schema-containment",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            integration_source_refs=source_refs,
            source_handoff_refs=["handoff:v71c:self-evidencing:v72-review"],
            ratification_refs=["ratification:v71b:self-evidencing:source-bound-validity"],
            amendment_scope_refs=["amendment:v71c:self-evidencing:schema-review"],
            target_boundary_refs=["target:v72a:self-evidencing:schema-surface"],
            containment_plan_posture="eligible_for_containment_planning",
            required_trial_posture="dry_run_required_later",
            rollback_requirement="Later dry-run review must preserve explicit rollback path.",
            odeu_lanes=["deontic", "epistemic", "ontological"],
            guardrail_refs=["guardrail:v72a:self-evidencing:no-release"],
            blocker_refs=[],
            limitation_note="Eligible only for later schema containment review.",
        ),
    ]
    payload = {
        "schema": REPO_CONTAINED_INTEGRATION_CANDIDATE_PLAN_SCHEMA,
        "review_id": "review:v72a:contained-integration-planning",
        "snapshot_id": "vNext+200-prestart-on-main",
        "source_set_id": handoff.source_set_id,
        "upstream_handoff_register_id": handoff.post_ratification_handoff_id,
        "amendment_scope_boundary_id": amendment_scope.amendment_scope_boundary_id,
        "family_closeout_alignment_id": closeout.family_closeout_alignment_id,
        "integration_source_rows": [
            row.model_dump(mode="json")
            for row in sorted(_integration_source_rows(), key=lambda row: row.source_ref)
        ],
        "candidate_input_refs": sorted(row.candidate_ref for row in handoff.handoff_rows),
        "plan_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.plan_ref)
        ],
        "non_trial_summary": _V72A_NON_TRIAL_SUMMARY,
    }
    payload["containment_plan_id"] = _surface_id(
        "repo_contained_integration_candidate_plan",
        REPO_CONTAINED_INTEGRATION_CANDIDATE_PLAN_SCHEMA,
        payload,
        "containment_plan_id",
    )
    return RepoContainedIntegrationCandidatePlan.model_validate(payload)


def derive_v72a_repo_integration_target_boundary(
    *,
    repo_root: Path,
    contained_integration_candidate_plan: RepoContainedIntegrationCandidatePlan | None = None,
) -> RepoIntegrationTargetBoundary:
    plan = (
        contained_integration_candidate_plan
        or derive_v72a_repo_contained_integration_candidate_plan(repo_root=repo_root)
    )
    v71c_sources = [
        "apps/api/fixtures/repo_description/vnext_plus199/repo_post_ratification_handoff_v199_reference.json",
        "apps/api/fixtures/repo_description/vnext_plus199/repo_ratification_amendment_scope_boundary_v199_reference.json",
    ]
    no_change = [
        "commit_or_release_action",
        "dispatch_or_runtime_permission",
        "external_contest_action",
        "product_surface_change",
        "runtime_behavior_change",
    ]
    rows = [
        RepoIntegrationTargetBoundaryRow(
            target_boundary_ref="target:v72a:odeu-diff:no-target",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            target_boundary_kind="no_target_boundary",
            target_resolution_kind="no_target_boundary",
            target_refs=[],
            target_posture="target_absent",
            allowed_change_kinds=[],
            forbidden_change_kinds=no_change,
            source_refs=v71c_sources,
            limitation_note="Dissent-blocked candidate has no V72-A target boundary.",
        ),
        RepoIntegrationTargetBoundaryRow(
            target_boundary_ref="target:v72a:product-wedge:no-target",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            target_boundary_kind="no_target_boundary",
            target_resolution_kind="no_target_boundary",
            target_refs=[],
            target_posture="target_absent",
            allowed_change_kinds=[],
            forbidden_change_kinds=no_change,
            source_refs=v71c_sources,
            limitation_note="Product pressure has no V72-A target boundary.",
        ),
        RepoIntegrationTargetBoundaryRow(
            target_boundary_ref="target:v72a:self-evidencing:schema-surface",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            target_boundary_kind="schema_surface",
            target_resolution_kind="concrete_schema_ref",
            target_refs=[
                "packages/adeu_repo_description/schema/repo_contained_integration_candidate_plan.v1.json",
                "packages/adeu_repo_description/schema/repo_integration_non_release_guardrail.v1.json",
                "packages/adeu_repo_description/schema/repo_integration_target_boundary.v1.json",
            ],
            target_posture="multi_surface_bounded",
            allowed_change_kinds=["schema_shape_update", "test_coverage_update"],
            forbidden_change_kinds=no_change,
            source_refs=v71c_sources,
            limitation_note="Later review may consider only bounded schema surfaces.",
        ),
    ]
    payload = {
        "schema": REPO_INTEGRATION_TARGET_BOUNDARY_SCHEMA,
        "review_id": plan.review_id,
        "snapshot_id": plan.snapshot_id,
        "source_set_id": plan.source_set_id,
        "containment_plan_id": plan.containment_plan_id,
        "target_boundary_rows": [
            row.model_dump(mode="json")
            for row in sorted(rows, key=lambda row: row.target_boundary_ref)
        ],
        "non_trial_summary": _V72A_NON_TRIAL_SUMMARY,
    }
    payload["target_boundary_id"] = _surface_id(
        "repo_integration_target_boundary",
        REPO_INTEGRATION_TARGET_BOUNDARY_SCHEMA,
        payload,
        "target_boundary_id",
    )
    return RepoIntegrationTargetBoundary.model_validate(payload)


def derive_v72a_repo_integration_non_release_guardrail(
    *,
    repo_root: Path,
    contained_integration_candidate_plan: RepoContainedIntegrationCandidatePlan | None = None,
) -> RepoIntegrationNonReleaseGuardrail:
    plan = (
        contained_integration_candidate_plan
        or derive_v72a_repo_contained_integration_candidate_plan(repo_root=repo_root)
    )
    rows = [
        RepoIntegrationNonReleaseGuardrailRow(
            guardrail_ref="guardrail:v72a:odeu-diff:no-integration",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            plan_refs=["plan:v72a:odeu-diff:blocked-by-dissent"],
            forbidden_downstream_roles=sorted(_V72A_FORBIDDEN_DOWNSTREAM_SET),
            non_release_posture="no_commit_or_release_authority",
            required_later_authority="Later authority is required before any downstream action.",
            limitation_note="Blocked candidate remains outside contained integration.",
        ),
        RepoIntegrationNonReleaseGuardrailRow(
            guardrail_ref="guardrail:v72a:product-wedge:future-family",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            plan_refs=["plan:v72a:product-wedge:future-family"],
            forbidden_downstream_roles=sorted(_V72A_FORBIDDEN_DOWNSTREAM_SET),
            non_release_posture="no_product_authorization",
            required_later_authority="Future-family review is required before product work.",
            limitation_note="Product pressure remains outside contained integration.",
        ),
        RepoIntegrationNonReleaseGuardrailRow(
            guardrail_ref="guardrail:v72a:self-evidencing:no-release",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            plan_refs=["plan:v72a:self-evidencing:schema-containment"],
            forbidden_downstream_roles=sorted(_V72A_FORBIDDEN_DOWNSTREAM_SET),
            non_release_posture="no_commit_or_release_authority",
            required_later_authority="V72-B and later maintainer review are required first.",
            limitation_note="Schema containment planning does not grant downstream action.",
        ),
    ]
    payload = {
        "schema": REPO_INTEGRATION_NON_RELEASE_GUARDRAIL_SCHEMA,
        "review_id": plan.review_id,
        "snapshot_id": plan.snapshot_id,
        "source_set_id": plan.source_set_id,
        "containment_plan_id": plan.containment_plan_id,
        "guardrail_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.guardrail_ref)
        ],
        "non_release_summary": _V72A_NON_RELEASE_SUMMARY,
    }
    payload["non_release_guardrail_id"] = _surface_id(
        "repo_integration_non_release_guardrail",
        REPO_INTEGRATION_NON_RELEASE_GUARDRAIL_SCHEMA,
        payload,
        "non_release_guardrail_id",
    )
    return RepoIntegrationNonReleaseGuardrail.model_validate(payload)


def derive_v72a_repo_contained_integration_review_bundle(
    *,
    repo_root: Path,
) -> tuple[
    RepoRatificationAmendmentScopeBoundary,
    RepoPostRatificationHandoff,
    RepoCandidateRatificationFamilyCloseoutAlignment,
    RepoContainedIntegrationCandidatePlan,
    RepoIntegrationTargetBoundary,
    RepoIntegrationNonReleaseGuardrail,
]:
    amendment_scope = _load_v71c_amendment_scope(repo_root)
    handoff = _load_v71c_handoff(repo_root)
    closeout = _load_v71c_closeout(repo_root)
    plan = derive_v72a_repo_contained_integration_candidate_plan(
        repo_root=repo_root,
        amendment_scope_boundary=amendment_scope,
        post_ratification_handoff=handoff,
        family_closeout_alignment=closeout,
    )
    target_boundary = derive_v72a_repo_integration_target_boundary(
        repo_root=repo_root,
        contained_integration_candidate_plan=plan,
    )
    guardrail = derive_v72a_repo_integration_non_release_guardrail(
        repo_root=repo_root,
        contained_integration_candidate_plan=plan,
    )
    validate_v72a_contained_integration_review_bundle(
        amendment_scope_boundary=amendment_scope,
        post_ratification_handoff=handoff,
        family_closeout_alignment=closeout,
        contained_integration_candidate_plan=plan,
        integration_target_boundary=target_boundary,
        integration_non_release_guardrail=guardrail,
    )
    return amendment_scope, handoff, closeout, plan, target_boundary, guardrail


class RepoContainedIntegrationTrialRow(_CartographyBase):
    trial_ref: str
    candidate_ref: str
    plan_refs: list[str] = Field(min_length=1)
    target_boundary_refs: list[str] = Field(default_factory=list)
    trial_posture: ContainedIntegrationTrialPosture
    trial_diff_posture: ContainedIntegrationTrialDiffPosture
    active_lock_refs: list[str] = Field(default_factory=list)
    trial_evidence_refs: list[str] = Field(default_factory=list)
    observed_effect_refs: list[str] = Field(default_factory=list)
    rollback_readiness_refs: list[str] = Field(default_factory=list)
    non_release_guardrail_refs: list[str] = Field(min_length=1)
    effect_gap_refs: list[str] = Field(default_factory=list)
    carried_forward_effect_gap_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_trial_row(self) -> RepoContainedIntegrationTrialRow:
        object.__setattr__(self, "trial_ref", _non_empty(self.trial_ref, field_name="trial_ref"))
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        for field_name in (
            "plan_refs",
            "target_boundary_refs",
            "active_lock_refs",
            "trial_evidence_refs",
            "observed_effect_refs",
            "rollback_readiness_refs",
            "non_release_guardrail_refs",
            "effect_gap_refs",
            "carried_forward_effect_gap_refs",
        ):
            values = getattr(self, field_name)
            object.__setattr__(self, field_name, _sorted_unique(values, field_name=field_name))
        object.__setattr__(
            self,
            "limitation_note",
            _v72b_note(self.limitation_note, field_name="limitation_note"),
        )
        if self.trial_posture in {
            "dry_run_recorded",
            "local_trial_recorded",
            "trial_ready_for_outcome_review",
        }:
            missing = [
                field_name
                for field_name in (
                    "active_lock_refs",
                    "target_boundary_refs",
                    "trial_evidence_refs",
                    "non_release_guardrail_refs",
                )
                if not getattr(self, field_name)
            ]
            if missing:
                raise ValueError(f"recorded trial rows require {missing}")
        if self.trial_posture == "local_trial_recorded" and self.trial_diff_posture in {
            "no_diff_recorded",
            "diff_requires_later_authority",
        }:
            raise ValueError(
                "local trial rows require observed, proposed, accepted, reverted, "
                "or rejected diff posture"
            )
        if self.trial_posture == "trial_ready_for_outcome_review":
            if not self.rollback_readiness_refs:
                raise ValueError("trial-ready rows require rollback readiness refs")
            if not self.observed_effect_refs:
                raise ValueError("trial-ready rows require observed effect refs")
            missing_gap_carry = sorted(
                set(self.effect_gap_refs) - set(self.carried_forward_effect_gap_refs)
            )
            if missing_gap_carry:
                raise ValueError(
                    f"trial-ready rows must carry forward effect gaps: {missing_gap_carry}"
                )
        if self.trial_diff_posture == "diff_accepted_for_review_only":
            lowered = self.limitation_note.lower()
            if "review-only" not in lowered and "review only" not in lowered:
                raise ValueError("review-only diff acceptance must be explicit")
        return self


class RepoContainedIntegrationTrialRecord(_CartographyBase):
    schema: Literal["repo_contained_integration_trial_record@1"] = (
        REPO_CONTAINED_INTEGRATION_TRIAL_RECORD_SCHEMA
    )
    trial_record_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    containment_plan_id: str
    target_boundary_id: str
    non_release_guardrail_id: str
    trial_rows: list[RepoContainedIntegrationTrialRow] = Field(min_length=1)
    non_authority_summary: str

    @model_validator(mode="after")
    def _validate_trial_record(self) -> RepoContainedIntegrationTrialRecord:
        for field_name in (
            "trial_record_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "containment_plan_id",
            "target_boundary_id",
            "non_release_guardrail_id",
        ):
            object.__setattr__(
                self,
                field_name,
                _non_empty(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "trial_rows",
            _sorted_unique_by_ref(self.trial_rows, attr="trial_ref", field_name="trial_rows"),
        )
        object.__setattr__(
            self,
            "non_authority_summary",
            _v72b_non_authority_summary(
                self.non_authority_summary,
                field_name="non_authority_summary",
            ),
        )
        expected_id = _surface_id(
            "repo_contained_integration_trial_record",
            REPO_CONTAINED_INTEGRATION_TRIAL_RECORD_SCHEMA,
            self.model_dump(mode="json"),
            "trial_record_id",
        )
        if self.trial_record_id != expected_id:
            raise ValueError("trial_record_id must match canonical full payload hash identity")
        return self


class RepoIntegrationEffectSurfaceRow(_CartographyBase):
    effect_ref: str
    candidate_ref: str
    trial_refs: list[str] = Field(min_length=1)
    target_boundary_refs: list[str] = Field(default_factory=list)
    effect_surface_kind: IntegrationEffectSurfaceKind
    effect_posture: IntegrationEffectPosture
    observed_artifact_refs: list[str] = Field(default_factory=list)
    test_refs: list[str] = Field(default_factory=list)
    effect_gap_refs: list[str] = Field(default_factory=list)
    carried_forward_gap_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_effect_row(self) -> RepoIntegrationEffectSurfaceRow:
        object.__setattr__(self, "effect_ref", _non_empty(self.effect_ref, field_name="effect_ref"))
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        for field_name in (
            "trial_refs",
            "target_boundary_refs",
            "effect_gap_refs",
            "carried_forward_gap_refs",
        ):
            values = getattr(self, field_name)
            object.__setattr__(self, field_name, _sorted_unique(values, field_name=field_name))
        for field_name in ("observed_artifact_refs", "test_refs"):
            values = sorted(
                _repo_ref(value, field_name=field_name) for value in getattr(self, field_name)
            )
            if len(set(values)) != len(values):
                raise ValueError(f"{field_name} values must be unique")
            object.__setattr__(self, field_name, values)
        object.__setattr__(
            self,
            "limitation_note",
            _v72b_note(self.limitation_note, field_name="limitation_note"),
        )
        if self.effect_posture == "effect_observed" and not (
            self.observed_artifact_refs or self.test_refs
        ):
            raise ValueError("observed effects require observed artifact or test refs")
        if self.effect_posture in {"effect_blocked", "effect_requires_later_review"} and not (
            self.effect_gap_refs or "gap" in self.limitation_note.lower()
        ):
            raise ValueError("blocked or later-review effects require gap refs or gap note")
        return self


class RepoIntegrationEffectSurfaceRegister(_CartographyBase):
    schema: Literal["repo_integration_effect_surface_register@1"] = (
        REPO_INTEGRATION_EFFECT_SURFACE_REGISTER_SCHEMA
    )
    effect_surface_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    trial_record_id: str
    effect_rows: list[RepoIntegrationEffectSurfaceRow] = Field(min_length=1)
    non_authority_summary: str

    @model_validator(mode="after")
    def _validate_effect_register(self) -> RepoIntegrationEffectSurfaceRegister:
        for field_name in (
            "effect_surface_register_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "trial_record_id",
        ):
            object.__setattr__(
                self,
                field_name,
                _non_empty(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "effect_rows",
            _sorted_unique_by_ref(self.effect_rows, attr="effect_ref", field_name="effect_rows"),
        )
        object.__setattr__(
            self,
            "non_authority_summary",
            _v72b_non_authority_summary(
                self.non_authority_summary,
                field_name="non_authority_summary",
            ),
        )
        expected_id = _surface_id(
            "repo_integration_effect_surface_register",
            REPO_INTEGRATION_EFFECT_SURFACE_REGISTER_SCHEMA,
            self.model_dump(mode="json"),
            "effect_surface_register_id",
        )
        if self.effect_surface_register_id != expected_id:
            raise ValueError(
                "effect_surface_register_id must match canonical full payload hash identity"
            )
        return self


class RepoIntegrationRollbackReadinessRow(_CartographyBase):
    rollback_ref: str
    candidate_ref: str
    trial_refs: list[str] = Field(min_length=1)
    effect_refs: list[str] = Field(default_factory=list)
    rollback_posture: IntegrationRollbackPosture
    rollback_evidence_refs: list[str] = Field(default_factory=list)
    required_before_next_surface: bool
    limitation_note: str

    @model_validator(mode="after")
    def _validate_rollback_row(self) -> RepoIntegrationRollbackReadinessRow:
        object.__setattr__(
            self,
            "rollback_ref",
            _non_empty(self.rollback_ref, field_name="rollback_ref"),
        )
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        for field_name in ("trial_refs", "effect_refs"):
            values = getattr(self, field_name)
            object.__setattr__(self, field_name, _sorted_unique(values, field_name=field_name))
        values = sorted(
            _repo_ref(value, field_name="rollback_evidence_refs")
            for value in self.rollback_evidence_refs
        )
        if len(set(values)) != len(values):
            raise ValueError("rollback_evidence_refs values must be unique")
        object.__setattr__(self, "rollback_evidence_refs", values)
        object.__setattr__(
            self,
            "limitation_note",
            _v72b_note(self.limitation_note, field_name="limitation_note"),
        )
        if self.rollback_posture == "rollback_verified" and not self.rollback_evidence_refs:
            raise ValueError("rollback verified rows require rollback evidence refs")
        if self.rollback_posture in {"rollback_plan_required", "rollback_blocked"} and not (
            self.required_before_next_surface
        ):
            raise ValueError("required or blocked rollback must be required before next surface")
        return self


class RepoIntegrationRollbackReadiness(_CartographyBase):
    schema: Literal["repo_integration_rollback_readiness@1"] = (
        REPO_INTEGRATION_ROLLBACK_READINESS_SCHEMA
    )
    rollback_readiness_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    trial_record_id: str
    effect_surface_register_id: str
    rollback_rows: list[RepoIntegrationRollbackReadinessRow] = Field(min_length=1)
    non_authority_summary: str

    @model_validator(mode="after")
    def _validate_rollback_readiness(self) -> RepoIntegrationRollbackReadiness:
        for field_name in (
            "rollback_readiness_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
            "trial_record_id",
            "effect_surface_register_id",
        ):
            object.__setattr__(
                self,
                field_name,
                _non_empty(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "rollback_rows",
            _sorted_unique_by_ref(
                self.rollback_rows,
                attr="rollback_ref",
                field_name="rollback_rows",
            ),
        )
        object.__setattr__(
            self,
            "non_authority_summary",
            _v72b_non_authority_summary(
                self.non_authority_summary,
                field_name="non_authority_summary",
            ),
        )
        expected_id = _surface_id(
            "repo_integration_rollback_readiness",
            REPO_INTEGRATION_ROLLBACK_READINESS_SCHEMA,
            self.model_dump(mode="json"),
            "rollback_readiness_id",
        )
        if self.rollback_readiness_id != expected_id:
            raise ValueError(
                "rollback_readiness_id must match canonical full payload hash identity"
            )
        return self


def validate_v72b_contained_integration_trial_bundle(
    *,
    contained_integration_candidate_plan: RepoContainedIntegrationCandidatePlan,
    integration_target_boundary: RepoIntegrationTargetBoundary,
    integration_non_release_guardrail: RepoIntegrationNonReleaseGuardrail,
    contained_integration_trial_record: RepoContainedIntegrationTrialRecord,
    integration_effect_surface_register: RepoIntegrationEffectSurfaceRegister,
    integration_rollback_readiness: RepoIntegrationRollbackReadiness,
) -> None:
    if (
        contained_integration_trial_record.containment_plan_id
        != contained_integration_candidate_plan.containment_plan_id
    ):
        raise ValueError("trial record must reference V72-A containment plan")
    if (
        contained_integration_trial_record.target_boundary_id
        != integration_target_boundary.target_boundary_id
    ):
        raise ValueError("trial record must reference V72-A target boundary")
    if (
        contained_integration_trial_record.non_release_guardrail_id
        != integration_non_release_guardrail.non_release_guardrail_id
    ):
        raise ValueError("trial record must reference V72-A non-release guardrail")
    if (
        integration_effect_surface_register.trial_record_id
        != contained_integration_trial_record.trial_record_id
    ):
        raise ValueError("effect surface register must reference trial record")
    if (
        integration_rollback_readiness.trial_record_id
        != contained_integration_trial_record.trial_record_id
    ):
        raise ValueError("rollback readiness must reference trial record")
    if (
        integration_rollback_readiness.effect_surface_register_id
        != integration_effect_surface_register.effect_surface_register_id
    ):
        raise ValueError("rollback readiness must reference effect surface register")
    if not (
        contained_integration_trial_record.source_set_id
        == contained_integration_candidate_plan.source_set_id
        == integration_target_boundary.source_set_id
        == integration_non_release_guardrail.source_set_id
        == integration_effect_surface_register.source_set_id
        == integration_rollback_readiness.source_set_id
        and contained_integration_trial_record.snapshot_id
        == contained_integration_candidate_plan.snapshot_id
        == integration_target_boundary.snapshot_id
        == integration_non_release_guardrail.snapshot_id
        == integration_effect_surface_register.snapshot_id
        == integration_rollback_readiness.snapshot_id
    ):
        raise ValueError("V72-B source_set_id and snapshot_id must match across surfaces")

    plan_rows = {row.plan_ref: row for row in contained_integration_candidate_plan.plan_rows}
    target_rows = {
        row.target_boundary_ref: row for row in integration_target_boundary.target_boundary_rows
    }
    guardrail_rows = {
        row.guardrail_ref: row for row in integration_non_release_guardrail.guardrail_rows
    }
    trial_rows = {row.trial_ref: row for row in contained_integration_trial_record.trial_rows}
    effect_rows = {row.effect_ref: row for row in integration_effect_surface_register.effect_rows}
    rollback_rows = {row.rollback_ref: row for row in integration_rollback_readiness.rollback_rows}

    for trial in contained_integration_trial_record.trial_rows:
        for plan_ref in trial.plan_refs:
            plan = plan_rows.get(plan_ref)
            if plan is None:
                raise ValueError("trial rows must reference known V72-A plan rows")
            if plan.candidate_ref != trial.candidate_ref:
                raise ValueError("trial candidate_ref must match referenced plan rows")
            if (
                trial.trial_posture
                in {"dry_run_recorded", "local_trial_recorded", "trial_ready_for_outcome_review"}
                and plan.containment_plan_posture != "eligible_for_containment_planning"
            ):
                raise ValueError("recorded or ready trials require eligible V72-A plans")
            if (
                plan.candidate_ref == "candidate:internal:typed_adjudication_product_wedge"
                and trial.trial_posture
                not in {"planned_not_executed", "trial_blocked", "trial_reverted"}
            ):
                raise ValueError("product wedge cannot enter V72-B trial work")
        for target_ref in trial.target_boundary_refs:
            target = target_rows.get(target_ref)
            if target is None:
                raise ValueError("trial rows must reference known target boundaries")
            if target.candidate_ref != trial.candidate_ref:
                raise ValueError("trial candidate_ref must match target boundary candidate")
            if (
                trial.trial_posture
                in {"dry_run_recorded", "local_trial_recorded", "trial_ready_for_outcome_review"}
                and target.target_boundary_kind == "no_target_boundary"
            ):
                raise ValueError("recorded or ready trials require concrete target boundaries")
        for guardrail_ref in trial.non_release_guardrail_refs:
            guardrail = guardrail_rows.get(guardrail_ref)
            if guardrail is None:
                raise ValueError("trial rows must reference known non-release guardrails")
            if guardrail.candidate_ref != trial.candidate_ref:
                raise ValueError("trial candidate_ref must match guardrail candidate")
            if not set(trial.plan_refs).issubset(set(guardrail.plan_refs)):
                raise ValueError("trial plan_refs must be covered by guardrail plan_refs")
        for effect_ref in trial.observed_effect_refs:
            effect = effect_rows.get(effect_ref)
            if effect is None:
                raise ValueError("trial rows must reference known observed effect rows")
            if effect.candidate_ref != trial.candidate_ref:
                raise ValueError("trial candidate_ref must match observed effect candidate")
            if trial.trial_ref not in effect.trial_refs:
                raise ValueError("observed effect rows must reference the trial row")
        for rollback_ref in trial.rollback_readiness_refs:
            rollback = rollback_rows.get(rollback_ref)
            if rollback is None:
                raise ValueError("trial rows must reference known rollback readiness rows")
            if rollback.candidate_ref != trial.candidate_ref:
                raise ValueError("trial candidate_ref must match rollback candidate")
            if trial.trial_ref not in rollback.trial_refs:
                raise ValueError("rollback readiness rows must reference the trial row")
            if (
                trial.trial_posture == "trial_ready_for_outcome_review"
                and rollback.rollback_posture == "rollback_blocked"
            ):
                raise ValueError("trial-ready rows cannot carry blocked rollback")
        if trial.trial_posture == "trial_ready_for_outcome_review":
            blocking_effects = [
                effect_ref
                for effect_ref in trial.observed_effect_refs
                if effect_rows[effect_ref].effect_posture
                in {"effect_blocked", "effect_requires_later_review"}
                and not set(effect_rows[effect_ref].effect_gap_refs).issubset(
                    set(effect_rows[effect_ref].carried_forward_gap_refs)
                )
            ]
            if blocking_effects:
                raise ValueError(
                    f"trial-ready rows must carry effect gaps forward: {blocking_effects}"
                )

    for effect in integration_effect_surface_register.effect_rows:
        for trial_ref in effect.trial_refs:
            trial = trial_rows.get(trial_ref)
            if trial is None:
                raise ValueError("effect rows must reference known trial rows")
            if trial.candidate_ref != effect.candidate_ref:
                raise ValueError("effect candidate_ref must match trial candidate")
        for target_ref in effect.target_boundary_refs:
            target = target_rows.get(target_ref)
            if target is None:
                raise ValueError("effect rows must reference known target boundaries")
            if target.candidate_ref != effect.candidate_ref:
                raise ValueError("effect candidate_ref must match target boundary candidate")

    for rollback in integration_rollback_readiness.rollback_rows:
        for trial_ref in rollback.trial_refs:
            trial = trial_rows.get(trial_ref)
            if trial is None:
                raise ValueError("rollback rows must reference known trial rows")
            if trial.candidate_ref != rollback.candidate_ref:
                raise ValueError("rollback candidate_ref must match trial candidate")
        for effect_ref in rollback.effect_refs:
            effect = effect_rows.get(effect_ref)
            if effect is None:
                raise ValueError("rollback rows must reference known effect rows")
            if effect.candidate_ref != rollback.candidate_ref:
                raise ValueError("rollback candidate_ref must match effect candidate")


def _load_v72a_plan(repo_root: Path) -> RepoContainedIntegrationCandidatePlan:
    return RepoContainedIntegrationCandidatePlan.model_validate(
        _load_json(
            repo_root,
            "apps/api/fixtures/repo_description/vnext_plus200/"
            "repo_contained_integration_candidate_plan_v200_reference.json",
        )
    )


def _load_v72a_target_boundary(repo_root: Path) -> RepoIntegrationTargetBoundary:
    return RepoIntegrationTargetBoundary.model_validate(
        _load_json(
            repo_root,
            "apps/api/fixtures/repo_description/vnext_plus200/"
            "repo_integration_target_boundary_v200_reference.json",
        )
    )


def _load_v72a_guardrail(repo_root: Path) -> RepoIntegrationNonReleaseGuardrail:
    return RepoIntegrationNonReleaseGuardrail.model_validate(
        _load_json(
            repo_root,
            "apps/api/fixtures/repo_description/vnext_plus200/"
            "repo_integration_non_release_guardrail_v200_reference.json",
        )
    )


def derive_v72b_repo_contained_integration_trial_record(
    *,
    repo_root: Path,
    contained_integration_candidate_plan: RepoContainedIntegrationCandidatePlan | None = None,
    integration_target_boundary: RepoIntegrationTargetBoundary | None = None,
    integration_non_release_guardrail: RepoIntegrationNonReleaseGuardrail | None = None,
) -> RepoContainedIntegrationTrialRecord:
    plan = contained_integration_candidate_plan or _load_v72a_plan(repo_root)
    target = integration_target_boundary or _load_v72a_target_boundary(repo_root)
    guardrail = integration_non_release_guardrail or _load_v72a_guardrail(repo_root)
    rows = [
        RepoContainedIntegrationTrialRow(
            trial_ref="trial:v72b:odeu-diff:blocked",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            plan_refs=["plan:v72a:odeu-diff:blocked-by-dissent"],
            target_boundary_refs=[],
            trial_posture="trial_blocked",
            trial_diff_posture="no_diff_recorded",
            active_lock_refs=[],
            trial_evidence_refs=[],
            observed_effect_refs=[],
            rollback_readiness_refs=[],
            non_release_guardrail_refs=["guardrail:v72a:odeu-diff:no-integration"],
            effect_gap_refs=["gap:v70b:odeu-diff:missing-counterevidence"],
            carried_forward_effect_gap_refs=["gap:v70b:odeu-diff:missing-counterevidence"],
            limitation_note="Dissent and evidence gap keep the trial blocked.",
        ),
        RepoContainedIntegrationTrialRow(
            trial_ref="trial:v72b:product-wedge:blocked",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            plan_refs=["plan:v72a:product-wedge:future-family"],
            target_boundary_refs=[],
            trial_posture="trial_blocked",
            trial_diff_posture="no_diff_recorded",
            active_lock_refs=[],
            trial_evidence_refs=[],
            observed_effect_refs=[],
            rollback_readiness_refs=[],
            non_release_guardrail_refs=["guardrail:v72a:product-wedge:future-family"],
            effect_gap_refs=["gap:v70b:product-wedge:v74-boundary"],
            carried_forward_effect_gap_refs=["gap:v70b:product-wedge:v74-boundary"],
            limitation_note="Product pressure remains future-family only.",
        ),
        RepoContainedIntegrationTrialRow(
            trial_ref="trial:v72b:self-evidencing:dry-run",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            plan_refs=["plan:v72a:self-evidencing:schema-containment"],
            target_boundary_refs=["target:v72a:self-evidencing:schema-surface"],
            trial_posture="trial_ready_for_outcome_review",
            trial_diff_posture="diff_accepted_for_review_only",
            active_lock_refs=["docs/LOCKED_CONTINUATION_vNEXT_PLUS201.md"],
            trial_evidence_refs=[
                "apps/api/fixtures/repo_description/vnext_plus201/repo_contained_integration_trial_record_v201_reference.json",
                "packages/adeu_repo_description/tests/test_contained_integration_review_v72b.py",
            ],
            observed_effect_refs=["effect:v72b:self-evidencing:schema-surface"],
            rollback_readiness_refs=["rollback:v72b:self-evidencing:plan-present"],
            non_release_guardrail_refs=["guardrail:v72a:self-evidencing:no-release"],
            effect_gap_refs=[],
            carried_forward_effect_gap_refs=[],
            limitation_note=(
                "Diff is accepted for review-only handoff; no downstream authority is granted."
            ),
        ),
    ]
    payload = {
        "schema": REPO_CONTAINED_INTEGRATION_TRIAL_RECORD_SCHEMA,
        "review_id": "review:v72b:contained-trial-review",
        "snapshot_id": plan.snapshot_id,
        "source_set_id": plan.source_set_id,
        "containment_plan_id": plan.containment_plan_id,
        "target_boundary_id": target.target_boundary_id,
        "non_release_guardrail_id": guardrail.non_release_guardrail_id,
        "trial_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.trial_ref)
        ],
        "non_authority_summary": _V72B_NON_AUTHORITY_SUMMARY,
    }
    payload["trial_record_id"] = _surface_id(
        "repo_contained_integration_trial_record",
        REPO_CONTAINED_INTEGRATION_TRIAL_RECORD_SCHEMA,
        payload,
        "trial_record_id",
    )
    return RepoContainedIntegrationTrialRecord.model_validate(payload)


def derive_v72b_repo_integration_effect_surface_register(
    *,
    repo_root: Path,
    contained_integration_trial_record: RepoContainedIntegrationTrialRecord | None = None,
) -> RepoIntegrationEffectSurfaceRegister:
    trial = (
        contained_integration_trial_record
        or derive_v72b_repo_contained_integration_trial_record(repo_root=repo_root)
    )
    rows = [
        RepoIntegrationEffectSurfaceRow(
            effect_ref="effect:v72b:self-evidencing:schema-surface",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            trial_refs=["trial:v72b:self-evidencing:dry-run"],
            target_boundary_refs=["target:v72a:self-evidencing:schema-surface"],
            effect_surface_kind="schema_effect",
            effect_posture="effect_observed",
            observed_artifact_refs=[
                "packages/adeu_repo_description/schema/repo_contained_integration_trial_record.v1.json",
                "packages/adeu_repo_description/schema/repo_integration_effect_surface_register.v1.json",
                "packages/adeu_repo_description/schema/repo_integration_rollback_readiness.v1.json",
            ],
            test_refs=[
                "packages/adeu_repo_description/tests/test_contained_integration_review_v72b.py"
            ],
            effect_gap_refs=[],
            carried_forward_gap_refs=[],
            limitation_note="Schema effect is observed for review-only trial records.",
        )
    ]
    payload = {
        "schema": REPO_INTEGRATION_EFFECT_SURFACE_REGISTER_SCHEMA,
        "review_id": trial.review_id,
        "snapshot_id": trial.snapshot_id,
        "source_set_id": trial.source_set_id,
        "trial_record_id": trial.trial_record_id,
        "effect_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.effect_ref)
        ],
        "non_authority_summary": _V72B_NON_AUTHORITY_SUMMARY,
    }
    payload["effect_surface_register_id"] = _surface_id(
        "repo_integration_effect_surface_register",
        REPO_INTEGRATION_EFFECT_SURFACE_REGISTER_SCHEMA,
        payload,
        "effect_surface_register_id",
    )
    return RepoIntegrationEffectSurfaceRegister.model_validate(payload)


def derive_v72b_repo_integration_rollback_readiness(
    *,
    repo_root: Path,
    contained_integration_trial_record: RepoContainedIntegrationTrialRecord | None = None,
    integration_effect_surface_register: RepoIntegrationEffectSurfaceRegister | None = None,
) -> RepoIntegrationRollbackReadiness:
    trial = (
        contained_integration_trial_record
        or derive_v72b_repo_contained_integration_trial_record(repo_root=repo_root)
    )
    effect = (
        integration_effect_surface_register
        or derive_v72b_repo_integration_effect_surface_register(
            repo_root=repo_root,
            contained_integration_trial_record=trial,
        )
    )
    rows = [
        RepoIntegrationRollbackReadinessRow(
            rollback_ref="rollback:v72b:self-evidencing:plan-present",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            trial_refs=["trial:v72b:self-evidencing:dry-run"],
            effect_refs=["effect:v72b:self-evidencing:schema-surface"],
            rollback_posture="rollback_plan_present",
            rollback_evidence_refs=[
                "docs/LOCKED_CONTINUATION_vNEXT_PLUS201.md",
                "packages/adeu_repo_description/tests/test_contained_integration_review_v72b.py",
            ],
            required_before_next_surface=True,
            limitation_note="Rollback plan is present for review-only trial posture.",
        )
    ]
    payload = {
        "schema": REPO_INTEGRATION_ROLLBACK_READINESS_SCHEMA,
        "review_id": trial.review_id,
        "snapshot_id": trial.snapshot_id,
        "source_set_id": trial.source_set_id,
        "trial_record_id": trial.trial_record_id,
        "effect_surface_register_id": effect.effect_surface_register_id,
        "rollback_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.rollback_ref)
        ],
        "non_authority_summary": _V72B_NON_AUTHORITY_SUMMARY,
    }
    payload["rollback_readiness_id"] = _surface_id(
        "repo_integration_rollback_readiness",
        REPO_INTEGRATION_ROLLBACK_READINESS_SCHEMA,
        payload,
        "rollback_readiness_id",
    )
    return RepoIntegrationRollbackReadiness.model_validate(payload)


def derive_v72b_repo_contained_integration_trial_bundle(
    *,
    repo_root: Path,
) -> tuple[
    RepoContainedIntegrationCandidatePlan,
    RepoIntegrationTargetBoundary,
    RepoIntegrationNonReleaseGuardrail,
    RepoContainedIntegrationTrialRecord,
    RepoIntegrationEffectSurfaceRegister,
    RepoIntegrationRollbackReadiness,
]:
    plan = _load_v72a_plan(repo_root)
    target = _load_v72a_target_boundary(repo_root)
    guardrail = _load_v72a_guardrail(repo_root)
    trial = derive_v72b_repo_contained_integration_trial_record(
        repo_root=repo_root,
        contained_integration_candidate_plan=plan,
        integration_target_boundary=target,
        integration_non_release_guardrail=guardrail,
    )
    effect = derive_v72b_repo_integration_effect_surface_register(
        repo_root=repo_root,
        contained_integration_trial_record=trial,
    )
    rollback = derive_v72b_repo_integration_rollback_readiness(
        repo_root=repo_root,
        contained_integration_trial_record=trial,
        integration_effect_surface_register=effect,
    )
    validate_v72b_contained_integration_trial_bundle(
        contained_integration_candidate_plan=plan,
        integration_target_boundary=target,
        integration_non_release_guardrail=guardrail,
        contained_integration_trial_record=trial,
        integration_effect_surface_register=effect,
        integration_rollback_readiness=rollback,
    )
    return plan, target, guardrail, trial, effect, rollback
