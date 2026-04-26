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
from .candidate_review_classification import _load_json, _surface_id
from .candidate_review_summary import (
    RepoCandidatePreRatificationHandoff,
    RepoCandidateReviewClassificationSummary,
)
from .recursive_candidate_intake import (
    CandidateAuthorityLayer,
    CandidateSourceKind,
    CandidateSourcePresencePosture,
    OdeuLane,
    _non_authority_note,
)

REPO_CANDIDATE_RATIFICATION_REQUEST_SCHEMA = "repo_candidate_ratification_request@1"
REPO_RATIFICATION_AUTHORITY_PROFILE_SCHEMA = "repo_ratification_authority_profile@1"
REPO_RATIFICATION_REQUEST_SCOPE_BOUNDARY_SCHEMA = "repo_ratification_request_scope_boundary@1"
REPO_CANDIDATE_RATIFICATION_RECORD_SCHEMA = "repo_candidate_ratification_record@1"
REPO_REVIEW_SETTLEMENT_RECORD_SCHEMA = "repo_review_settlement_record@1"
REPO_RATIFICATION_DISSENT_REGISTER_SCHEMA = "repo_ratification_dissent_register@1"
REPO_RATIFICATION_AMENDMENT_SCOPE_BOUNDARY_SCHEMA = "repo_ratification_amendment_scope_boundary@1"
REPO_POST_RATIFICATION_HANDOFF_SCHEMA = "repo_post_ratification_handoff@1"
REPO_CANDIDATE_RATIFICATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA = (
    "repo_candidate_ratification_family_closeout_alignment@1"
)

RatificationRequestPosture = Literal[
    "eligible_for_ratification_review",
    "requires_settlement_before_ratification",
    "deferred_to_future_family",
    "rejected_out_of_scope",
]
AuthorityActorKind = Literal[
    "human_operator",
    "maintainer",
    "model_reviewer",
    "tool_validator",
    "external_reviewer",
]
AuthorityGrantSourceKind = Literal[
    "repo_lock",
    "closeout_decision",
    "maintainer_record",
    "policy_doc",
    "support_doc",
    "transcript",
    "tool_output",
]
AuthorityPosture = Literal[
    "ratification_authority",
    "settlement_authority",
    "review_only",
    "advisory_only",
    "tool_evidence_only",
    "not_authorized",
]
ReviewSignalPosture = Literal[
    "warning_only",
    "gating_blocker",
    "settlement_required",
    "evidence_required",
    "human_review_required",
    "future_family_only",
]
RatificationHorizon = Literal[
    "source_bound_candidate_validity",
    "review_conflict_settlement",
    "authority_boundary_acceptance",
    "future_family_routing",
    "integration_review_readiness",
    "utility_projection_acceptance",
]
ForbiddenDownstreamRole = Literal[
    "implementation_task",
    "contained_integration",
    "commit_release_authority",
    "product_authorization",
    "runtime_permission",
    "dispatch_authority",
    "external_contest_authority",
]
AllowedRatificationAction = Literal[
    "request_ratification_review",
    "request_settlement_review",
    "defer_to_future_family",
    "reject_out_of_scope",
]
AllowedNextReviewSurface = Literal[
    "v71b_ratification_review",
    "v71b_settlement_review",
    "future_family_review",
    "deferred_no_selection",
]
RatificationDecisionPosture = Literal["ratified", "rejected", "deferred", "out_of_scope"]
V71BAllowedNextReviewSurface = Literal[
    "v72_contained_integration_review",
    "future_family_review",
    "deferred_no_selection",
]
ReviewRelationKind = Literal[
    "conflict",
    "complementarity",
    "orthogonal",
    "duplicate",
    "unclear_relation",
]
SettlementPosture = Literal[
    "settled_for_candidate_horizon",
    "partially_settled_with_dissent",
    "blocked_by_unresolved_conflict",
    "blocked_by_unresolved_gap",
    "requires_more_evidence",
    "requires_human_review",
    "future_family_only",
]
DissentPosture = Literal[
    "no_dissent_recorded",
    "dissent_carried_forward",
    "minority_review_preserved",
    "unresolved_blocker",
    "not_applicable",
]
DissentSearchPosture = Literal[
    "searched_none_found",
    "not_searched",
    "not_applicable",
    "dissent_present",
    "unknown",
]
AllowedAmendmentScope = Literal[
    "docs_or_support_only",
    "schema_review_candidate",
    "validator_review_candidate",
    "fixture_review_candidate",
    "workflow_review_candidate",
    "future_family_only",
    "no_amendment_scope",
]
V71CAllowedNextReviewSurface = Literal[
    "v72_contained_integration_review",
    "future_family_review",
    "deferred_no_selection",
]
PostRatificationHandoffPosture = Literal[
    "ready_for_v72_review",
    "blocked_by_scope_boundary",
    "blocked_by_dissent",
    "blocked_by_evidence_gap",
    "deferred_to_future_family",
    "rejected_out_of_scope",
]
RequiredNextSurface = Literal[
    "v72_candidate_containment_planning",
    "future_family_candidate_review",
    "deferred_no_selection",
]
FamilyCandidateCloseoutPosture = Literal[
    "ratified_for_later_review",
    "deferred_with_dissent",
    "future_family_routed",
    "rejected_out_of_scope",
]

_V70C_SUMMARY_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus196/"
    "repo_candidate_review_classification_summary_v196_reference.json"
)
_V70C_HANDOFF_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus196/"
    "repo_candidate_pre_ratification_handoff_v196_reference.json"
)

_FORBIDDEN_V71A_AUTHORITY_TERMS = (
    "final ratification",
    "ratified decision",
    "candidate adoption",
    "implementation task",
    "contained integration",
    "commit release",
    "release authority",
    "product authorization",
    "runtime permission",
    "dispatch authority",
)
_FORBIDDEN_V71B_DOWNSTREAM_TERMS = (
    "implementation ticket",
    "merge permission",
    "merge authority",
    "release authority",
    "product authorization",
    "runtime permission",
    "dispatch authority",
    "external contest authority",
)
_DOWNSTREAM_FORBIDDEN_SET: set[ForbiddenDownstreamRole] = {
    "implementation_task",
    "contained_integration",
    "commit_release_authority",
    "product_authorization",
    "runtime_permission",
    "dispatch_authority",
}
_V71B_NON_INTEGRATION_GUARDRAIL = (
    "No implementation, no release, no product authorization, and no dispatch authority."
)
_V71C_NON_AUTHORITY_GUARDRAIL = (
    "No implementation, no integration, no release, no product authorization, "
    "and no dispatch authority."
)
_V71C_FORBIDDEN_SET: set[ForbiddenDownstreamRole] = {
    "implementation_task",
    "contained_integration",
    "commit_release_authority",
    "product_authorization",
    "runtime_permission",
    "dispatch_authority",
    "external_contest_authority",
}


def _v71a_note(value: str, *, field_name: str) -> str:
    normalized = _non_authority_note(value, field_name=field_name)
    lowered = normalized.lower()
    if any(term in lowered for term in _FORBIDDEN_V71A_AUTHORITY_TERMS):
        raise ValueError(f"{field_name} may not carry downstream or final ratification authority")
    return normalized


def _v71b_note(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    lowered = normalized.lower()
    if any(term in lowered for term in _FORBIDDEN_V71B_DOWNSTREAM_TERMS):
        raise ValueError(f"{field_name} may not carry downstream authority")
    return normalized


def _non_integration_guardrail(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    lowered = normalized.lower()
    required = ("no implementation", "no release", "no product", "no dispatch")
    missing = [phrase for phrase in required if phrase not in lowered]
    if missing:
        raise ValueError(f"{field_name} must state {', '.join(missing)}")
    return normalized


def _v71c_note(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    lowered = normalized.lower()
    if any(term in lowered for term in _FORBIDDEN_V71B_DOWNSTREAM_TERMS):
        raise ValueError(f"{field_name} may not carry downstream authority")
    return normalized


def _v71c_non_authority_guardrail(value: str, *, field_name: str) -> str:
    normalized = _non_empty(value, field_name=field_name)
    lowered = normalized.lower()
    required = ("no implementation", "no integration", "no release", "no product", "no dispatch")
    missing = [phrase for phrase in required if phrase not in lowered]
    if missing:
        raise ValueError(f"{field_name} must state {', '.join(missing)}")
    if "integration performed" in lowered or "release authorized" in lowered:
        raise ValueError(f"{field_name} may not perform integration or release")
    return normalized


class RepoRatificationSourceRow(_CartographyBase):
    source_ref: str
    source_kind: CandidateSourceKind
    authority_layer: CandidateAuthorityLayer
    source_status: SourceStatus
    source_presence_posture: CandidateSourcePresencePosture
    source_horizon: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_source(self) -> RepoRatificationSourceRow:
        object.__setattr__(self, "source_ref", _repo_ref(self.source_ref, field_name="source_ref"))
        object.__setattr__(
            self,
            "source_horizon",
            _v71a_note(self.source_horizon, field_name="source_horizon"),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _v71a_note(self.limitation_note, field_name="limitation_note"),
        )
        if (
            self.source_status == "integrated_shaping_source"
            and self.source_presence_posture != "present"
        ):
            raise ValueError("integrated ratification sources must have presence posture present")
        if self.source_kind in {"support_doc", "review_input"} and self.authority_layer == "lock":
            raise ValueError("support and review sources cannot be lock authority")
        if self.source_ref.startswith("docs/support/") and self.authority_layer == "lock":
            raise ValueError("support-layer source cannot be marked as lock authority")
        return self


class RepoCandidateRatificationRequestRow(_CartographyBase):
    request_ref: str
    candidate_ref: str
    ratification_source_refs: list[str] = Field(min_length=1)
    summary_refs: list[str] = Field(min_length=1, max_length=1)
    handoff_refs: list[str] = Field(min_length=1, max_length=1)
    source_handoff_refs: list[str] = Field(min_length=1, max_length=1)
    requested_ratification_horizon: RatificationHorizon
    request_posture: RatificationRequestPosture
    review_signal_posture: ReviewSignalPosture
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    authority_profile_refs: list[str] = Field(min_length=1)
    request_scope_boundary_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_request(self) -> RepoCandidateRatificationRequestRow:
        object.__setattr__(
            self, "request_ref", _non_empty(self.request_ref, field_name="request_ref")
        )
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        object.__setattr__(
            self,
            "ratification_source_refs",
            _sorted_unique(self.ratification_source_refs, field_name="ratification_source_refs"),
        )
        object.__setattr__(
            self, "summary_refs", _sorted_unique(self.summary_refs, field_name="summary_refs")
        )
        object.__setattr__(
            self, "handoff_refs", _sorted_unique(self.handoff_refs, field_name="handoff_refs")
        )
        object.__setattr__(
            self,
            "source_handoff_refs",
            _sorted_unique(self.source_handoff_refs, field_name="source_handoff_refs"),
        )
        object.__setattr__(
            self, "odeu_lanes", _sorted_unique(self.odeu_lanes, field_name="odeu_lanes")
        )
        object.__setattr__(
            self,
            "authority_profile_refs",
            _sorted_unique(self.authority_profile_refs, field_name="authority_profile_refs"),
        )
        object.__setattr__(
            self,
            "request_scope_boundary_refs",
            _sorted_unique(
                self.request_scope_boundary_refs, field_name="request_scope_boundary_refs"
            ),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _v71a_note(self.limitation_note, field_name="limitation_note"),
        )
        if (
            self.request_posture == "eligible_for_ratification_review"
            and self.review_signal_posture
            in {"gating_blocker", "settlement_required", "evidence_required", "future_family_only"}
        ):
            raise ValueError("eligible requests cannot carry blocker or future-family signal")
        if (
            self.request_posture == "requires_settlement_before_ratification"
            and self.review_signal_posture
            not in {"gating_blocker", "settlement_required", "evidence_required"}
        ):
            raise ValueError("settlement-required requests must carry a blocking review signal")
        if (
            self.request_posture == "deferred_to_future_family"
            and self.review_signal_posture != "future_family_only"
        ):
            raise ValueError("future-family deferrals must carry future_family_only signal")
        return self


class RepoCandidateRatificationRequest(_CartographyBase):
    schema: Literal["repo_candidate_ratification_request@1"] = (
        REPO_CANDIDATE_RATIFICATION_REQUEST_SCHEMA
    )
    ratification_request_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    summary_register_id: str
    handoff_register_id: str
    ratification_source_rows: list[RepoRatificationSourceRow] = Field(min_length=1)
    candidate_input_refs: list[str] = Field(min_length=1)
    request_rows: list[RepoCandidateRatificationRequestRow] = Field(min_length=1)
    non_ratification_summary: str

    @model_validator(mode="after")
    def _validate_request_register(self) -> RepoCandidateRatificationRequest:
        object.__setattr__(
            self,
            "ratification_request_id",
            _non_empty(self.ratification_request_id, field_name="ratification_request_id"),
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
            "summary_register_id",
            _non_empty(self.summary_register_id, field_name="summary_register_id"),
        )
        object.__setattr__(
            self,
            "handoff_register_id",
            _non_empty(self.handoff_register_id, field_name="handoff_register_id"),
        )
        object.__setattr__(
            self,
            "ratification_source_rows",
            _sorted_unique_by_ref(
                self.ratification_source_rows,
                attr="source_ref",
                field_name="ratification_source_rows",
            ),
        )
        object.__setattr__(
            self,
            "candidate_input_refs",
            _sorted_unique(self.candidate_input_refs, field_name="candidate_input_refs"),
        )
        object.__setattr__(
            self,
            "request_rows",
            _sorted_unique_by_ref(self.request_rows, attr="request_ref", field_name="request_rows"),
        )
        object.__setattr__(
            self,
            "non_ratification_summary",
            _v71a_note(self.non_ratification_summary, field_name="non_ratification_summary"),
        )
        known_sources = {row.source_ref for row in self.ratification_source_rows}
        for row in self.request_rows:
            missing_sources = sorted(set(row.ratification_source_refs) - known_sources)
            if missing_sources:
                raise ValueError(
                    f"request rows must reference known ratification sources: {missing_sources}"
                )
            if row.candidate_ref not in self.candidate_input_refs:
                raise ValueError("request rows must reference candidate_input_refs")
            if (
                row.candidate_ref == "candidate:internal:typed_adjudication_product_wedge"
                and row.request_posture != "deferred_to_future_family"
            ):
                raise ValueError("product wedge requests must stay deferred to future family")
        expected_id = _surface_id(
            "repo_candidate_ratification_request",
            REPO_CANDIDATE_RATIFICATION_REQUEST_SCHEMA,
            self.model_dump(mode="json"),
            "ratification_request_id",
        )
        if self.ratification_request_id != expected_id:
            raise ValueError(
                "ratification_request_id must match canonical full payload hash identity"
            )
        return self


class RepoRatificationAuthorityProfileRow(_CartographyBase):
    authority_profile_ref: str
    authority_actor_ref: str
    authority_actor_kind: AuthorityActorKind
    authority_grant_source_kind: AuthorityGrantSourceKind
    authority_source_refs: list[str] = Field(min_length=1)
    authority_posture: AuthorityPosture
    binding_layer: CandidateAuthorityLayer
    allowed_ratification_horizons: list[RatificationHorizon] = Field(default_factory=list)
    forbidden_downstream_roles: list[ForbiddenDownstreamRole] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_authority_profile(self) -> RepoRatificationAuthorityProfileRow:
        object.__setattr__(
            self,
            "authority_profile_ref",
            _non_empty(self.authority_profile_ref, field_name="authority_profile_ref"),
        )
        object.__setattr__(
            self,
            "authority_actor_ref",
            _non_empty(self.authority_actor_ref, field_name="authority_actor_ref"),
        )
        object.__setattr__(
            self,
            "authority_source_refs",
            _sorted_unique(self.authority_source_refs, field_name="authority_source_refs"),
        )
        object.__setattr__(
            self,
            "allowed_ratification_horizons",
            _sorted_unique(
                self.allowed_ratification_horizons, field_name="allowed_ratification_horizons"
            ),
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
            "limitation_note",
            _v71a_note(self.limitation_note, field_name="limitation_note"),
        )
        if self.authority_posture == "ratification_authority":
            if self.authority_actor_kind not in {"human_operator", "maintainer"}:
                raise ValueError("only human or maintainer profiles may be ratification authority")
            if self.authority_grant_source_kind not in {
                "repo_lock",
                "closeout_decision",
                "maintainer_record",
                "policy_doc",
            }:
                raise ValueError("ratification authority requires lock or maintainer grant source")
            if not self.allowed_ratification_horizons:
                raise ValueError("ratification authority must declare allowed horizons")
        if self.authority_grant_source_kind in {"support_doc", "transcript", "tool_output"} and (
            self.authority_posture in {"ratification_authority", "settlement_authority"}
            or self.binding_layer == "lock"
        ):
            raise ValueError(
                "support docs, transcripts, and tool output cannot grant ratification authority"
            )
        missing_forbidden = sorted(_DOWNSTREAM_FORBIDDEN_SET - set(self.forbidden_downstream_roles))
        if missing_forbidden:
            raise ValueError(
                f"authority profiles must forbid downstream roles: {missing_forbidden}"
            )
        return self


class RepoRatificationAuthorityProfile(_CartographyBase):
    schema: Literal["repo_ratification_authority_profile@1"] = (
        REPO_RATIFICATION_AUTHORITY_PROFILE_SCHEMA
    )
    authority_profile_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    ratification_source_refs: list[str] = Field(min_length=1)
    authority_profile_rows: list[RepoRatificationAuthorityProfileRow] = Field(min_length=1)
    non_authority_summary: str

    @model_validator(mode="after")
    def _validate_authority_profile_register(self) -> RepoRatificationAuthorityProfile:
        object.__setattr__(
            self,
            "authority_profile_id",
            _non_empty(self.authority_profile_id, field_name="authority_profile_id"),
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
            "ratification_source_refs",
            _sorted_unique(self.ratification_source_refs, field_name="ratification_source_refs"),
        )
        object.__setattr__(
            self,
            "authority_profile_rows",
            _sorted_unique_by_ref(
                self.authority_profile_rows,
                attr="authority_profile_ref",
                field_name="authority_profile_rows",
            ),
        )
        object.__setattr__(
            self,
            "non_authority_summary",
            _v71a_note(self.non_authority_summary, field_name="non_authority_summary"),
        )
        expected_id = _surface_id(
            "repo_ratification_authority_profile",
            REPO_RATIFICATION_AUTHORITY_PROFILE_SCHEMA,
            self.model_dump(mode="json"),
            "authority_profile_id",
        )
        if self.authority_profile_id != expected_id:
            raise ValueError("authority_profile_id must match canonical full payload hash identity")
        return self


class RepoRatificationRequestScopeBoundaryRow(_CartographyBase):
    request_scope_boundary_ref: str
    candidate_ref: str
    ratification_source_refs: list[str] = Field(min_length=1)
    request_refs: list[str] = Field(min_length=1)
    allowed_ratification_actions: list[AllowedRatificationAction] = Field(min_length=1)
    forbidden_downstream_roles: list[ForbiddenDownstreamRole] = Field(min_length=1)
    allowed_next_review_surfaces: list[AllowedNextReviewSurface] = Field(min_length=1)
    non_implementation_guardrail: str

    @model_validator(mode="after")
    def _validate_scope_boundary(self) -> RepoRatificationRequestScopeBoundaryRow:
        object.__setattr__(
            self,
            "request_scope_boundary_ref",
            _non_empty(self.request_scope_boundary_ref, field_name="request_scope_boundary_ref"),
        )
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        object.__setattr__(
            self,
            "ratification_source_refs",
            _sorted_unique(self.ratification_source_refs, field_name="ratification_source_refs"),
        )
        object.__setattr__(
            self, "request_refs", _sorted_unique(self.request_refs, field_name="request_refs")
        )
        object.__setattr__(
            self,
            "allowed_ratification_actions",
            _sorted_unique(
                self.allowed_ratification_actions, field_name="allowed_ratification_actions"
            ),
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
            "allowed_next_review_surfaces",
            _sorted_unique(
                self.allowed_next_review_surfaces, field_name="allowed_next_review_surfaces"
            ),
        )
        object.__setattr__(
            self,
            "non_implementation_guardrail",
            _non_empty(
                self.non_implementation_guardrail, field_name="non_implementation_guardrail"
            ),
        )
        lowered_guardrail = self.non_implementation_guardrail.lower()
        if "no implementation" not in lowered_guardrail or "no release" not in lowered_guardrail:
            raise ValueError(
                "scope boundary requires explicit no implementation/no release guardrail"
            )
        missing_forbidden = sorted(_DOWNSTREAM_FORBIDDEN_SET - set(self.forbidden_downstream_roles))
        if missing_forbidden:
            raise ValueError(f"scope boundaries must forbid downstream roles: {missing_forbidden}")
        if (
            self.candidate_ref == "candidate:internal:typed_adjudication_product_wedge"
            and "future_family_review" not in self.allowed_next_review_surfaces
        ):
            raise ValueError("product wedge scope must route to future family review")
        return self


class RepoRatificationRequestScopeBoundary(_CartographyBase):
    schema: Literal["repo_ratification_request_scope_boundary@1"] = (
        REPO_RATIFICATION_REQUEST_SCOPE_BOUNDARY_SCHEMA
    )
    request_scope_boundary_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    ratification_request_id: str
    authority_profile_id: str
    request_scope_boundary_rows: list[RepoRatificationRequestScopeBoundaryRow] = Field(min_length=1)
    non_implementation_summary: str

    @model_validator(mode="after")
    def _validate_scope_boundary_register(self) -> RepoRatificationRequestScopeBoundary:
        object.__setattr__(
            self,
            "request_scope_boundary_id",
            _non_empty(self.request_scope_boundary_id, field_name="request_scope_boundary_id"),
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
            "ratification_request_id",
            _non_empty(self.ratification_request_id, field_name="ratification_request_id"),
        )
        object.__setattr__(
            self,
            "authority_profile_id",
            _non_empty(self.authority_profile_id, field_name="authority_profile_id"),
        )
        object.__setattr__(
            self,
            "request_scope_boundary_rows",
            _sorted_unique_by_ref(
                self.request_scope_boundary_rows,
                attr="request_scope_boundary_ref",
                field_name="request_scope_boundary_rows",
            ),
        )
        object.__setattr__(
            self,
            "non_implementation_summary",
            _non_empty(self.non_implementation_summary, field_name="non_implementation_summary"),
        )
        lowered_summary = self.non_implementation_summary.lower()
        if "no implementation" not in lowered_summary or "no release" not in lowered_summary:
            raise ValueError("scope boundary summary must state no implementation and no release")
        expected_id = _surface_id(
            "repo_ratification_request_scope_boundary",
            REPO_RATIFICATION_REQUEST_SCOPE_BOUNDARY_SCHEMA,
            self.model_dump(mode="json"),
            "request_scope_boundary_id",
        )
        if self.request_scope_boundary_id != expected_id:
            raise ValueError(
                "request_scope_boundary_id must match canonical full payload hash identity"
            )
        return self


def validate_v71a_candidate_ratification_review_bundle(
    *,
    classification_summary: RepoCandidateReviewClassificationSummary,
    pre_ratification_handoff: RepoCandidatePreRatificationHandoff,
    ratification_request: RepoCandidateRatificationRequest,
    authority_profile: RepoRatificationAuthorityProfile,
    request_scope_boundary: RepoRatificationRequestScopeBoundary,
) -> None:
    if pre_ratification_handoff.review_id != classification_summary.review_id:
        raise ValueError("V70-C review_id must match across summary and handoff")
    if pre_ratification_handoff.summary_register_id != classification_summary.summary_register_id:
        raise ValueError("V70-C handoff must reference classification summary")
    if ratification_request.summary_register_id != classification_summary.summary_register_id:
        raise ValueError("ratification request must reference V70-C summary register")
    if ratification_request.handoff_register_id != pre_ratification_handoff.handoff_register_id:
        raise ValueError("ratification request must reference V70-C handoff register")
    if authority_profile.review_id != ratification_request.review_id:
        raise ValueError("authority profile review_id must match ratification request")
    if request_scope_boundary.review_id != ratification_request.review_id:
        raise ValueError("request scope boundary review_id must match ratification request")
    if authority_profile.source_set_id != ratification_request.source_set_id:
        raise ValueError("authority profile source_set_id must match ratification request")
    if request_scope_boundary.source_set_id != ratification_request.source_set_id:
        raise ValueError("request scope boundary source_set_id must match ratification request")
    if (
        request_scope_boundary.ratification_request_id
        != ratification_request.ratification_request_id
    ):
        raise ValueError("request scope boundary must reference ratification request id")
    if request_scope_boundary.authority_profile_id != authority_profile.authority_profile_id:
        raise ValueError("request scope boundary must reference authority profile id")

    source_refs = {row.source_ref for row in ratification_request.ratification_source_rows}
    missing_authority_sources = sorted(
        set(authority_profile.ratification_source_refs) - source_refs
    )
    if missing_authority_sources:
        raise ValueError(
            "authority profile must reference known ratification sources: "
            f"{missing_authority_sources}"
        )
    for profile in authority_profile.authority_profile_rows:
        missing_sources = sorted(set(profile.authority_source_refs) - source_refs)
        if missing_sources:
            raise ValueError(
                f"authority profile rows must reference known sources: {missing_sources}"
            )

    summary_rows = {row.summary_ref: row for row in classification_summary.summary_rows}
    handoff_rows = {row.handoff_ref: row for row in pre_ratification_handoff.handoff_rows}
    authority_rows = {
        row.authority_profile_ref: row for row in authority_profile.authority_profile_rows
    }
    scope_rows = {
        row.request_scope_boundary_ref: row
        for row in request_scope_boundary.request_scope_boundary_rows
    }
    seen_handoffs: set[str] = set()
    for request in ratification_request.request_rows:
        missing_summaries = sorted(set(request.summary_refs) - set(summary_rows))
        if missing_summaries:
            raise ValueError(f"request rows must reference known summary rows: {missing_summaries}")
        missing_handoffs = sorted(set(request.handoff_refs) - set(handoff_rows))
        if missing_handoffs:
            raise ValueError(f"request rows must reference known handoff rows: {missing_handoffs}")
        missing_profiles = sorted(set(request.authority_profile_refs) - set(authority_rows))
        if missing_profiles:
            raise ValueError(
                f"request rows must reference known authority profiles: {missing_profiles}"
            )
        missing_scopes = sorted(set(request.request_scope_boundary_refs) - set(scope_rows))
        if missing_scopes:
            raise ValueError(
                f"request rows must reference known scope boundaries: {missing_scopes}"
            )
        for handoff_ref in request.handoff_refs:
            if handoff_ref in seen_handoffs:
                raise ValueError("ratification requests must reference each handoff at most once")
            seen_handoffs.add(handoff_ref)
            handoff = handoff_rows[handoff_ref]
            if request.candidate_ref != handoff.candidate_ref:
                raise ValueError("request candidate_ref must match referenced handoff")
            expected_handoff_refs = [handoff_ref]
            if request.source_handoff_refs != expected_handoff_refs:
                raise ValueError(
                    "request source_handoff_refs must exactly match the source handoff row"
                )
            if request.summary_refs != [handoff.summary_ref]:
                raise ValueError(
                    "request summary_refs must exactly match referenced handoff summary"
                )
            if handoff.handoff_posture == "ready_for_v71_review" and (
                request.request_posture != "eligible_for_ratification_review"
            ):
                raise ValueError("ready V70-C handoffs require eligible V71-A requests")
            if (
                handoff.handoff_posture
                in {
                    "blocked_by_conflict",
                    "blocked_by_evidence_gap",
                    "blocked_by_authority_boundary",
                }
                and request.request_posture != "requires_settlement_before_ratification"
            ):
                raise ValueError("blocked V70-C handoffs require settlement-required requests")
            if handoff.handoff_target == "future_family_review" and (
                request.request_posture != "deferred_to_future_family"
            ):
                raise ValueError("future-family V70-C handoffs must remain deferred")
        for profile_ref in request.authority_profile_refs:
            profile = authority_rows[profile_ref]
            if (
                request.request_posture != "deferred_to_future_family"
                and profile.authority_posture
                not in {"ratification_authority", "settlement_authority"}
            ):
                raise ValueError(
                    "non-deferred requests must reference ratification or settlement authority"
                )
            if (
                request.request_posture != "deferred_to_future_family"
                and request.requested_ratification_horizon
                not in profile.allowed_ratification_horizons
            ):
                raise ValueError("request horizon must be allowed by each authority profile")
        for scope_ref in request.request_scope_boundary_refs:
            scope = scope_rows[scope_ref]
            if scope.candidate_ref != request.candidate_ref:
                raise ValueError("scope candidate_ref must match request candidate_ref")
            if set(scope.request_refs) != {request.request_ref}:
                raise ValueError("scope request_refs must match request row")
    missing_handoffs = sorted(set(handoff_rows) - seen_handoffs)
    if missing_handoffs:
        raise ValueError(
            f"ratification requests must cover every V70-C handoff: {missing_handoffs}"
        )


def _ratification_source_rows() -> list[RepoRatificationSourceRow]:
    return [
        RepoRatificationSourceRow(
            source_ref="apps/api/fixtures/repo_description/vnext_plus196/repo_candidate_pre_ratification_handoff_v196_reference.json",
            source_kind="fixture_file",
            authority_layer="fixture",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            source_horizon="V70-C pre-ratification handoff fixture.",
            limitation_note="Fixture is consumed as review input only.",
        ),
        RepoRatificationSourceRow(
            source_ref="apps/api/fixtures/repo_description/vnext_plus196/repo_candidate_review_classification_summary_v196_reference.json",
            source_kind="fixture_file",
            authority_layer="fixture",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            source_horizon="V70-C review summary fixture.",
            limitation_note="Fixture is consumed as review input only.",
        ),
        RepoRatificationSourceRow(
            source_ref="docs/LOCKED_CONTINUATION_vNEXT_PLUS197.md",
            source_kind="evidence_artifact",
            authority_layer="lock",
            source_status="integrated_shaping_source",
            source_presence_posture="present",
            source_horizon="V71-A starter lock scope.",
            limitation_note="Lock binds only request-shape work for V71-A.",
        ),
    ]


def _request_rows() -> list[RepoCandidateRatificationRequestRow]:
    return [
        RepoCandidateRatificationRequestRow(
            request_ref="request:v71a:odeu-diff:settlement-required",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            ratification_source_refs=[
                "apps/api/fixtures/repo_description/vnext_plus196/repo_candidate_pre_ratification_handoff_v196_reference.json",
                "apps/api/fixtures/repo_description/vnext_plus196/repo_candidate_review_classification_summary_v196_reference.json",
            ],
            summary_refs=["summary:v70c:odeu-diff:blocking-review"],
            handoff_refs=["handoff:v70c:odeu-diff:blocking-review"],
            source_handoff_refs=["handoff:v70c:odeu-diff:blocking-review"],
            requested_ratification_horizon="review_conflict_settlement",
            request_posture="requires_settlement_before_ratification",
            review_signal_posture="settlement_required",
            odeu_lanes=["deontic", "epistemic", "ontological"],
            authority_profile_refs=["authority:v71a:maintainer:ratification-review"],
            request_scope_boundary_refs=["scope:v71a:odeu-diff:settlement-request"],
            limitation_note="Blocked model-output comparison requests settlement review only.",
        ),
        RepoCandidateRatificationRequestRow(
            request_ref="request:v71a:product-wedge:future-family",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            ratification_source_refs=[
                "apps/api/fixtures/repo_description/vnext_plus196/repo_candidate_pre_ratification_handoff_v196_reference.json",
                "apps/api/fixtures/repo_description/vnext_plus196/repo_candidate_review_classification_summary_v196_reference.json",
            ],
            summary_refs=["summary:v70c:product-wedge:future-family"],
            handoff_refs=["handoff:v70c:product-wedge:future-family"],
            source_handoff_refs=["handoff:v70c:product-wedge:future-family"],
            requested_ratification_horizon="future_family_routing",
            request_posture="deferred_to_future_family",
            review_signal_posture="future_family_only",
            odeu_lanes=["deontic", "epistemic", "ontological", "utility"],
            authority_profile_refs=["authority:v71a:support-reviewer:advisory-only"],
            request_scope_boundary_refs=["scope:v71a:product-wedge:future-family"],
            limitation_note="Product pressure remains future-family review only.",
        ),
        RepoCandidateRatificationRequestRow(
            request_ref="request:v71a:self-evidencing:eligible",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            ratification_source_refs=[
                "apps/api/fixtures/repo_description/vnext_plus196/repo_candidate_pre_ratification_handoff_v196_reference.json",
                "apps/api/fixtures/repo_description/vnext_plus196/repo_candidate_review_classification_summary_v196_reference.json",
            ],
            summary_refs=["summary:v70c:self-evidencing:ready-review"],
            handoff_refs=["handoff:v70c:self-evidencing:ready-review"],
            source_handoff_refs=["handoff:v70c:self-evidencing:ready-review"],
            requested_ratification_horizon="source_bound_candidate_validity",
            request_posture="eligible_for_ratification_review",
            review_signal_posture="human_review_required",
            odeu_lanes=["deontic", "epistemic", "ontological"],
            authority_profile_refs=["authority:v71a:maintainer:ratification-review"],
            request_scope_boundary_refs=["scope:v71a:self-evidencing:ratification-request"],
            limitation_note="Ready workflow-residue request still requires human review.",
        ),
    ]


def derive_v71a_repo_candidate_ratification_request(
    *,
    repo_root: Path,
) -> RepoCandidateRatificationRequest:
    summary = RepoCandidateReviewClassificationSummary.model_validate(
        _load_json(repo_root, _V70C_SUMMARY_FIXTURE)
    )
    handoff = RepoCandidatePreRatificationHandoff.model_validate(
        _load_json(repo_root, _V70C_HANDOFF_FIXTURE)
    )
    payload = {
        "schema": REPO_CANDIDATE_RATIFICATION_REQUEST_SCHEMA,
        "review_id": "review:v71a:ratification-request-intake",
        "snapshot_id": "vNext+197-prestart-on-main",
        "source_set_id": summary.source_set_id,
        "summary_register_id": summary.summary_register_id,
        "handoff_register_id": handoff.handoff_register_id,
        "ratification_source_rows": [
            row.model_dump(mode="json")
            for row in sorted(_ratification_source_rows(), key=lambda row: row.source_ref)
        ],
        "candidate_input_refs": sorted(row.candidate_ref for row in handoff.handoff_rows),
        "request_rows": [
            row.model_dump(mode="json")
            for row in sorted(_request_rows(), key=lambda row: row.request_ref)
        ],
        "non_ratification_summary": "V71-A creates review requests only.",
    }
    payload["ratification_request_id"] = _surface_id(
        "repo_candidate_ratification_request",
        REPO_CANDIDATE_RATIFICATION_REQUEST_SCHEMA,
        payload,
        "ratification_request_id",
    )
    return RepoCandidateRatificationRequest.model_validate(payload)


def derive_v71a_repo_ratification_authority_profile(
    *,
    repo_root: Path,
) -> RepoRatificationAuthorityProfile:
    request = derive_v71a_repo_candidate_ratification_request(repo_root=repo_root)
    rows = [
        RepoRatificationAuthorityProfileRow(
            authority_profile_ref="authority:v71a:maintainer:ratification-review",
            authority_actor_ref="actor:maintainer:repo-review",
            authority_actor_kind="maintainer",
            authority_grant_source_kind="repo_lock",
            authority_source_refs=["docs/LOCKED_CONTINUATION_vNEXT_PLUS197.md"],
            authority_posture="ratification_authority",
            binding_layer="lock",
            allowed_ratification_horizons=[
                "review_conflict_settlement",
                "source_bound_candidate_validity",
            ],
            forbidden_downstream_roles=sorted(_DOWNSTREAM_FORBIDDEN_SET),
            limitation_note="Maintainer profile may review the selected horizons only.",
        ),
        RepoRatificationAuthorityProfileRow(
            authority_profile_ref="authority:v71a:support-reviewer:advisory-only",
            authority_actor_ref="actor:support:gptpro-review",
            authority_actor_kind="external_reviewer",
            authority_grant_source_kind="support_doc",
            authority_source_refs=["docs/LOCKED_CONTINUATION_vNEXT_PLUS197.md"],
            authority_posture="advisory_only",
            binding_layer="support",
            allowed_ratification_horizons=[],
            forbidden_downstream_roles=sorted(_DOWNSTREAM_FORBIDDEN_SET),
            limitation_note="Support review may shape future-family routing only.",
        ),
    ]
    payload = {
        "schema": REPO_RATIFICATION_AUTHORITY_PROFILE_SCHEMA,
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
        "ratification_source_refs": [row.source_ref for row in request.ratification_source_rows],
        "authority_profile_rows": [
            row.model_dump(mode="json")
            for row in sorted(rows, key=lambda row: row.authority_profile_ref)
        ],
        "non_authority_summary": "V71-A authority profiles bound review role only.",
    }
    payload["authority_profile_id"] = _surface_id(
        "repo_ratification_authority_profile",
        REPO_RATIFICATION_AUTHORITY_PROFILE_SCHEMA,
        payload,
        "authority_profile_id",
    )
    return RepoRatificationAuthorityProfile.model_validate(payload)


def derive_v71a_repo_ratification_request_scope_boundary(
    *,
    repo_root: Path,
) -> RepoRatificationRequestScopeBoundary:
    request = derive_v71a_repo_candidate_ratification_request(repo_root=repo_root)
    authority_profile = derive_v71a_repo_ratification_authority_profile(repo_root=repo_root)
    source_refs = [
        "apps/api/fixtures/repo_description/vnext_plus196/repo_candidate_pre_ratification_handoff_v196_reference.json",
        "apps/api/fixtures/repo_description/vnext_plus196/repo_candidate_review_classification_summary_v196_reference.json",
    ]
    rows = [
        RepoRatificationRequestScopeBoundaryRow(
            request_scope_boundary_ref="scope:v71a:odeu-diff:settlement-request",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            ratification_source_refs=source_refs,
            request_refs=["request:v71a:odeu-diff:settlement-required"],
            allowed_ratification_actions=["request_settlement_review"],
            forbidden_downstream_roles=sorted(_DOWNSTREAM_FORBIDDEN_SET),
            allowed_next_review_surfaces=["v71b_settlement_review"],
            non_implementation_guardrail="No implementation and no release authority is granted.",
        ),
        RepoRatificationRequestScopeBoundaryRow(
            request_scope_boundary_ref="scope:v71a:product-wedge:future-family",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            ratification_source_refs=source_refs,
            request_refs=["request:v71a:product-wedge:future-family"],
            allowed_ratification_actions=["defer_to_future_family"],
            forbidden_downstream_roles=sorted(_DOWNSTREAM_FORBIDDEN_SET),
            allowed_next_review_surfaces=["future_family_review"],
            non_implementation_guardrail="No implementation and no release authority is granted.",
        ),
        RepoRatificationRequestScopeBoundaryRow(
            request_scope_boundary_ref="scope:v71a:self-evidencing:ratification-request",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            ratification_source_refs=source_refs,
            request_refs=["request:v71a:self-evidencing:eligible"],
            allowed_ratification_actions=["request_ratification_review"],
            forbidden_downstream_roles=sorted(_DOWNSTREAM_FORBIDDEN_SET),
            allowed_next_review_surfaces=["v71b_ratification_review"],
            non_implementation_guardrail="No implementation and no release authority is granted.",
        ),
    ]
    payload = {
        "schema": REPO_RATIFICATION_REQUEST_SCOPE_BOUNDARY_SCHEMA,
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
        "ratification_request_id": request.ratification_request_id,
        "authority_profile_id": authority_profile.authority_profile_id,
        "request_scope_boundary_rows": [
            row.model_dump(mode="json")
            for row in sorted(rows, key=lambda row: row.request_scope_boundary_ref)
        ],
        "non_implementation_summary": "V71-A records no implementation and no release authority.",
    }
    payload["request_scope_boundary_id"] = _surface_id(
        "repo_ratification_request_scope_boundary",
        REPO_RATIFICATION_REQUEST_SCOPE_BOUNDARY_SCHEMA,
        payload,
        "request_scope_boundary_id",
    )
    return RepoRatificationRequestScopeBoundary.model_validate(payload)


def derive_v71a_repo_candidate_ratification_review_bundle(
    *,
    repo_root: Path,
) -> tuple[
    RepoCandidateReviewClassificationSummary,
    RepoCandidatePreRatificationHandoff,
    RepoCandidateRatificationRequest,
    RepoRatificationAuthorityProfile,
    RepoRatificationRequestScopeBoundary,
]:
    summary = RepoCandidateReviewClassificationSummary.model_validate(
        _load_json(repo_root, _V70C_SUMMARY_FIXTURE)
    )
    handoff = RepoCandidatePreRatificationHandoff.model_validate(
        _load_json(repo_root, _V70C_HANDOFF_FIXTURE)
    )
    request = derive_v71a_repo_candidate_ratification_request(repo_root=repo_root)
    authority_profile = derive_v71a_repo_ratification_authority_profile(repo_root=repo_root)
    scope_boundary = derive_v71a_repo_ratification_request_scope_boundary(repo_root=repo_root)
    validate_v71a_candidate_ratification_review_bundle(
        classification_summary=summary,
        pre_ratification_handoff=handoff,
        ratification_request=request,
        authority_profile=authority_profile,
        request_scope_boundary=scope_boundary,
    )
    return summary, handoff, request, authority_profile, scope_boundary


class RepoCandidateRatificationRecordRow(_CartographyBase):
    ratification_ref: str
    candidate_ref: str
    request_refs: list[str] = Field(min_length=1)
    settlement_refs: list[str] = Field(default_factory=list)
    decision_posture: RatificationDecisionPosture
    ratification_horizon: RatificationHorizon
    allowed_next_review_surface: V71BAllowedNextReviewSurface
    ratifying_authority_profile_refs: list[str] = Field(min_length=1)
    dissent_refs: list[str] = Field(default_factory=list)
    amendment_scope_refs: list[str] = Field(default_factory=list, max_length=0)
    non_integration_guardrail: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_ratification_row(self) -> RepoCandidateRatificationRecordRow:
        object.__setattr__(
            self,
            "ratification_ref",
            _non_empty(self.ratification_ref, field_name="ratification_ref"),
        )
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        object.__setattr__(
            self, "request_refs", _sorted_unique(self.request_refs, field_name="request_refs")
        )
        object.__setattr__(
            self,
            "settlement_refs",
            _sorted_unique(self.settlement_refs, field_name="settlement_refs"),
        )
        object.__setattr__(
            self,
            "ratifying_authority_profile_refs",
            _sorted_unique(
                self.ratifying_authority_profile_refs,
                field_name="ratifying_authority_profile_refs",
            ),
        )
        object.__setattr__(
            self, "dissent_refs", _sorted_unique(self.dissent_refs, field_name="dissent_refs")
        )
        object.__setattr__(
            self,
            "amendment_scope_refs",
            _sorted_unique(self.amendment_scope_refs, field_name="amendment_scope_refs"),
        )
        object.__setattr__(
            self,
            "non_integration_guardrail",
            _non_integration_guardrail(
                self.non_integration_guardrail, field_name="non_integration_guardrail"
            ),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _v71b_note(self.limitation_note, field_name="limitation_note"),
        )
        if self.amendment_scope_refs:
            raise ValueError("V71-B cannot emit amendment_scope_refs")
        if self.decision_posture in {"rejected", "out_of_scope"} and (
            self.allowed_next_review_surface == "v72_contained_integration_review"
        ):
            raise ValueError("rejected or out-of-scope rows cannot route to V72 review")
        if (
            self.candidate_ref == "candidate:internal:typed_adjudication_product_wedge"
            and self.allowed_next_review_surface == "v72_contained_integration_review"
        ):
            raise ValueError("product wedge cannot be ratified for integration review")
        return self


class RepoCandidateRatificationRecord(_CartographyBase):
    schema: Literal["repo_candidate_ratification_record@1"] = (
        REPO_CANDIDATE_RATIFICATION_RECORD_SCHEMA
    )
    ratification_record_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    ratification_request_id: str
    authority_profile_id: str
    request_scope_boundary_id: str
    settlement_register_id: str
    dissent_register_id: str
    ratification_rows: list[RepoCandidateRatificationRecordRow] = Field(min_length=1)
    non_integration_summary: str

    @model_validator(mode="after")
    def _validate_ratification_record(self) -> RepoCandidateRatificationRecord:
        object.__setattr__(
            self,
            "ratification_record_id",
            _non_empty(self.ratification_record_id, field_name="ratification_record_id"),
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
            "ratification_request_id",
            _non_empty(self.ratification_request_id, field_name="ratification_request_id"),
        )
        object.__setattr__(
            self,
            "authority_profile_id",
            _non_empty(self.authority_profile_id, field_name="authority_profile_id"),
        )
        object.__setattr__(
            self,
            "request_scope_boundary_id",
            _non_empty(self.request_scope_boundary_id, field_name="request_scope_boundary_id"),
        )
        object.__setattr__(
            self,
            "settlement_register_id",
            _non_empty(self.settlement_register_id, field_name="settlement_register_id"),
        )
        object.__setattr__(
            self,
            "dissent_register_id",
            _non_empty(self.dissent_register_id, field_name="dissent_register_id"),
        )
        object.__setattr__(
            self,
            "ratification_rows",
            _sorted_unique_by_ref(
                self.ratification_rows,
                attr="ratification_ref",
                field_name="ratification_rows",
            ),
        )
        object.__setattr__(
            self,
            "non_integration_summary",
            _non_integration_guardrail(
                self.non_integration_summary, field_name="non_integration_summary"
            ),
        )
        expected_id = _surface_id(
            "repo_candidate_ratification_record",
            REPO_CANDIDATE_RATIFICATION_RECORD_SCHEMA,
            self.model_dump(mode="json"),
            "ratification_record_id",
        )
        if self.ratification_record_id != expected_id:
            raise ValueError(
                "ratification_record_id must match canonical full payload hash identity"
            )
        return self


class RepoReviewSettlementRow(_CartographyBase):
    settlement_ref: str
    candidate_ref: str
    request_refs: list[str] = Field(min_length=1)
    source_relation_refs: list[str] = Field(default_factory=list)
    relation_kind: ReviewRelationKind
    source_gap_refs: list[str] = Field(default_factory=list)
    settlement_posture: SettlementPosture
    review_signal_posture: ReviewSignalPosture
    settlement_authority_profile_refs: list[str] = Field(min_length=1)
    dissent_refs: list[str] = Field(default_factory=list)
    carried_forward_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_settlement_row(self) -> RepoReviewSettlementRow:
        object.__setattr__(
            self, "settlement_ref", _non_empty(self.settlement_ref, field_name="settlement_ref")
        )
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        object.__setattr__(
            self, "request_refs", _sorted_unique(self.request_refs, field_name="request_refs")
        )
        object.__setattr__(
            self,
            "source_relation_refs",
            _sorted_unique(self.source_relation_refs, field_name="source_relation_refs"),
        )
        object.__setattr__(
            self,
            "source_gap_refs",
            _sorted_unique(self.source_gap_refs, field_name="source_gap_refs"),
        )
        object.__setattr__(
            self,
            "settlement_authority_profile_refs",
            _sorted_unique(
                self.settlement_authority_profile_refs,
                field_name="settlement_authority_profile_refs",
            ),
        )
        object.__setattr__(
            self, "dissent_refs", _sorted_unique(self.dissent_refs, field_name="dissent_refs")
        )
        object.__setattr__(
            self,
            "carried_forward_refs",
            _sorted_unique(self.carried_forward_refs, field_name="carried_forward_refs"),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _v71b_note(self.limitation_note, field_name="limitation_note"),
        )
        if self.relation_kind == "conflict" and not self.source_relation_refs:
            raise ValueError("conflict settlement rows require source_relation_refs")
        if self.relation_kind != "conflict" and (
            self.settlement_posture == "blocked_by_unresolved_conflict"
        ):
            raise ValueError("non-conflict settlement rows cannot be blocked by conflict")
        if self.relation_kind == "complementarity" and (
            self.review_signal_posture == "gating_blocker"
        ):
            raise ValueError("complementarity rows cannot carry gating blocker posture")
        if (
            self.settlement_posture
            in {"partially_settled_with_dissent", "blocked_by_unresolved_conflict"}
            and not self.dissent_refs
        ):
            raise ValueError("partial or unresolved settlement rows must preserve dissent_refs")
        if self.settlement_posture == "blocked_by_unresolved_gap" and not self.source_gap_refs:
            raise ValueError("gap-blocked settlement rows require source_gap_refs")
        if (
            self.settlement_posture
            in {"blocked_by_unresolved_gap", "requires_more_evidence", "future_family_only"}
            and not self.carried_forward_refs
        ):
            raise ValueError("unresolved gap or future-family settlements require carry-forward")
        return self


class RepoReviewSettlementRecord(_CartographyBase):
    schema: Literal["repo_review_settlement_record@1"] = REPO_REVIEW_SETTLEMENT_RECORD_SCHEMA
    settlement_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    ratification_request_id: str
    authority_profile_id: str
    request_refs: list[str] = Field(min_length=1)
    settlement_rows: list[RepoReviewSettlementRow] = Field(min_length=1)
    non_integration_summary: str

    @model_validator(mode="after")
    def _validate_settlement_record(self) -> RepoReviewSettlementRecord:
        object.__setattr__(
            self,
            "settlement_register_id",
            _non_empty(self.settlement_register_id, field_name="settlement_register_id"),
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
            "ratification_request_id",
            _non_empty(self.ratification_request_id, field_name="ratification_request_id"),
        )
        object.__setattr__(
            self,
            "authority_profile_id",
            _non_empty(self.authority_profile_id, field_name="authority_profile_id"),
        )
        object.__setattr__(
            self, "request_refs", _sorted_unique(self.request_refs, field_name="request_refs")
        )
        object.__setattr__(
            self,
            "settlement_rows",
            _sorted_unique_by_ref(
                self.settlement_rows, attr="settlement_ref", field_name="settlement_rows"
            ),
        )
        object.__setattr__(
            self,
            "non_integration_summary",
            _non_integration_guardrail(
                self.non_integration_summary, field_name="non_integration_summary"
            ),
        )
        known_request_refs = set(self.request_refs)
        covered_request_refs: set[str] = set()
        for row in self.settlement_rows:
            missing = sorted(set(row.request_refs) - known_request_refs)
            if missing:
                raise ValueError(f"settlement rows must reference known request_refs: {missing}")
            covered_request_refs.update(row.request_refs)
        uncovered_request_refs = sorted(known_request_refs - covered_request_refs)
        if uncovered_request_refs:
            raise ValueError(
                f"settlement rows must cover every declared request_ref: {uncovered_request_refs}"
            )
        expected_id = _surface_id(
            "repo_review_settlement_record",
            REPO_REVIEW_SETTLEMENT_RECORD_SCHEMA,
            self.model_dump(mode="json"),
            "settlement_register_id",
        )
        if self.settlement_register_id != expected_id:
            raise ValueError(
                "settlement_register_id must match canonical full payload hash identity"
            )
        return self


class RepoRatificationDissentRow(_CartographyBase):
    dissent_ref: str
    candidate_ref: str
    request_refs: list[str] = Field(min_length=1)
    settlement_refs: list[str] = Field(default_factory=list)
    dissent_source_refs: list[str] = Field(min_length=1)
    dissent_posture: DissentPosture
    dissent_search_posture: DissentSearchPosture
    dissent_summary: str
    carry_forward_required: bool
    limitation_note: str

    @model_validator(mode="after")
    def _validate_dissent_row(self) -> RepoRatificationDissentRow:
        object.__setattr__(
            self, "dissent_ref", _non_empty(self.dissent_ref, field_name="dissent_ref")
        )
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        object.__setattr__(
            self, "request_refs", _sorted_unique(self.request_refs, field_name="request_refs")
        )
        object.__setattr__(
            self,
            "settlement_refs",
            _sorted_unique(self.settlement_refs, field_name="settlement_refs"),
        )
        object.__setattr__(
            self,
            "dissent_source_refs",
            _sorted_unique(self.dissent_source_refs, field_name="dissent_source_refs"),
        )
        object.__setattr__(
            self,
            "dissent_summary",
            _v71b_note(self.dissent_summary, field_name="dissent_summary"),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _v71b_note(self.limitation_note, field_name="limitation_note"),
        )
        if (
            self.dissent_posture == "no_dissent_recorded"
            and self.dissent_search_posture != "searched_none_found"
        ):
            raise ValueError("no_dissent_recorded requires searched_none_found")
        if self.dissent_posture == "no_dissent_recorded" and self.carry_forward_required:
            raise ValueError("no_dissent_recorded cannot require carry-forward")
        if self.dissent_posture in {
            "dissent_carried_forward",
            "minority_review_preserved",
            "unresolved_blocker",
        }:
            if self.dissent_search_posture != "dissent_present":
                raise ValueError("dissent-preserving rows require dissent_present search posture")
            if not self.carry_forward_required:
                raise ValueError("dissent-preserving rows require carry_forward_required")
        return self


class RepoRatificationDissentRegister(_CartographyBase):
    schema: Literal["repo_ratification_dissent_register@1"] = (
        REPO_RATIFICATION_DISSENT_REGISTER_SCHEMA
    )
    dissent_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    ratification_request_id: str
    settlement_register_id: str
    request_refs: list[str] = Field(min_length=1)
    dissent_rows: list[RepoRatificationDissentRow] = Field(min_length=1)
    dissent_preservation_summary: str

    @model_validator(mode="after")
    def _validate_dissent_register(self) -> RepoRatificationDissentRegister:
        object.__setattr__(
            self,
            "dissent_register_id",
            _non_empty(self.dissent_register_id, field_name="dissent_register_id"),
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
            "ratification_request_id",
            _non_empty(self.ratification_request_id, field_name="ratification_request_id"),
        )
        object.__setattr__(
            self,
            "settlement_register_id",
            _non_empty(self.settlement_register_id, field_name="settlement_register_id"),
        )
        object.__setattr__(
            self, "request_refs", _sorted_unique(self.request_refs, field_name="request_refs")
        )
        object.__setattr__(
            self,
            "dissent_rows",
            _sorted_unique_by_ref(self.dissent_rows, attr="dissent_ref", field_name="dissent_rows"),
        )
        object.__setattr__(
            self,
            "dissent_preservation_summary",
            _v71b_note(
                self.dissent_preservation_summary, field_name="dissent_preservation_summary"
            ),
        )
        known_request_refs = set(self.request_refs)
        for row in self.dissent_rows:
            missing = sorted(set(row.request_refs) - known_request_refs)
            if missing:
                raise ValueError(f"dissent rows must reference known request_refs: {missing}")
        expected_id = _surface_id(
            "repo_ratification_dissent_register",
            REPO_RATIFICATION_DISSENT_REGISTER_SCHEMA,
            self.model_dump(mode="json"),
            "dissent_register_id",
        )
        if self.dissent_register_id != expected_id:
            raise ValueError("dissent_register_id must match canonical full payload hash identity")
        return self


_V71A_REQUEST_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus197/"
    "repo_candidate_ratification_request_v197_reference.json"
)
_V71A_AUTHORITY_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus197/"
    "repo_ratification_authority_profile_v197_reference.json"
)
_V71A_SCOPE_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus197/"
    "repo_ratification_request_scope_boundary_v197_reference.json"
)


def validate_v71b_candidate_ratification_review_bundle(
    *,
    ratification_request: RepoCandidateRatificationRequest,
    authority_profile: RepoRatificationAuthorityProfile,
    request_scope_boundary: RepoRatificationRequestScopeBoundary,
    settlement_record: RepoReviewSettlementRecord,
    dissent_register: RepoRatificationDissentRegister,
    ratification_record: RepoCandidateRatificationRecord,
) -> None:
    if authority_profile.review_id != ratification_request.review_id:
        raise ValueError("authority profile review_id must match ratification request")
    if request_scope_boundary.review_id != ratification_request.review_id:
        raise ValueError("request scope boundary review_id must match ratification request")
    if dissent_register.review_id != settlement_record.review_id:
        raise ValueError("dissent register review_id must match settlement record")
    if ratification_record.review_id != settlement_record.review_id:
        raise ValueError("ratification record review_id must match settlement record")
    if settlement_record.source_set_id != ratification_request.source_set_id:
        raise ValueError("settlement record source_set_id must match ratification request")
    if dissent_register.source_set_id != settlement_record.source_set_id:
        raise ValueError("dissent register source_set_id must match settlement record")
    if ratification_record.source_set_id != settlement_record.source_set_id:
        raise ValueError("ratification record source_set_id must match settlement record")
    if settlement_record.ratification_request_id != ratification_request.ratification_request_id:
        raise ValueError("settlement record must reference V71-A ratification request")
    if dissent_register.ratification_request_id != ratification_request.ratification_request_id:
        raise ValueError("dissent register must reference V71-A ratification request")
    if ratification_record.ratification_request_id != ratification_request.ratification_request_id:
        raise ValueError("ratification record must reference V71-A ratification request")
    if settlement_record.authority_profile_id != authority_profile.authority_profile_id:
        raise ValueError("settlement record must reference V71-A authority profile register")
    if ratification_record.authority_profile_id != authority_profile.authority_profile_id:
        raise ValueError("ratification record must reference V71-A authority profile register")
    if (
        ratification_record.request_scope_boundary_id
        != request_scope_boundary.request_scope_boundary_id
    ):
        raise ValueError("ratification record must reference V71-A request scope boundary")
    if dissent_register.settlement_register_id != settlement_record.settlement_register_id:
        raise ValueError("dissent register must reference settlement register")
    if ratification_record.settlement_register_id != settlement_record.settlement_register_id:
        raise ValueError("ratification record must reference settlement register")
    if ratification_record.dissent_register_id != dissent_register.dissent_register_id:
        raise ValueError("ratification record must reference dissent register")

    request_rows = {row.request_ref: row for row in ratification_request.request_rows}
    authority_rows = {
        row.authority_profile_ref: row for row in authority_profile.authority_profile_rows
    }
    scope_rows_by_request: dict[str, RepoRatificationRequestScopeBoundaryRow] = {}
    for scope_row in request_scope_boundary.request_scope_boundary_rows:
        for request_ref in scope_row.request_refs:
            if request_ref in scope_rows_by_request:
                raise ValueError("request scope boundary rows must cover each request once")
            scope_rows_by_request[request_ref] = scope_row
    settlement_rows = {row.settlement_ref: row for row in settlement_record.settlement_rows}
    dissent_rows = {row.dissent_ref: row for row in dissent_register.dissent_rows}
    known_request_refs = set(request_rows)
    if set(scope_rows_by_request) != known_request_refs:
        raise ValueError("request scope boundary rows must match V71-A requests")
    if set(settlement_record.request_refs) != known_request_refs:
        raise ValueError("settlement record request_refs must match V71-A requests")
    if set(dissent_register.request_refs) != known_request_refs:
        raise ValueError("dissent register request_refs must match V71-A requests")

    for settlement in settlement_record.settlement_rows:
        for request_ref in settlement.request_refs:
            request = request_rows[request_ref]
            if settlement.candidate_ref != request.candidate_ref:
                raise ValueError("settlement candidate_ref must match request")
        for profile_ref in settlement.settlement_authority_profile_refs:
            profile = authority_rows.get(profile_ref)
            if profile is None:
                raise ValueError("settlement rows must reference known authority profiles")
            if profile.authority_posture not in {"ratification_authority", "settlement_authority"}:
                raise ValueError("settlement rows require settlement-capable authority profile")
        for dissent_ref in settlement.dissent_refs:
            if dissent_ref not in dissent_rows:
                raise ValueError("settlement rows must reference known dissent rows")

    for dissent in dissent_register.dissent_rows:
        for request_ref in dissent.request_refs:
            request = request_rows[request_ref]
            if dissent.candidate_ref != request.candidate_ref:
                raise ValueError("dissent candidate_ref must match request")
        for settlement_ref in dissent.settlement_refs:
            if settlement_ref not in settlement_rows:
                raise ValueError("dissent rows must reference known settlement rows")

    seen_ratification_requests: set[str] = set()
    for ratification in ratification_record.ratification_rows:
        missing_requests = sorted(set(ratification.request_refs) - known_request_refs)
        if missing_requests:
            raise ValueError(
                f"ratification rows must reference known request_refs: {missing_requests}"
            )
        for request_ref in ratification.request_refs:
            if request_ref in seen_ratification_requests:
                raise ValueError("ratification rows must cover each request at most once")
            seen_ratification_requests.add(request_ref)
            request = request_rows[request_ref]
            if ratification.candidate_ref != request.candidate_ref:
                raise ValueError("ratification candidate_ref must match request")
            scope_row = scope_rows_by_request[request_ref]
            if ratification.candidate_ref != scope_row.candidate_ref:
                raise ValueError("ratification candidate_ref must match scope boundary")
            scope_surfaces = set(scope_row.allowed_next_review_surfaces)
            if (
                ratification.allowed_next_review_surface == "v72_contained_integration_review"
                and "v71b_ratification_review" not in scope_surfaces
            ):
                raise ValueError("ratification next surface exceeds V71-A scope boundary")
            if (
                ratification.allowed_next_review_surface == "future_family_review"
                and "future_family_review" not in scope_surfaces
            ):
                raise ValueError("ratification future-family routing exceeds V71-A scope boundary")
            if (
                request.request_posture == "requires_settlement_before_ratification"
                and ratification.decision_posture == "ratified"
                and not any(
                    settlement_ref in settlement_rows
                    and request_ref in settlement_rows[settlement_ref].request_refs
                    for settlement_ref in ratification.settlement_refs
                )
            ):
                raise ValueError(
                    f"blocked request {request_ref} cannot be ratified without covering settlement"
                )
            if request.request_posture == "deferred_to_future_family" and (
                ratification.decision_posture == "ratified"
                or ratification.allowed_next_review_surface == "v72_contained_integration_review"
            ):
                raise ValueError("future-family requests cannot be ratified for integration")
            for profile_ref in ratification.ratifying_authority_profile_refs:
                profile = authority_rows.get(profile_ref)
                if profile is None:
                    raise ValueError("ratification rows must reference known authority profiles")
                if ratification.decision_posture != "ratified":
                    continue
                if profile.authority_posture != "ratification_authority":
                    raise ValueError("ratification requires ratification-authorized profile")
                if ratification.ratification_horizon not in profile.allowed_ratification_horizons:
                    raise ValueError(
                        "ratification horizon must be allowed by every authority profile"
                    )
        for settlement_ref in ratification.settlement_refs:
            settlement = settlement_rows.get(settlement_ref)
            if settlement is None:
                raise ValueError("ratification rows must reference known settlement rows")
            if settlement.candidate_ref != ratification.candidate_ref:
                raise ValueError("ratification candidate_ref must match settlement")
            if (
                settlement.settlement_posture
                in {
                    "blocked_by_unresolved_conflict",
                    "blocked_by_unresolved_gap",
                    "requires_more_evidence",
                    "requires_human_review",
                    "future_family_only",
                }
                and ratification.decision_posture == "ratified"
            ):
                raise ValueError("unresolved settlement blockers cannot be ratified")
            missing_dissent = sorted(set(settlement.dissent_refs) - set(ratification.dissent_refs))
            if missing_dissent:
                raise ValueError(
                    f"ratification row must preserve dissent from settlement "
                    f"{settlement_ref}: {missing_dissent}"
                )
        for dissent_ref in ratification.dissent_refs:
            dissent = dissent_rows.get(dissent_ref)
            if dissent is None:
                raise ValueError("ratification rows must reference known dissent rows")
            if dissent.candidate_ref != ratification.candidate_ref:
                raise ValueError("ratification candidate_ref must match dissent")
            if dissent.dissent_posture == "unresolved_blocker" and (
                ratification.decision_posture == "ratified"
            ):
                raise ValueError("unresolved dissent blockers cannot be ratified")
    if seen_ratification_requests != known_request_refs:
        missing = sorted(known_request_refs - seen_ratification_requests)
        raise ValueError(f"ratification rows must cover every V71-A request: {missing}")


def derive_v71b_repo_review_settlement_record(
    *,
    repo_root: Path,
) -> RepoReviewSettlementRecord:
    request = RepoCandidateRatificationRequest.model_validate(
        _load_json(repo_root, _V71A_REQUEST_FIXTURE)
    )
    authority_profile = RepoRatificationAuthorityProfile.model_validate(
        _load_json(repo_root, _V71A_AUTHORITY_FIXTURE)
    )
    rows = [
        RepoReviewSettlementRow(
            settlement_ref="settlement:v71b:odeu-diff:partial-with-dissent",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            request_refs=["request:v71a:odeu-diff:settlement-required"],
            source_relation_refs=["relation:v70b:odeu-diff:model-output-divergence"],
            relation_kind="conflict",
            source_gap_refs=["gap:v70b:odeu-diff:missing-counterevidence"],
            settlement_posture="partially_settled_with_dissent",
            review_signal_posture="settlement_required",
            settlement_authority_profile_refs=["authority:v71a:maintainer:ratification-review"],
            dissent_refs=["dissent:v71b:odeu-diff:minority-preserved"],
            carried_forward_refs=["gap:v70b:odeu-diff:missing-counterevidence"],
            limitation_note=(
                "Settlement preserves the model-output review dissent for later review."
            ),
        ),
        RepoReviewSettlementRow(
            settlement_ref="settlement:v71b:product-wedge:future-family",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            request_refs=["request:v71a:product-wedge:future-family"],
            source_relation_refs=["relation:v70b:product-wedge:authority-boundary"],
            relation_kind="conflict",
            source_gap_refs=[
                "gap:v70b:product-wedge:single-source-overclaim",
                "gap:v70b:product-wedge:v74-boundary",
            ],
            settlement_posture="future_family_only",
            review_signal_posture="future_family_only",
            settlement_authority_profile_refs=["authority:v71a:maintainer:ratification-review"],
            dissent_refs=[],
            carried_forward_refs=["gap:v70b:product-wedge:v74-boundary"],
            limitation_note="Product pressure remains routed to future-family review.",
        ),
        RepoReviewSettlementRow(
            settlement_ref="settlement:v71b:self-evidencing:complementary",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            request_refs=["request:v71a:self-evidencing:eligible"],
            source_relation_refs=["relation:v70b:self-evidencing:complementarity"],
            relation_kind="complementarity",
            source_gap_refs=[],
            settlement_posture="settled_for_candidate_horizon",
            review_signal_posture="warning_only",
            settlement_authority_profile_refs=["authority:v71a:maintainer:ratification-review"],
            dissent_refs=["dissent:v71b:self-evidencing:none-found"],
            carried_forward_refs=[],
            limitation_note=(
                "Complementary source-binding review is settled for candidate validity."
            ),
        ),
    ]
    payload = {
        "schema": REPO_REVIEW_SETTLEMENT_RECORD_SCHEMA,
        "review_id": "review:v71b:ratification-settlement",
        "snapshot_id": "vNext+198-prestart-on-main",
        "source_set_id": request.source_set_id,
        "ratification_request_id": request.ratification_request_id,
        "authority_profile_id": authority_profile.authority_profile_id,
        "request_refs": [row.request_ref for row in request.request_rows],
        "settlement_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.settlement_ref)
        ],
        "non_integration_summary": _V71B_NON_INTEGRATION_GUARDRAIL,
    }
    payload["settlement_register_id"] = _surface_id(
        "repo_review_settlement_record",
        REPO_REVIEW_SETTLEMENT_RECORD_SCHEMA,
        payload,
        "settlement_register_id",
    )
    return RepoReviewSettlementRecord.model_validate(payload)


def derive_v71b_repo_ratification_dissent_register(
    *,
    repo_root: Path,
) -> RepoRatificationDissentRegister:
    request = RepoCandidateRatificationRequest.model_validate(
        _load_json(repo_root, _V71A_REQUEST_FIXTURE)
    )
    settlement = derive_v71b_repo_review_settlement_record(repo_root=repo_root)
    rows = [
        RepoRatificationDissentRow(
            dissent_ref="dissent:v71b:odeu-diff:minority-preserved",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            request_refs=["request:v71a:odeu-diff:settlement-required"],
            settlement_refs=["settlement:v71b:odeu-diff:partial-with-dissent"],
            dissent_source_refs=["gap:v70b:odeu-diff:missing-counterevidence"],
            dissent_posture="minority_review_preserved",
            dissent_search_posture="dissent_present",
            dissent_summary="Counterevidence gap remains preserved for later review.",
            carry_forward_required=True,
            limitation_note="Dissent preservation does not grant downstream work.",
        ),
        RepoRatificationDissentRow(
            dissent_ref="dissent:v71b:product-wedge:not-applicable",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            request_refs=["request:v71a:product-wedge:future-family"],
            settlement_refs=["settlement:v71b:product-wedge:future-family"],
            dissent_source_refs=["gap:v70b:product-wedge:v74-boundary"],
            dissent_posture="not_applicable",
            dissent_search_posture="not_applicable",
            dissent_summary="Future-family product boundary review is not settled here.",
            carry_forward_required=False,
            limitation_note="Future-family routing is not product selection.",
        ),
        RepoRatificationDissentRow(
            dissent_ref="dissent:v71b:self-evidencing:none-found",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            request_refs=["request:v71a:self-evidencing:eligible"],
            settlement_refs=["settlement:v71b:self-evidencing:complementary"],
            dissent_source_refs=["relation:v70b:self-evidencing:complementarity"],
            dissent_posture="no_dissent_recorded",
            dissent_search_posture="searched_none_found",
            dissent_summary="No dissent found within the released review relation horizon.",
            carry_forward_required=False,
            limitation_note="Absence is bounded to the searched V70/V71 review horizon.",
        ),
    ]
    payload = {
        "schema": REPO_RATIFICATION_DISSENT_REGISTER_SCHEMA,
        "review_id": settlement.review_id,
        "snapshot_id": settlement.snapshot_id,
        "source_set_id": settlement.source_set_id,
        "ratification_request_id": request.ratification_request_id,
        "settlement_register_id": settlement.settlement_register_id,
        "request_refs": [row.request_ref for row in request.request_rows],
        "dissent_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.dissent_ref)
        ],
        "dissent_preservation_summary": (
            "Dissent is preserved or explicitly searched within horizon."
        ),
    }
    payload["dissent_register_id"] = _surface_id(
        "repo_ratification_dissent_register",
        REPO_RATIFICATION_DISSENT_REGISTER_SCHEMA,
        payload,
        "dissent_register_id",
    )
    return RepoRatificationDissentRegister.model_validate(payload)


def derive_v71b_repo_candidate_ratification_record(
    *,
    repo_root: Path,
) -> RepoCandidateRatificationRecord:
    request = RepoCandidateRatificationRequest.model_validate(
        _load_json(repo_root, _V71A_REQUEST_FIXTURE)
    )
    authority_profile = RepoRatificationAuthorityProfile.model_validate(
        _load_json(repo_root, _V71A_AUTHORITY_FIXTURE)
    )
    scope_boundary = RepoRatificationRequestScopeBoundary.model_validate(
        _load_json(repo_root, _V71A_SCOPE_FIXTURE)
    )
    settlement = derive_v71b_repo_review_settlement_record(repo_root=repo_root)
    dissent = derive_v71b_repo_ratification_dissent_register(repo_root=repo_root)
    rows = [
        RepoCandidateRatificationRecordRow(
            ratification_ref="ratification:v71b:odeu-diff:deferred-with-dissent",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            request_refs=["request:v71a:odeu-diff:settlement-required"],
            settlement_refs=["settlement:v71b:odeu-diff:partial-with-dissent"],
            decision_posture="deferred",
            ratification_horizon="review_conflict_settlement",
            allowed_next_review_surface="deferred_no_selection",
            ratifying_authority_profile_refs=["authority:v71a:maintainer:ratification-review"],
            dissent_refs=["dissent:v71b:odeu-diff:minority-preserved"],
            amendment_scope_refs=[],
            non_integration_guardrail=_V71B_NON_INTEGRATION_GUARDRAIL,
            limitation_note="Partial settlement defers the candidate while preserving dissent.",
        ),
        RepoCandidateRatificationRecordRow(
            ratification_ref="ratification:v71b:product-wedge:future-family",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            request_refs=["request:v71a:product-wedge:future-family"],
            settlement_refs=["settlement:v71b:product-wedge:future-family"],
            decision_posture="deferred",
            ratification_horizon="future_family_routing",
            allowed_next_review_surface="future_family_review",
            ratifying_authority_profile_refs=["authority:v71a:maintainer:ratification-review"],
            dissent_refs=["dissent:v71b:product-wedge:not-applicable"],
            amendment_scope_refs=[],
            non_integration_guardrail=_V71B_NON_INTEGRATION_GUARDRAIL,
            limitation_note="Product wedge remains future-family routed.",
        ),
        RepoCandidateRatificationRecordRow(
            ratification_ref="ratification:v71b:self-evidencing:source-bound-validity",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            request_refs=["request:v71a:self-evidencing:eligible"],
            settlement_refs=["settlement:v71b:self-evidencing:complementary"],
            decision_posture="ratified",
            ratification_horizon="source_bound_candidate_validity",
            allowed_next_review_surface="v72_contained_integration_review",
            ratifying_authority_profile_refs=["authority:v71a:maintainer:ratification-review"],
            dissent_refs=["dissent:v71b:self-evidencing:none-found"],
            amendment_scope_refs=[],
            non_integration_guardrail=_V71B_NON_INTEGRATION_GUARDRAIL,
            limitation_note="Ratified only for source-bound candidate validity review horizon.",
        ),
    ]
    payload = {
        "schema": REPO_CANDIDATE_RATIFICATION_RECORD_SCHEMA,
        "review_id": settlement.review_id,
        "snapshot_id": settlement.snapshot_id,
        "source_set_id": settlement.source_set_id,
        "ratification_request_id": request.ratification_request_id,
        "authority_profile_id": authority_profile.authority_profile_id,
        "request_scope_boundary_id": scope_boundary.request_scope_boundary_id,
        "settlement_register_id": settlement.settlement_register_id,
        "dissent_register_id": dissent.dissent_register_id,
        "ratification_rows": [
            row.model_dump(mode="json")
            for row in sorted(rows, key=lambda row: row.ratification_ref)
        ],
        "non_integration_summary": _V71B_NON_INTEGRATION_GUARDRAIL,
    }
    payload["ratification_record_id"] = _surface_id(
        "repo_candidate_ratification_record",
        REPO_CANDIDATE_RATIFICATION_RECORD_SCHEMA,
        payload,
        "ratification_record_id",
    )
    return RepoCandidateRatificationRecord.model_validate(payload)


def derive_v71b_repo_candidate_ratification_review_bundle(
    *,
    repo_root: Path,
) -> tuple[
    RepoCandidateRatificationRequest,
    RepoRatificationAuthorityProfile,
    RepoRatificationRequestScopeBoundary,
    RepoReviewSettlementRecord,
    RepoRatificationDissentRegister,
    RepoCandidateRatificationRecord,
]:
    request = RepoCandidateRatificationRequest.model_validate(
        _load_json(repo_root, _V71A_REQUEST_FIXTURE)
    )
    authority_profile = RepoRatificationAuthorityProfile.model_validate(
        _load_json(repo_root, _V71A_AUTHORITY_FIXTURE)
    )
    scope_boundary = RepoRatificationRequestScopeBoundary.model_validate(
        _load_json(repo_root, _V71A_SCOPE_FIXTURE)
    )
    settlement = derive_v71b_repo_review_settlement_record(repo_root=repo_root)
    dissent = derive_v71b_repo_ratification_dissent_register(repo_root=repo_root)
    ratification = derive_v71b_repo_candidate_ratification_record(repo_root=repo_root)
    validate_v71b_candidate_ratification_review_bundle(
        ratification_request=request,
        authority_profile=authority_profile,
        request_scope_boundary=scope_boundary,
        settlement_record=settlement,
        dissent_register=dissent,
        ratification_record=ratification,
    )
    return request, authority_profile, scope_boundary, settlement, dissent, ratification


class RepoRatificationAmendmentScopeBoundaryRow(_CartographyBase):
    amendment_scope_ref: str
    candidate_ref: str
    ratification_refs: list[str] = Field(min_length=1)
    settlement_refs: list[str] = Field(default_factory=list)
    allowed_amendment_scope: AllowedAmendmentScope
    forbidden_downstream_roles: list[ForbiddenDownstreamRole] = Field(min_length=1)
    allowed_next_review_surfaces: list[V71CAllowedNextReviewSurface] = Field(min_length=1)
    scope_limitation_note: str
    non_release_guardrail: str

    @model_validator(mode="after")
    def _validate_amendment_scope_row(self) -> RepoRatificationAmendmentScopeBoundaryRow:
        object.__setattr__(
            self,
            "amendment_scope_ref",
            _non_empty(self.amendment_scope_ref, field_name="amendment_scope_ref"),
        )
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
        )
        object.__setattr__(
            self,
            "ratification_refs",
            _sorted_unique(self.ratification_refs, field_name="ratification_refs"),
        )
        object.__setattr__(
            self,
            "settlement_refs",
            _sorted_unique(self.settlement_refs, field_name="settlement_refs"),
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
            "allowed_next_review_surfaces",
            _sorted_unique(
                self.allowed_next_review_surfaces, field_name="allowed_next_review_surfaces"
            ),
        )
        object.__setattr__(
            self,
            "scope_limitation_note",
            _v71c_note(self.scope_limitation_note, field_name="scope_limitation_note"),
        )
        object.__setattr__(
            self,
            "non_release_guardrail",
            _v71c_non_authority_guardrail(
                self.non_release_guardrail, field_name="non_release_guardrail"
            ),
        )
        missing_forbidden = sorted(_V71C_FORBIDDEN_SET - set(self.forbidden_downstream_roles))
        if missing_forbidden:
            raise ValueError(f"amendment scope must forbid downstream roles: {missing_forbidden}")
        if (
            self.candidate_ref == "candidate:internal:typed_adjudication_product_wedge"
            and "v72_contained_integration_review" in self.allowed_next_review_surfaces
        ):
            raise ValueError("product wedge cannot be routed to V72")
        if (
            self.allowed_amendment_scope in {"future_family_only", "no_amendment_scope"}
            and "v72_contained_integration_review" in self.allowed_next_review_surfaces
        ):
            raise ValueError("future-only or no-amendment scope cannot route to V72")
        return self


class RepoRatificationAmendmentScopeBoundary(_CartographyBase):
    schema: Literal["repo_ratification_amendment_scope_boundary@1"] = (
        REPO_RATIFICATION_AMENDMENT_SCOPE_BOUNDARY_SCHEMA
    )
    amendment_scope_boundary_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    ratification_record_id: str
    settlement_register_id: str
    dissent_register_id: str
    amendment_scope_rows: list[RepoRatificationAmendmentScopeBoundaryRow] = Field(min_length=1)
    non_authority_summary: str

    @model_validator(mode="after")
    def _validate_amendment_scope_boundary(self) -> RepoRatificationAmendmentScopeBoundary:
        object.__setattr__(
            self,
            "amendment_scope_boundary_id",
            _non_empty(
                self.amendment_scope_boundary_id,
                field_name="amendment_scope_boundary_id",
            ),
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
            "ratification_record_id",
            _non_empty(self.ratification_record_id, field_name="ratification_record_id"),
        )
        object.__setattr__(
            self,
            "settlement_register_id",
            _non_empty(self.settlement_register_id, field_name="settlement_register_id"),
        )
        object.__setattr__(
            self,
            "dissent_register_id",
            _non_empty(self.dissent_register_id, field_name="dissent_register_id"),
        )
        object.__setattr__(
            self,
            "amendment_scope_rows",
            _sorted_unique_by_ref(
                self.amendment_scope_rows,
                attr="amendment_scope_ref",
                field_name="amendment_scope_rows",
            ),
        )
        object.__setattr__(
            self,
            "non_authority_summary",
            _v71c_non_authority_guardrail(
                self.non_authority_summary, field_name="non_authority_summary"
            ),
        )
        expected_id = _surface_id(
            "repo_ratification_amendment_scope_boundary",
            REPO_RATIFICATION_AMENDMENT_SCOPE_BOUNDARY_SCHEMA,
            self.model_dump(mode="json"),
            "amendment_scope_boundary_id",
        )
        if self.amendment_scope_boundary_id != expected_id:
            raise ValueError(
                "amendment_scope_boundary_id must match canonical full payload hash identity"
            )
        return self


class RepoPostRatificationHandoffRow(_CartographyBase):
    handoff_ref: str
    candidate_ref: str
    ratification_refs: list[str] = Field(min_length=1)
    amendment_scope_refs: list[str] = Field(min_length=1)
    handoff_target: V71CAllowedNextReviewSurface
    handoff_posture: PostRatificationHandoffPosture
    required_next_surface: RequiredNextSurface
    carried_forward_dissent_refs: list[str] = Field(default_factory=list)
    carried_forward_gap_refs: list[str] = Field(default_factory=list)
    non_integration_guardrail: str

    @model_validator(mode="after")
    def _validate_handoff_row(self) -> RepoPostRatificationHandoffRow:
        object.__setattr__(
            self, "handoff_ref", _non_empty(self.handoff_ref, field_name="handoff_ref")
        )
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
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
            "carried_forward_dissent_refs",
            _sorted_unique(
                self.carried_forward_dissent_refs, field_name="carried_forward_dissent_refs"
            ),
        )
        object.__setattr__(
            self,
            "carried_forward_gap_refs",
            _sorted_unique(self.carried_forward_gap_refs, field_name="carried_forward_gap_refs"),
        )
        object.__setattr__(
            self,
            "non_integration_guardrail",
            _v71c_non_authority_guardrail(
                self.non_integration_guardrail, field_name="non_integration_guardrail"
            ),
        )
        expected_required_surface = {
            "v72_contained_integration_review": "v72_candidate_containment_planning",
            "future_family_review": "future_family_candidate_review",
            "deferred_no_selection": "deferred_no_selection",
        }[self.handoff_target]
        if self.required_next_surface != expected_required_surface:
            raise ValueError("required_next_surface must be narrower than handoff_target")
        if (
            self.candidate_ref == "candidate:internal:typed_adjudication_product_wedge"
            and self.handoff_target == "v72_contained_integration_review"
        ):
            raise ValueError("product wedge cannot be routed to V72")
        if (
            self.handoff_target == "v72_contained_integration_review"
            and self.handoff_posture != "ready_for_v72_review"
        ):
            raise ValueError("V72 handoff requires ready_for_v72_review posture")
        if (
            self.handoff_posture == "ready_for_v72_review"
            and self.handoff_target != "v72_contained_integration_review"
        ):
            raise ValueError("ready_for_v72_review requires V72 handoff target")
        if self.handoff_posture == "ready_for_v72_review" and (
            self.carried_forward_dissent_refs or self.carried_forward_gap_refs
        ):
            raise ValueError("ready_for_v72_review cannot carry blocking dissent or gaps")
        return self


class RepoPostRatificationHandoff(_CartographyBase):
    schema: Literal["repo_post_ratification_handoff@1"] = REPO_POST_RATIFICATION_HANDOFF_SCHEMA
    post_ratification_handoff_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    ratification_record_id: str
    amendment_scope_boundary_id: str
    handoff_rows: list[RepoPostRatificationHandoffRow] = Field(min_length=1)
    non_integration_summary: str

    @model_validator(mode="after")
    def _validate_handoff(self) -> RepoPostRatificationHandoff:
        object.__setattr__(
            self,
            "post_ratification_handoff_id",
            _non_empty(
                self.post_ratification_handoff_id,
                field_name="post_ratification_handoff_id",
            ),
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
            "ratification_record_id",
            _non_empty(self.ratification_record_id, field_name="ratification_record_id"),
        )
        object.__setattr__(
            self,
            "amendment_scope_boundary_id",
            _non_empty(
                self.amendment_scope_boundary_id,
                field_name="amendment_scope_boundary_id",
            ),
        )
        object.__setattr__(
            self,
            "handoff_rows",
            _sorted_unique_by_ref(
                self.handoff_rows,
                attr="handoff_ref",
                field_name="handoff_rows",
            ),
        )
        object.__setattr__(
            self,
            "non_integration_summary",
            _v71c_non_authority_guardrail(
                self.non_integration_summary, field_name="non_integration_summary"
            ),
        )
        expected_id = _surface_id(
            "repo_post_ratification_handoff",
            REPO_POST_RATIFICATION_HANDOFF_SCHEMA,
            self.model_dump(mode="json"),
            "post_ratification_handoff_id",
        )
        if self.post_ratification_handoff_id != expected_id:
            raise ValueError(
                "post_ratification_handoff_id must match canonical full payload hash identity"
            )
        return self


class RepoCandidateRatificationFamilyCloseoutRow(_CartographyBase):
    candidate_ref: str
    ratification_refs: list[str] = Field(min_length=1)
    amendment_scope_refs: list[str] = Field(min_length=1)
    handoff_refs: list[str] = Field(min_length=1)
    closeout_posture: FamilyCandidateCloseoutPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_family_closeout_row(self) -> RepoCandidateRatificationFamilyCloseoutRow:
        object.__setattr__(
            self,
            "candidate_ref",
            _non_empty(self.candidate_ref, field_name="candidate_ref"),
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
            "handoff_refs",
            _sorted_unique(self.handoff_refs, field_name="handoff_refs"),
        )
        object.__setattr__(
            self,
            "limitation_note",
            _v71c_note(self.limitation_note, field_name="limitation_note"),
        )
        return self


class RepoCandidateRatificationFamilyCloseoutAlignment(_CartographyBase):
    schema: Literal["repo_candidate_ratification_family_closeout_alignment@1"] = (
        REPO_CANDIDATE_RATIFICATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
    )
    family_closeout_alignment_id: str
    family_id: str
    snapshot_id: str
    source_set_id: str
    closed_slices: list[str] = Field(min_length=1)
    consumed_record_shapes: list[str] = Field(min_length=1)
    emitted_record_shapes: list[str] = Field(min_length=1)
    candidate_rows: list[RepoCandidateRatificationFamilyCloseoutRow] = Field(min_length=1)
    future_family_refs: list[str] = Field(default_factory=list)
    non_authority_guardrail: str

    @model_validator(mode="after")
    def _validate_family_closeout_alignment(
        self,
    ) -> RepoCandidateRatificationFamilyCloseoutAlignment:
        object.__setattr__(
            self,
            "family_closeout_alignment_id",
            _non_empty(
                self.family_closeout_alignment_id,
                field_name="family_closeout_alignment_id",
            ),
        )
        object.__setattr__(self, "family_id", _non_empty(self.family_id, field_name="family_id"))
        object.__setattr__(
            self, "snapshot_id", _non_empty(self.snapshot_id, field_name="snapshot_id")
        )
        object.__setattr__(
            self, "source_set_id", _non_empty(self.source_set_id, field_name="source_set_id")
        )
        object.__setattr__(
            self, "closed_slices", _sorted_unique(self.closed_slices, field_name="closed_slices")
        )
        object.__setattr__(
            self,
            "consumed_record_shapes",
            _sorted_unique(self.consumed_record_shapes, field_name="consumed_record_shapes"),
        )
        object.__setattr__(
            self,
            "emitted_record_shapes",
            _sorted_unique(self.emitted_record_shapes, field_name="emitted_record_shapes"),
        )
        object.__setattr__(
            self,
            "candidate_rows",
            _sorted_unique_by_ref(
                self.candidate_rows,
                attr="candidate_ref",
                field_name="candidate_rows",
            ),
        )
        object.__setattr__(
            self,
            "future_family_refs",
            _sorted_unique(self.future_family_refs, field_name="future_family_refs"),
        )
        object.__setattr__(
            self,
            "non_authority_guardrail",
            _v71c_non_authority_guardrail(
                self.non_authority_guardrail, field_name="non_authority_guardrail"
            ),
        )
        if self.closed_slices != ["V71-A", "V71-B", "V71-C"]:
            raise ValueError("family closeout alignment must close V71-A, V71-B, and V71-C")
        for forbidden_shape in (
            "repo_contained_integration_record@1",
            "repo_product_authorization@1",
            "repo_release_authority@1",
        ):
            if forbidden_shape in self.emitted_record_shapes:
                raise ValueError("family closeout alignment may not emit downstream authority")
        expected_id = _surface_id(
            "repo_candidate_ratification_family_closeout_alignment",
            REPO_CANDIDATE_RATIFICATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            self.model_dump(mode="json"),
            "family_closeout_alignment_id",
        )
        if self.family_closeout_alignment_id != expected_id:
            raise ValueError(
                "family_closeout_alignment_id must match canonical full payload hash identity"
            )
        return self


_V71B_RATIFICATION_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus198/"
    "repo_candidate_ratification_record_v198_reference.json"
)
_V71B_SETTLEMENT_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus198/"
    "repo_review_settlement_record_v198_reference.json"
)
_V71B_DISSENT_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus198/"
    "repo_ratification_dissent_register_v198_reference.json"
)


def _v71c_load_ratification(repo_root: Path) -> RepoCandidateRatificationRecord:
    return RepoCandidateRatificationRecord.model_validate(
        _load_json(repo_root, _V71B_RATIFICATION_FIXTURE)
    )


def _v71c_load_settlement(repo_root: Path) -> RepoReviewSettlementRecord:
    return RepoReviewSettlementRecord.model_validate(
        _load_json(repo_root, _V71B_SETTLEMENT_FIXTURE)
    )


def _v71c_load_dissent(repo_root: Path) -> RepoRatificationDissentRegister:
    return RepoRatificationDissentRegister.model_validate(
        _load_json(repo_root, _V71B_DISSENT_FIXTURE)
    )


def validate_v71c_candidate_ratification_closeout_bundle(
    *,
    ratification_record: RepoCandidateRatificationRecord,
    settlement_record: RepoReviewSettlementRecord,
    dissent_register: RepoRatificationDissentRegister,
    amendment_scope_boundary: RepoRatificationAmendmentScopeBoundary,
    post_ratification_handoff: RepoPostRatificationHandoff,
    family_closeout_alignment: RepoCandidateRatificationFamilyCloseoutAlignment,
) -> None:
    if (
        amendment_scope_boundary.ratification_record_id
        != ratification_record.ratification_record_id
    ):
        raise ValueError("amendment scope must reference V71-B ratification record")
    if amendment_scope_boundary.settlement_register_id != settlement_record.settlement_register_id:
        raise ValueError("amendment scope must reference V71-B settlement record")
    if amendment_scope_boundary.dissent_register_id != dissent_register.dissent_register_id:
        raise ValueError("amendment scope must reference V71-B dissent register")
    if (
        post_ratification_handoff.ratification_record_id
        != ratification_record.ratification_record_id
    ):
        raise ValueError("post-ratification handoff must reference V71-B ratification record")
    if (
        post_ratification_handoff.amendment_scope_boundary_id
        != amendment_scope_boundary.amendment_scope_boundary_id
    ):
        raise ValueError("post-ratification handoff must reference amendment scope boundary")
    if amendment_scope_boundary.source_set_id != ratification_record.source_set_id:
        raise ValueError("amendment scope source_set_id must match ratification record")
    if post_ratification_handoff.source_set_id != ratification_record.source_set_id:
        raise ValueError("handoff source_set_id must match ratification record")
    if family_closeout_alignment.source_set_id != ratification_record.source_set_id:
        raise ValueError("family closeout source_set_id must match ratification record")

    ratification_rows = {row.ratification_ref: row for row in ratification_record.ratification_rows}
    settlement_rows = {row.settlement_ref: row for row in settlement_record.settlement_rows}
    dissent_rows = {row.dissent_ref: row for row in dissent_register.dissent_rows}
    amendment_rows = {
        row.amendment_scope_ref: row for row in amendment_scope_boundary.amendment_scope_rows
    }
    handoff_rows = {row.handoff_ref: row for row in post_ratification_handoff.handoff_rows}

    for scope_row in amendment_scope_boundary.amendment_scope_rows:
        for ratification_ref in scope_row.ratification_refs:
            ratification = ratification_rows.get(ratification_ref)
            if ratification is None:
                raise ValueError("amendment scope rows must reference known ratification rows")
            if scope_row.candidate_ref != ratification.candidate_ref:
                raise ValueError("amendment scope candidate_ref must match ratification")
            if ratification.decision_posture != "ratified" and (
                "v72_contained_integration_review" in scope_row.allowed_next_review_surfaces
            ):
                raise ValueError("rejected or deferred candidates cannot be routed to V72")
        for settlement_ref in scope_row.settlement_refs:
            settlement = settlement_rows.get(settlement_ref)
            if settlement is None:
                raise ValueError("amendment scope rows must reference known settlement rows")
            if settlement.candidate_ref != scope_row.candidate_ref:
                raise ValueError("amendment scope candidate_ref must match settlement")

    for handoff in post_ratification_handoff.handoff_rows:
        for ratification_ref in handoff.ratification_refs:
            ratification = ratification_rows.get(ratification_ref)
            if ratification is None:
                raise ValueError("handoff rows must reference known ratification rows")
            if handoff.candidate_ref != ratification.candidate_ref:
                raise ValueError("handoff candidate_ref must match ratification")
            if ratification.decision_posture != "ratified" and (
                handoff.handoff_target == "v72_contained_integration_review"
                or handoff.handoff_posture == "ready_for_v72_review"
            ):
                raise ValueError("rejected or deferred candidates cannot be routed to V72")
            if (
                ratification.candidate_ref == "candidate:internal:typed_adjudication_product_wedge"
                and handoff.handoff_target == "v72_contained_integration_review"
            ):
                raise ValueError("product wedge cannot be routed to V72")
            for ref in ratification.dissent_refs:
                if ref not in dissent_rows:
                    raise ValueError(f"ratification references unknown dissent: {ref}")
            required_dissent_refs = sorted(
                ref
                for ref in ratification.dissent_refs
                if dissent_rows[ref].carry_forward_required
                or dissent_rows[ref].dissent_posture
                in {
                    "dissent_carried_forward",
                    "minority_review_preserved",
                    "unresolved_blocker",
                }
            )
            missing_dissent = sorted(
                set(required_dissent_refs) - set(handoff.carried_forward_dissent_refs)
            )
            if missing_dissent:
                raise ValueError(f"handoff must carry forward dissent refs: {missing_dissent}")
            required_gap_refs: set[str] = set()
            for settlement_ref in ratification.settlement_refs:
                settlement = settlement_rows.get(settlement_ref)
                if settlement is None:
                    raise ValueError(
                        f"ratification references unknown settlement: {settlement_ref}"
                    )
                if settlement.settlement_posture in {
                    "partially_settled_with_dissent",
                    "blocked_by_unresolved_conflict",
                    "blocked_by_unresolved_gap",
                    "requires_more_evidence",
                    "requires_human_review",
                    "future_family_only",
                }:
                    required_gap_refs.update(settlement.carried_forward_refs)
                    required_gap_refs.update(settlement.source_gap_refs)
            missing_gaps = sorted(required_gap_refs - set(handoff.carried_forward_gap_refs))
            if missing_gaps:
                raise ValueError(f"handoff must carry forward evidence gap refs: {missing_gaps}")
        for amendment_scope_ref in handoff.amendment_scope_refs:
            amendment = amendment_rows.get(amendment_scope_ref)
            if amendment is None:
                raise ValueError("handoff rows must reference known amendment scope rows")
            if amendment.candidate_ref != handoff.candidate_ref:
                raise ValueError("handoff candidate_ref must match amendment scope")

    candidate_refs = {row.candidate_ref for row in ratification_record.ratification_rows}
    closeout_candidate_refs = {
        row.candidate_ref for row in family_closeout_alignment.candidate_rows
    }
    if closeout_candidate_refs != candidate_refs:
        raise ValueError("family closeout alignment must cover every V71 ratification candidate")
    for row in family_closeout_alignment.candidate_rows:
        for ratification_ref in row.ratification_refs:
            ratification = ratification_rows.get(ratification_ref)
            if ratification is None:
                raise ValueError("family closeout rows must reference known ratification rows")
            if ratification.candidate_ref != row.candidate_ref:
                raise ValueError("family closeout candidate_ref must match ratification")
        for amendment_scope_ref in row.amendment_scope_refs:
            amendment = amendment_rows.get(amendment_scope_ref)
            if amendment is None:
                raise ValueError("family closeout rows must reference known amendment scopes")
            if amendment.candidate_ref != row.candidate_ref:
                raise ValueError("family closeout candidate_ref must match amendment scope")
        for handoff_ref in row.handoff_refs:
            handoff = handoff_rows.get(handoff_ref)
            if handoff is None:
                raise ValueError("family closeout rows must reference known handoff rows")
            if handoff.candidate_ref != row.candidate_ref:
                raise ValueError("family closeout candidate_ref must match handoff")


def derive_v71c_repo_ratification_amendment_scope_boundary(
    *,
    repo_root: Path,
    ratification_record: RepoCandidateRatificationRecord | None = None,
    settlement_record: RepoReviewSettlementRecord | None = None,
    dissent_register: RepoRatificationDissentRegister | None = None,
) -> RepoRatificationAmendmentScopeBoundary:
    ratification = ratification_record or _v71c_load_ratification(repo_root)
    settlement = settlement_record or _v71c_load_settlement(repo_root)
    dissent = dissent_register or _v71c_load_dissent(repo_root)
    rows = [
        RepoRatificationAmendmentScopeBoundaryRow(
            amendment_scope_ref="amendment:v71c:odeu-diff:blocked-by-dissent",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            ratification_refs=["ratification:v71b:odeu-diff:deferred-with-dissent"],
            settlement_refs=["settlement:v71b:odeu-diff:partial-with-dissent"],
            allowed_amendment_scope="no_amendment_scope",
            forbidden_downstream_roles=sorted(_V71C_FORBIDDEN_SET),
            allowed_next_review_surfaces=["deferred_no_selection"],
            scope_limitation_note="Dissent and evidence gaps block amendment scope here.",
            non_release_guardrail=_V71C_NON_AUTHORITY_GUARDRAIL,
        ),
        RepoRatificationAmendmentScopeBoundaryRow(
            amendment_scope_ref="amendment:v71c:product-wedge:future-family",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            ratification_refs=["ratification:v71b:product-wedge:future-family"],
            settlement_refs=["settlement:v71b:product-wedge:future-family"],
            allowed_amendment_scope="future_family_only",
            forbidden_downstream_roles=sorted(_V71C_FORBIDDEN_SET),
            allowed_next_review_surfaces=["future_family_review"],
            scope_limitation_note="Product pressure remains future-family only.",
            non_release_guardrail=_V71C_NON_AUTHORITY_GUARDRAIL,
        ),
        RepoRatificationAmendmentScopeBoundaryRow(
            amendment_scope_ref="amendment:v71c:self-evidencing:schema-review",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            ratification_refs=["ratification:v71b:self-evidencing:source-bound-validity"],
            settlement_refs=["settlement:v71b:self-evidencing:complementary"],
            allowed_amendment_scope="schema_review_candidate",
            forbidden_downstream_roles=sorted(_V71C_FORBIDDEN_SET),
            allowed_next_review_surfaces=["v72_contained_integration_review"],
            scope_limitation_note="Later review may consider schema containment only.",
            non_release_guardrail=_V71C_NON_AUTHORITY_GUARDRAIL,
        ),
    ]
    payload = {
        "schema": REPO_RATIFICATION_AMENDMENT_SCOPE_BOUNDARY_SCHEMA,
        "review_id": "review:v71c:amendment-scope-handoff",
        "snapshot_id": "vNext+199-prestart-on-main",
        "source_set_id": ratification.source_set_id,
        "ratification_record_id": ratification.ratification_record_id,
        "settlement_register_id": settlement.settlement_register_id,
        "dissent_register_id": dissent.dissent_register_id,
        "amendment_scope_rows": [
            row.model_dump(mode="json")
            for row in sorted(rows, key=lambda row: row.amendment_scope_ref)
        ],
        "non_authority_summary": _V71C_NON_AUTHORITY_GUARDRAIL,
    }
    payload["amendment_scope_boundary_id"] = _surface_id(
        "repo_ratification_amendment_scope_boundary",
        REPO_RATIFICATION_AMENDMENT_SCOPE_BOUNDARY_SCHEMA,
        payload,
        "amendment_scope_boundary_id",
    )
    return RepoRatificationAmendmentScopeBoundary.model_validate(payload)


def derive_v71c_repo_post_ratification_handoff(
    *,
    repo_root: Path,
    ratification_record: RepoCandidateRatificationRecord | None = None,
    amendment_scope_boundary: RepoRatificationAmendmentScopeBoundary | None = None,
) -> RepoPostRatificationHandoff:
    ratification = ratification_record or _v71c_load_ratification(repo_root)
    amendment_scope = (
        amendment_scope_boundary
        or derive_v71c_repo_ratification_amendment_scope_boundary(
            repo_root=repo_root,
            ratification_record=ratification,
        )
    )
    rows = [
        RepoPostRatificationHandoffRow(
            handoff_ref="handoff:v71c:odeu-diff:blocked-by-dissent",
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            ratification_refs=["ratification:v71b:odeu-diff:deferred-with-dissent"],
            amendment_scope_refs=["amendment:v71c:odeu-diff:blocked-by-dissent"],
            handoff_target="deferred_no_selection",
            handoff_posture="blocked_by_dissent",
            required_next_surface="deferred_no_selection",
            carried_forward_dissent_refs=["dissent:v71b:odeu-diff:minority-preserved"],
            carried_forward_gap_refs=[
                "gap:v70b:odeu-diff:missing-counterevidence",
            ],
            non_integration_guardrail=_V71C_NON_AUTHORITY_GUARDRAIL,
        ),
        RepoPostRatificationHandoffRow(
            handoff_ref="handoff:v71c:product-wedge:future-family",
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            ratification_refs=["ratification:v71b:product-wedge:future-family"],
            amendment_scope_refs=["amendment:v71c:product-wedge:future-family"],
            handoff_target="future_family_review",
            handoff_posture="deferred_to_future_family",
            required_next_surface="future_family_candidate_review",
            carried_forward_dissent_refs=[],
            carried_forward_gap_refs=[
                "gap:v70b:product-wedge:single-source-overclaim",
                "gap:v70b:product-wedge:v74-boundary",
            ],
            non_integration_guardrail=_V71C_NON_AUTHORITY_GUARDRAIL,
        ),
        RepoPostRatificationHandoffRow(
            handoff_ref="handoff:v71c:self-evidencing:v72-review",
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            ratification_refs=["ratification:v71b:self-evidencing:source-bound-validity"],
            amendment_scope_refs=["amendment:v71c:self-evidencing:schema-review"],
            handoff_target="v72_contained_integration_review",
            handoff_posture="ready_for_v72_review",
            required_next_surface="v72_candidate_containment_planning",
            carried_forward_dissent_refs=[],
            carried_forward_gap_refs=[],
            non_integration_guardrail=_V71C_NON_AUTHORITY_GUARDRAIL,
        ),
    ]
    payload = {
        "schema": REPO_POST_RATIFICATION_HANDOFF_SCHEMA,
        "review_id": amendment_scope.review_id,
        "snapshot_id": amendment_scope.snapshot_id,
        "source_set_id": ratification.source_set_id,
        "ratification_record_id": ratification.ratification_record_id,
        "amendment_scope_boundary_id": amendment_scope.amendment_scope_boundary_id,
        "handoff_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.handoff_ref)
        ],
        "non_integration_summary": _V71C_NON_AUTHORITY_GUARDRAIL,
    }
    payload["post_ratification_handoff_id"] = _surface_id(
        "repo_post_ratification_handoff",
        REPO_POST_RATIFICATION_HANDOFF_SCHEMA,
        payload,
        "post_ratification_handoff_id",
    )
    return RepoPostRatificationHandoff.model_validate(payload)


def derive_v71c_repo_candidate_ratification_family_closeout_alignment(
    *,
    repo_root: Path,
    ratification_record: RepoCandidateRatificationRecord | None = None,
    amendment_scope_boundary: RepoRatificationAmendmentScopeBoundary | None = None,
) -> RepoCandidateRatificationFamilyCloseoutAlignment:
    ratification = ratification_record or _v71c_load_ratification(repo_root)
    amendment_scope = (
        amendment_scope_boundary
        or derive_v71c_repo_ratification_amendment_scope_boundary(
            repo_root=repo_root,
            ratification_record=ratification,
        )
    )
    rows = [
        RepoCandidateRatificationFamilyCloseoutRow(
            candidate_ref="candidate:internal:odeu_conceptual_diff_report@1",
            ratification_refs=["ratification:v71b:odeu-diff:deferred-with-dissent"],
            amendment_scope_refs=["amendment:v71c:odeu-diff:blocked-by-dissent"],
            handoff_refs=["handoff:v71c:odeu-diff:blocked-by-dissent"],
            closeout_posture="deferred_with_dissent",
            limitation_note="Deferred with dissent and counterevidence gap carried forward.",
        ),
        RepoCandidateRatificationFamilyCloseoutRow(
            candidate_ref="candidate:internal:typed_adjudication_product_wedge",
            ratification_refs=["ratification:v71b:product-wedge:future-family"],
            amendment_scope_refs=["amendment:v71c:product-wedge:future-family"],
            handoff_refs=["handoff:v71c:product-wedge:future-family"],
            closeout_posture="future_family_routed",
            limitation_note="Product pressure remains future-family routed.",
        ),
        RepoCandidateRatificationFamilyCloseoutRow(
            candidate_ref="candidate:internal:self_evidencing_workflow_type_emergence",
            ratification_refs=["ratification:v71b:self-evidencing:source-bound-validity"],
            amendment_scope_refs=["amendment:v71c:self-evidencing:schema-review"],
            handoff_refs=["handoff:v71c:self-evidencing:v72-review"],
            closeout_posture="ratified_for_later_review",
            limitation_note="Ratified only for later bounded review, not implementation.",
        ),
    ]
    payload = {
        "schema": REPO_CANDIDATE_RATIFICATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
        "family_id": "V71",
        "snapshot_id": amendment_scope.snapshot_id,
        "source_set_id": ratification.source_set_id,
        "closed_slices": ["V71-A", "V71-B", "V71-C"],
        "consumed_record_shapes": sorted(
            [
                REPO_CANDIDATE_RATIFICATION_RECORD_SCHEMA,
                REPO_REVIEW_SETTLEMENT_RECORD_SCHEMA,
                REPO_RATIFICATION_DISSENT_REGISTER_SCHEMA,
            ]
        ),
        "emitted_record_shapes": sorted(
            [
                REPO_CANDIDATE_RATIFICATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
                REPO_POST_RATIFICATION_HANDOFF_SCHEMA,
                REPO_RATIFICATION_AMENDMENT_SCOPE_BOUNDARY_SCHEMA,
            ]
        ),
        "candidate_rows": [
            row.model_dump(mode="json") for row in sorted(rows, key=lambda row: row.candidate_ref)
        ],
        "future_family_refs": ["V72", "V73", "V74", "V75"],
        "non_authority_guardrail": _V71C_NON_AUTHORITY_GUARDRAIL,
    }
    payload["family_closeout_alignment_id"] = _surface_id(
        "repo_candidate_ratification_family_closeout_alignment",
        REPO_CANDIDATE_RATIFICATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
        payload,
        "family_closeout_alignment_id",
    )
    return RepoCandidateRatificationFamilyCloseoutAlignment.model_validate(payload)


def derive_v71c_repo_candidate_ratification_closeout_bundle(
    *,
    repo_root: Path,
) -> tuple[
    RepoCandidateRatificationRecord,
    RepoReviewSettlementRecord,
    RepoRatificationDissentRegister,
    RepoRatificationAmendmentScopeBoundary,
    RepoPostRatificationHandoff,
    RepoCandidateRatificationFamilyCloseoutAlignment,
]:
    ratification = _v71c_load_ratification(repo_root)
    settlement = _v71c_load_settlement(repo_root)
    dissent = _v71c_load_dissent(repo_root)
    amendment_scope = derive_v71c_repo_ratification_amendment_scope_boundary(
        repo_root=repo_root,
        ratification_record=ratification,
        settlement_record=settlement,
        dissent_register=dissent,
    )
    handoff = derive_v71c_repo_post_ratification_handoff(
        repo_root=repo_root,
        ratification_record=ratification,
        amendment_scope_boundary=amendment_scope,
    )
    closeout = derive_v71c_repo_candidate_ratification_family_closeout_alignment(
        repo_root=repo_root,
        ratification_record=ratification,
        amendment_scope_boundary=amendment_scope,
    )
    validate_v71c_candidate_ratification_closeout_bundle(
        ratification_record=ratification,
        settlement_record=settlement,
        dissent_register=dissent,
        amendment_scope_boundary=amendment_scope,
        post_ratification_handoff=handoff,
        family_closeout_alignment=closeout,
    )
    return ratification, settlement, dissent, amendment_scope, handoff, closeout
