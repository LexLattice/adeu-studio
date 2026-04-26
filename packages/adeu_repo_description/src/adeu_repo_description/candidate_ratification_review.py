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
_DOWNSTREAM_FORBIDDEN_SET: set[ForbiddenDownstreamRole] = {
    "implementation_task",
    "contained_integration",
    "commit_release_authority",
    "product_authorization",
    "runtime_permission",
    "dispatch_authority",
}


def _v71a_note(value: str, *, field_name: str) -> str:
    normalized = _non_authority_note(value, field_name=field_name)
    lowered = normalized.lower()
    if any(term in lowered for term in _FORBIDDEN_V71A_AUTHORITY_TERMS):
        raise ValueError(f"{field_name} may not carry downstream or final ratification authority")
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
