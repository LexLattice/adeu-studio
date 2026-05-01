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
from .dispatch_review import (
    RepoDispatchReconciliationContract,
    RepoDispatchReviewFamilyCloseoutAlignment,
    RepoPostDispatchReviewHandoff,
    RepoWorkerOutputReconciliationPlan,
    _reject_unnegated_authority_claim,
    _require_terms,
    derive_v75c_dispatch_review_closeout_bundle,
)
from .recursive_candidate_intake import (
    CandidateAuthorityLayer,
    CandidateSourceKind,
    CandidateSourcePresencePosture,
)

REPO_RECONCILIATION_CLAIM_MAP_SCHEMA = "repo_reconciliation_claim_map@1"
REPO_ARBITER_RELATION_REGISTER_SCHEMA = "repo_arbiter_relation_register@1"
REPO_RECONCILIATION_DISSENT_REGISTER_SCHEMA = "repo_reconciliation_dissent_register@1"
REPO_ARBITER_AUTHORITY_PROFILE_SCHEMA = "repo_arbiter_authority_profile@1"
REPO_RECONCILIATION_SETTLEMENT_REQUEST_SCHEMA = (
    "repo_reconciliation_settlement_request@1"
)
REPO_ADVERSARIAL_RELATION_REVIEW_SCHEMA = "repo_adversarial_relation_review@1"
REPO_RECONCILIATION_GAP_SCAN_SCHEMA = "repo_reconciliation_gap_scan@1"

ReconciliationSourceRole = Literal[
    "v75_reconciliation_plan_source",
    "v75_relation_row_source",
    "v75_reconciliation_contract_source",
    "v75_post_dispatch_review_handoff_source",
    "v75_family_closeout_source",
    "combined_dogfood_source",
    "support_review_source",
    "absence_marker",
]
OutputPresencePosture = Literal[
    "projected_not_observed",
    "observed_from_authorized_prior_run",
    "observed_from_support_artifact",
    "missing_expected_output",
    "not_applicable",
]
ReconciliationClaimKind = Literal[
    "projected_output_slot_existence",
    "projected_relation_review_need",
    "observed_output_content_claim",
    "observed_model_output_claim",
    "support_artifact_output_claim",
    "relation_placeholder_claim",
]
ClaimPresencePosture = Literal[
    "claim_mapped_from_projected_slot",
    "claim_mapped_from_observed_output",
    "claim_missing_expected_source",
    "claim_absent_not_applicable",
    "unknown_needs_review",
]
ClaimMapPosture = Literal[
    "mapped_for_reconciliation_review",
    "blocked_by_projected_not_observed",
    "blocked_by_missing_relation_source",
    "blocked_by_required_later_authority",
    "future_family_only",
    "rejected_out_of_scope",
]
ArbiterRelationKind = Literal[
    "conflict",
    "complementarity",
    "duplicate",
    "orthogonal",
    "unclear_relation",
    "single_output_no_relation",
]
RelationReviewPosture = Literal[
    "visible_unsettled",
    "requires_arbiter_review",
    "requires_adversarial_review",
    "blocked_by_missing_source",
    "blocked_by_no_observed_output",
    "deferred_no_selection",
]
ArbiterNeedPosture = Literal[
    "arbiter_review_needed_later",
    "arbiter_not_needed_for_single_output",
    "arbiter_blocked_by_missing_authority",
    "arbiter_deferred_to_future_family",
    "arbiter_rejected_out_of_scope",
]
ReconciliationNextReviewSurface = Literal[
    "future_runtime_permission_review",
    "future_product_review",
    "future_external_branch_review",
    "future_outcome_review",
    "future_reconciliation_or_arbiter_review",
    "future_experiment_review",
    "future_family_review",
    "deferred_no_selection",
]
DissentKind = Literal[
    "source_gap_dissent",
    "relation_uncertainty_dissent",
    "authority_boundary_dissent",
    "product_authority_dissent",
    "runtime_authority_dissent",
    "no_dissent_recorded",
]
DissentPresencePosture = Literal[
    "dissent_present",
    "searched_none_found",
    "not_searched",
    "not_applicable",
    "unknown",
]
DissentSearchCoveragePosture = Literal[
    "searched_released_v75c_sources",
    "partially_checked",
    "not_searched",
    "not_applicable",
    "unknown",
]
DissentCarryForwardPosture = Literal[
    "carried_for_later_review",
    "warning_only",
    "blocking_until_reviewed",
    "not_applicable",
    "deferred_no_selection",
]
ArbiterAuthorityActorKind = Literal[
    "human_operator",
    "maintainer",
    "model_reviewer",
    "tool_validator",
    "support_doc_context",
    "external_reviewer",
]
ArbiterAuthorityGrantSourceKind = Literal[
    "repo_lock",
    "maintainer_record",
    "policy_doc",
    "support_doc",
    "transcript",
    "tool_output",
    "fixture_source",
    "absence_marker",
]
ArbiterAllowedReviewAction = Literal[
    "inspect_relation",
    "request_adversarial_review",
    "preserve_dissent",
    "classify_gap",
    "request_later_settlement_review",
    "request_future_family_review",
]
ArbiterForbiddenAuthorityKind = Literal[
    "settle_relation_now",
    "ratify_claim_now",
    "declare_truth_now",
    "authorize_runtime_now",
    "authorize_product_now",
    "authorize_release_now",
    "assign_worker_now",
    "dispatch_now",
    "select_model_now",
]
ArbiterAuthorityGapPosture = Literal[
    "review_only_authority",
    "authority_gap_missing",
    "blocked_pending_later_authority",
    "future_family_only",
    "rejected_out_of_scope",
]
SettlementRequestPosture = Literal[
    "request_ready_for_later_review",
    "blocked_by_authority_gap",
    "blocked_by_unreviewed_relation",
    "blocked_by_dissent",
    "blocked_by_missing_source",
    "future_family_only",
    "rejected_out_of_scope",
]
AdversarialReviewResultPosture = Literal[
    "counterevidence_found",
    "complementarity_found",
    "no_counterevidence_in_checked_horizon",
    "inconclusive",
    "blocked_by_missing_source",
]
ReconciliationGapKind = Literal[
    "missing_claim_map_source",
    "missing_relation_source",
    "unreviewed_dissent",
    "authority_profile_missing",
    "adversarial_review_missing",
    "product_authority_gap",
    "runtime_authority_gap",
    "external_branch_gap",
    "projected_slot_not_observed_for_content_claim",
    "observed_output_source_authority_missing",
    "benchmark_truth_guardrail_missing",
    "unknown_needs_review",
]
ReconciliationGapSeverity = Literal["blocking", "warning", "info", "unknown"]
ReconciliationGapBlockingPosture = Literal[
    "blocking_until_reviewed",
    "warning_only",
    "carried_for_future_family",
    "not_applicable",
]

_PROJECTED_ONLY_CLAIM_KINDS = {
    "projected_output_slot_existence",
    "projected_relation_review_need",
    "relation_placeholder_claim",
}


def _has_local_negation(value: str, *, index: int) -> bool:
    prefix = value[max(0, index - 18) : index]
    return any(marker in prefix for marker in ("no ", "not ", "without ", "forbidden ", "non-"))


def _reject_unnegated_phrases(
    value: str,
    *,
    field_name: str,
    phrases: list[str],
    authority_kind: str,
) -> None:
    lowered = value.lower()
    for phrase in phrases:
        start = 0
        while (index := lowered.find(phrase, start)) != -1:
            if not _has_local_negation(lowered, index=index):
                raise ValueError(f"{field_name} may not carry {authority_kind} authority")
            start = index + len(phrase)


def _reject_reconciliation_overclaim(value: str, *, field_name: str) -> str:
    _reject_unnegated_authority_claim(value, field_name=field_name)
    _reject_unnegated_phrases(
        value,
        field_name=field_name,
        phrases=[
            "settles truth",
            "settled truth",
            "declares truth",
            "majority agreement proves",
            "majority-as-correctness",
            "benchmark truth",
            "model selected",
            "is correct",
        ],
        authority_kind="truth or correctness",
    )
    return value


def _reject_settlement_overclaim(value: str, *, field_name: str) -> str:
    _reject_reconciliation_overclaim(value, field_name=field_name)
    _reject_unnegated_phrases(
        value,
        field_name=field_name,
        phrases=[
            "settlement complete",
            "settled relation",
            "settles relation",
            "ratifies claim",
            "claim is true",
            "truth authority",
            "implementation priority",
            "majority proves",
            "majority agreement proves",
        ],
        authority_kind="settlement or truth",
    )
    return value


class RepoReconciliationSourceRow(_CartographyBase):
    source_ref: str
    source_kind: CandidateSourceKind
    authority_layer: CandidateAuthorityLayer
    source_status: SourceStatus
    source_presence_posture: CandidateSourcePresencePosture
    reconciliation_source_role: ReconciliationSourceRole
    source_horizon: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_source_row(self) -> RepoReconciliationSourceRow:
        _repo_ref(self.source_ref, field_name="source_ref")
        _non_empty(self.source_horizon, field_name="source_horizon")
        _reject_reconciliation_overclaim(self.limitation_note, field_name="limitation_note")
        if (
            self.reconciliation_source_role != "absence_marker"
            and self.source_presence_posture != "present"
        ):
            raise ValueError("non-absence reconciliation source rows must be present")
        if (
            self.reconciliation_source_role == "absence_marker"
            and self.source_presence_posture == "present"
        ):
            raise ValueError("absence-marker reconciliation source rows must not be present")
        return self


class RepoReconciliationClaimMapRow(_CartographyBase):
    claim_map_ref: str
    candidate_ref: str
    output_claim_ref: str
    claim_kind: ReconciliationClaimKind
    claim_label: str
    reconciliation_plan_refs: list[str] = Field(min_length=1)
    projected_output_slot_refs: list[str] = Field(default_factory=list)
    observed_worker_output_refs: list[str] = Field(default_factory=list)
    v75_source_relation_refs: list[str] = Field(min_length=1)
    handoff_refs: list[str] = Field(default_factory=list)
    claim_horizon: str
    claim_source_refs: list[str] = Field(min_length=1)
    claim_presence_posture: ClaimPresencePosture
    output_presence_posture: OutputPresencePosture
    claim_map_posture: ClaimMapPosture
    source_refs: list[str] = Field(min_length=1)
    truth_status_forbidden: Literal[True]
    non_truth_guardrail: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_claim_map_row(self) -> RepoReconciliationClaimMapRow:
        for field_name in (
            "reconciliation_plan_refs",
            "projected_output_slot_refs",
            "observed_worker_output_refs",
            "v75_source_relation_refs",
            "handoff_refs",
            "claim_source_refs",
            "source_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for field_name in (
            "claim_map_ref",
            "candidate_ref",
            "output_claim_ref",
            "claim_label",
            "claim_horizon",
        ):
            _non_empty(getattr(self, field_name), field_name=field_name)
        for source_ref in self.source_refs + self.claim_source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        if self.output_presence_posture == "projected_not_observed":
            if self.observed_worker_output_refs:
                raise ValueError("projected claim maps must not carry observed worker outputs")
            if not self.projected_output_slot_refs:
                raise ValueError("projected claim maps require projected output slot refs")
            if self.claim_kind not in _PROJECTED_ONLY_CLAIM_KINDS:
                raise ValueError("projected output slots cannot become observed content claims")
        if (
            self.claim_kind
            in {
                "observed_output_content_claim",
                "observed_model_output_claim",
                "support_artifact_output_claim",
            }
            and not self.observed_worker_output_refs
        ):
            raise ValueError("observed output content claims require observed output refs")
        _reject_reconciliation_overclaim(
            self.non_truth_guardrail, field_name="non_truth_guardrail"
        )
        _reject_reconciliation_overclaim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.non_truth_guardrail,
            field_name="non_truth_guardrail",
            terms=("not truth", "review"),
        )
        if self.output_presence_posture == "projected_not_observed":
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("projected", "not observed"),
            )
        if (
            any("product-wedge" in ref for ref in self.handoff_refs + self.source_refs)
            and self.claim_map_posture == "mapped_for_reconciliation_review"
        ):
            raise ValueError("authority blockers must remain blocked or future-family-only")
        return self


class RepoReconciliationClaimMap(_CartographyBase):
    schema: Literal["repo_reconciliation_claim_map@1"] = REPO_RECONCILIATION_CLAIM_MAP_SCHEMA
    reconciliation_claim_map_id: str
    worker_output_reconciliation_plan_id: str
    post_dispatch_review_handoff_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    source_rows: list[RepoReconciliationSourceRow] = Field(min_length=1)
    claim_map_rows: list[RepoReconciliationClaimMapRow] = Field(min_length=1)
    claim_map_summary: str

    @model_validator(mode="after")
    def _validate_claim_map(self) -> RepoReconciliationClaimMap:
        object.__setattr__(
            self,
            "source_rows",
            _sorted_unique_by_ref(self.source_rows, attr="source_ref", field_name="source_rows"),
        )
        object.__setattr__(
            self,
            "claim_map_rows",
            _sorted_unique_by_ref(
                self.claim_map_rows,
                attr="claim_map_ref",
                field_name="claim_map_rows",
            ),
        )
        _require_terms(
            self.claim_map_summary,
            field_name="claim_map_summary",
            terms=("projected", "not truth", "v75-c"),
        )
        expected_id = _surface_id(
            "repo_reconciliation_claim_map",
            self.schema,
            self.model_dump(mode="json"),
            "reconciliation_claim_map_id",
        )
        if self.reconciliation_claim_map_id != expected_id:
            raise ValueError("reconciliation_claim_map_id does not match canonical payload hash")
        return self


class RepoArbiterRelationRow(_CartographyBase):
    arbiter_relation_ref: str
    claim_map_refs: list[str] = Field(min_length=1)
    source_relation_refs: list[str] = Field(min_length=1)
    relation_kind: ArbiterRelationKind
    relation_review_posture: RelationReviewPosture
    arbiter_need_posture: ArbiterNeedPosture
    required_next_review_surface: ReconciliationNextReviewSurface
    source_refs: list[str] = Field(min_length=1)
    non_truth_guardrail: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_arbiter_relation_row(self) -> RepoArbiterRelationRow:
        _non_empty(self.arbiter_relation_ref, field_name="arbiter_relation_ref")
        for field_name in ("claim_map_refs", "source_relation_refs", "source_refs"):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        _reject_reconciliation_overclaim(
            self.non_truth_guardrail, field_name="non_truth_guardrail"
        )
        _reject_reconciliation_overclaim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.non_truth_guardrail,
            field_name="non_truth_guardrail",
            terms=("not truth", "review"),
        )
        return self


class RepoArbiterRelationRegister(_CartographyBase):
    schema: Literal["repo_arbiter_relation_register@1"] = (
        REPO_ARBITER_RELATION_REGISTER_SCHEMA
    )
    arbiter_relation_register_id: str
    reconciliation_claim_map_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    relation_rows: list[RepoArbiterRelationRow] = Field(min_length=1)
    relation_register_summary: str

    @model_validator(mode="after")
    def _validate_relation_register(self) -> RepoArbiterRelationRegister:
        object.__setattr__(
            self,
            "relation_rows",
            _sorted_unique_by_ref(
                self.relation_rows,
                attr="arbiter_relation_ref",
                field_name="relation_rows",
            ),
        )
        _require_terms(
            self.relation_register_summary,
            field_name="relation_register_summary",
            terms=("relation", "not truth", "v75-c"),
        )
        expected_id = _surface_id(
            "repo_arbiter_relation_register",
            self.schema,
            self.model_dump(mode="json"),
            "arbiter_relation_register_id",
        )
        if self.arbiter_relation_register_id != expected_id:
            raise ValueError("arbiter_relation_register_id does not match canonical payload hash")
        return self


class RepoReconciliationDissentRow(_CartographyBase):
    dissent_ref: str
    claim_map_refs: list[str] = Field(min_length=1)
    relation_refs: list[str] = Field(min_length=1)
    dissent_kind: DissentKind
    dissent_presence_posture: DissentPresencePosture
    dissent_search_horizon_refs: list[str] = Field(default_factory=list)
    dissent_search_coverage_posture: DissentSearchCoveragePosture
    checked_source_refs: list[str] = Field(default_factory=list)
    unchecked_source_refs: list[str] = Field(default_factory=list)
    dissent_source_refs: list[str] = Field(default_factory=list)
    dissent_carry_forward_posture: DissentCarryForwardPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_dissent_row(self) -> RepoReconciliationDissentRow:
        _non_empty(self.dissent_ref, field_name="dissent_ref")
        for field_name in (
            "claim_map_refs",
            "relation_refs",
            "dissent_search_horizon_refs",
            "checked_source_refs",
            "unchecked_source_refs",
            "dissent_source_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in (
            self.checked_source_refs + self.unchecked_source_refs + self.dissent_source_refs
        ):
            _repo_ref(source_ref, field_name="source_refs")
        if self.dissent_presence_posture == "searched_none_found":
            if not self.dissent_search_horizon_refs or not self.checked_source_refs:
                raise ValueError(
                    "searched-none dissent rows require a search horizon and checked sources"
                )
            if self.dissent_search_coverage_posture == "not_searched":
                raise ValueError("searched-none dissent rows require checked coverage")
        if self.dissent_kind == "no_dissent_recorded" and (
            self.dissent_presence_posture != "searched_none_found"
        ):
            raise ValueError("no dissent recorded requires searched-none posture")
        _reject_reconciliation_overclaim(self.limitation_note, field_name="limitation_note")
        return self


class RepoReconciliationDissentRegister(_CartographyBase):
    schema: Literal["repo_reconciliation_dissent_register@1"] = (
        REPO_RECONCILIATION_DISSENT_REGISTER_SCHEMA
    )
    reconciliation_dissent_register_id: str
    reconciliation_claim_map_id: str
    arbiter_relation_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    dissent_rows: list[RepoReconciliationDissentRow] = Field(min_length=1)
    dissent_register_summary: str

    @model_validator(mode="after")
    def _validate_dissent_register(self) -> RepoReconciliationDissentRegister:
        object.__setattr__(
            self,
            "dissent_rows",
            _sorted_unique_by_ref(
                self.dissent_rows,
                attr="dissent_ref",
                field_name="dissent_rows",
            ),
        )
        _require_terms(
            self.dissent_register_summary,
            field_name="dissent_register_summary",
            terms=("dissent", "searched", "not truth"),
        )
        expected_id = _surface_id(
            "repo_reconciliation_dissent_register",
            self.schema,
            self.model_dump(mode="json"),
            "reconciliation_dissent_register_id",
        )
        if self.reconciliation_dissent_register_id != expected_id:
            raise ValueError(
                "reconciliation_dissent_register_id does not match canonical payload hash"
            )
        return self


class RepoArbiterAuthorityProfileRow(_CartographyBase):
    authority_profile_ref: str
    authority_actor_kind: ArbiterAuthorityActorKind
    authority_grant_source_kind: ArbiterAuthorityGrantSourceKind
    authority_source_refs: list[str] = Field(min_length=1)
    allowed_relation_horizons: list[str] = Field(min_length=1)
    allowed_review_actions: list[ArbiterAllowedReviewAction] = Field(min_length=1)
    forbidden_authority_kinds: list[ArbiterForbiddenAuthorityKind] = Field(min_length=1)
    authority_gap_posture: ArbiterAuthorityGapPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_authority_profile_row(self) -> RepoArbiterAuthorityProfileRow:
        _non_empty(self.authority_profile_ref, field_name="authority_profile_ref")
        for field_name in (
            "authority_source_refs",
            "allowed_relation_horizons",
            "allowed_review_actions",
            "forbidden_authority_kinds",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.authority_source_refs:
            _repo_ref(source_ref, field_name="authority_source_refs")
        _reject_settlement_overclaim(self.limitation_note, field_name="limitation_note")
        if self.authority_grant_source_kind in {
            "support_doc",
            "transcript",
            "tool_output",
        } and self.authority_gap_posture == "authority_gap_missing":
            raise ValueError("non-lock grant sources cannot become settlement authority")
        return self


class RepoArbiterAuthorityProfile(_CartographyBase):
    schema: Literal["repo_arbiter_authority_profile@1"] = (
        REPO_ARBITER_AUTHORITY_PROFILE_SCHEMA
    )
    arbiter_authority_profile_id: str
    reconciliation_claim_map_id: str
    arbiter_relation_register_id: str
    reconciliation_dissent_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    authority_profile_rows: list[RepoArbiterAuthorityProfileRow] = Field(min_length=1)
    authority_profile_summary: str

    @model_validator(mode="after")
    def _validate_authority_profile(self) -> RepoArbiterAuthorityProfile:
        object.__setattr__(
            self,
            "authority_profile_rows",
            _sorted_unique_by_ref(
                self.authority_profile_rows,
                attr="authority_profile_ref",
                field_name="authority_profile_rows",
            ),
        )
        _require_terms(
            self.authority_profile_summary,
            field_name="authority_profile_summary",
            terms=("review", "not truth", "not settlement"),
        )
        expected_id = _surface_id(
            "repo_arbiter_authority_profile",
            self.schema,
            self.model_dump(mode="json"),
            "arbiter_authority_profile_id",
        )
        if self.arbiter_authority_profile_id != expected_id:
            raise ValueError("arbiter_authority_profile_id does not match canonical payload hash")
        return self


class RepoReconciliationSettlementRequestRow(_CartographyBase):
    settlement_request_ref: str
    claim_map_refs: list[str] = Field(min_length=1)
    relation_refs: list[str] = Field(min_length=1)
    dissent_refs: list[str] = Field(default_factory=list)
    authority_profile_refs: list[str] = Field(min_length=1)
    requested_settlement_horizon: str
    settlement_request_posture: SettlementRequestPosture
    required_adversarial_review_refs: list[str] = Field(default_factory=list)
    carried_gap_refs: list[str] = Field(default_factory=list)
    non_settlement_guardrail: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_settlement_request_row(self) -> RepoReconciliationSettlementRequestRow:
        _non_empty(self.settlement_request_ref, field_name="settlement_request_ref")
        _non_empty(
            self.requested_settlement_horizon,
            field_name="requested_settlement_horizon",
        )
        for field_name in (
            "claim_map_refs",
            "relation_refs",
            "dissent_refs",
            "authority_profile_refs",
            "required_adversarial_review_refs",
            "carried_gap_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        _reject_settlement_overclaim(
            self.non_settlement_guardrail,
            field_name="non_settlement_guardrail",
        )
        _reject_settlement_overclaim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.non_settlement_guardrail,
            field_name="non_settlement_guardrail",
            terms=("request", "not settlement", "not truth"),
        )
        return self


class RepoReconciliationSettlementRequest(_CartographyBase):
    schema: Literal["repo_reconciliation_settlement_request@1"] = (
        REPO_RECONCILIATION_SETTLEMENT_REQUEST_SCHEMA
    )
    reconciliation_settlement_request_id: str
    reconciliation_claim_map_id: str
    arbiter_relation_register_id: str
    reconciliation_dissent_register_id: str
    arbiter_authority_profile_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    settlement_request_rows: list[RepoReconciliationSettlementRequestRow] = Field(
        min_length=1
    )
    settlement_request_summary: str

    @model_validator(mode="after")
    def _validate_settlement_request(self) -> RepoReconciliationSettlementRequest:
        object.__setattr__(
            self,
            "settlement_request_rows",
            _sorted_unique_by_ref(
                self.settlement_request_rows,
                attr="settlement_request_ref",
                field_name="settlement_request_rows",
            ),
        )
        _require_terms(
            self.settlement_request_summary,
            field_name="settlement_request_summary",
            terms=("request", "not settlement", "not truth"),
        )
        expected_id = _surface_id(
            "repo_reconciliation_settlement_request",
            self.schema,
            self.model_dump(mode="json"),
            "reconciliation_settlement_request_id",
        )
        if self.reconciliation_settlement_request_id != expected_id:
            raise ValueError(
                "reconciliation_settlement_request_id does not match canonical payload hash"
            )
        return self


class RepoAdversarialRelationReviewRow(_CartographyBase):
    adversarial_review_ref: str
    claim_map_refs: list[str] = Field(min_length=1)
    relation_refs: list[str] = Field(min_length=1)
    review_perspective: str
    counterclaim_horizon: str
    negative_control_refs: list[str] = Field(default_factory=list)
    review_result_posture: AdversarialReviewResultPosture
    source_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_adversarial_review_row(self) -> RepoAdversarialRelationReviewRow:
        for field_name in (
            "adversarial_review_ref",
            "review_perspective",
            "counterclaim_horizon",
        ):
            _non_empty(getattr(self, field_name), field_name=field_name)
        for field_name in (
            "claim_map_refs",
            "relation_refs",
            "negative_control_refs",
            "source_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        if (
            self.review_result_posture == "no_counterevidence_in_checked_horizon"
            and not self.counterclaim_horizon
            and not self.negative_control_refs
        ):
            raise ValueError("no-counterevidence review requires checked horizon or controls")
        _reject_settlement_overclaim(self.limitation_note, field_name="limitation_note")
        return self


class RepoAdversarialRelationReview(_CartographyBase):
    schema: Literal["repo_adversarial_relation_review@1"] = (
        REPO_ADVERSARIAL_RELATION_REVIEW_SCHEMA
    )
    adversarial_relation_review_id: str
    reconciliation_claim_map_id: str
    arbiter_relation_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    adversarial_review_rows: list[RepoAdversarialRelationReviewRow] = Field(min_length=1)
    adversarial_review_summary: str

    @model_validator(mode="after")
    def _validate_adversarial_review(self) -> RepoAdversarialRelationReview:
        object.__setattr__(
            self,
            "adversarial_review_rows",
            _sorted_unique_by_ref(
                self.adversarial_review_rows,
                attr="adversarial_review_ref",
                field_name="adversarial_review_rows",
            ),
        )
        _require_terms(
            self.adversarial_review_summary,
            field_name="adversarial_review_summary",
            terms=("adversarial", "not truth", "not settlement"),
        )
        expected_id = _surface_id(
            "repo_adversarial_relation_review",
            self.schema,
            self.model_dump(mode="json"),
            "adversarial_relation_review_id",
        )
        if self.adversarial_relation_review_id != expected_id:
            raise ValueError(
                "adversarial_relation_review_id does not match canonical payload hash"
            )
        return self


class RepoReconciliationGapRow(_CartographyBase):
    gap_ref: str
    claim_map_refs: list[str] = Field(min_length=1)
    relation_refs: list[str] = Field(min_length=1)
    gap_kind: ReconciliationGapKind
    gap_severity: ReconciliationGapSeverity
    blocking_posture: ReconciliationGapBlockingPosture
    required_next_surface: ReconciliationNextReviewSurface
    source_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_gap_row(self) -> RepoReconciliationGapRow:
        _non_empty(self.gap_ref, field_name="gap_ref")
        for field_name in ("claim_map_refs", "relation_refs", "source_refs"):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        _reject_settlement_overclaim(self.limitation_note, field_name="limitation_note")
        return self


class RepoReconciliationGapScan(_CartographyBase):
    schema: Literal["repo_reconciliation_gap_scan@1"] = REPO_RECONCILIATION_GAP_SCAN_SCHEMA
    reconciliation_gap_scan_id: str
    reconciliation_claim_map_id: str
    arbiter_relation_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    gap_rows: list[RepoReconciliationGapRow] = Field(min_length=1)
    gap_scan_summary: str

    @model_validator(mode="after")
    def _validate_gap_scan(self) -> RepoReconciliationGapScan:
        object.__setattr__(
            self,
            "gap_rows",
            _sorted_unique_by_ref(self.gap_rows, attr="gap_ref", field_name="gap_rows"),
        )
        _require_terms(
            self.gap_scan_summary,
            field_name="gap_scan_summary",
            terms=("gap", "not authority", "not truth"),
        )
        expected_id = _surface_id(
            "repo_reconciliation_gap_scan",
            self.schema,
            self.model_dump(mode="json"),
            "reconciliation_gap_scan_id",
        )
        if self.reconciliation_gap_scan_id != expected_id:
            raise ValueError("reconciliation_gap_scan_id does not match canonical payload hash")
        return self


def _v76b_base_payload(
    *,
    schema: str,
    reconciliation_claim_map: RepoReconciliationClaimMap,
    arbiter_relation_register: RepoArbiterRelationRegister,
    reconciliation_dissent_register: RepoReconciliationDissentRegister,
) -> dict[str, str]:
    return {
        "schema": schema,
        "review_id": "review:v76b:arbiter-authority-settlement-gap",
        "snapshot_id": "vNext+212-closed-on-main",
        "source_set_id": "source-set:v76b:released-v76a-reconciliation-arbiter",
        "reconciliation_claim_map_id": reconciliation_claim_map.reconciliation_claim_map_id,
        "arbiter_relation_register_id": (
            arbiter_relation_register.arbiter_relation_register_id
        ),
        "reconciliation_dissent_register_id": (
            reconciliation_dissent_register.reconciliation_dissent_register_id
        ),
    }


def _v76a_base_payload(
    *,
    schema: str,
    worker_output_reconciliation_plan: RepoWorkerOutputReconciliationPlan,
) -> dict[str, str]:
    return {
        "schema": schema,
        "review_id": "review:v76a:claim-relation-dissent-map",
        "snapshot_id": "vNext+211-closed-on-main",
        "source_set_id": "source-set:v76a:released-v75c-reconciliation",
        "worker_output_reconciliation_plan_id": (
            worker_output_reconciliation_plan.worker_output_reconciliation_plan_id
        ),
    }


def derive_v76a_repo_reconciliation_claim_map(
    *,
    repo_root: Path | None = None,
    worker_output_reconciliation_plan: RepoWorkerOutputReconciliationPlan | None = None,
    post_dispatch_review_handoff: RepoPostDispatchReviewHandoff | None = None,
) -> RepoReconciliationClaimMap:
    if worker_output_reconciliation_plan is None or post_dispatch_review_handoff is None:
        derived_plan, _, derived_handoff, _ = derive_v75c_dispatch_review_closeout_bundle(
            repo_root=repo_root
        )
        reconciliation_plan = worker_output_reconciliation_plan or derived_plan
        handoff = post_dispatch_review_handoff or derived_handoff
    else:
        reconciliation_plan = worker_output_reconciliation_plan
        handoff = post_dispatch_review_handoff
    payload = {
        **_v76a_base_payload(
            schema=REPO_RECONCILIATION_CLAIM_MAP_SCHEMA,
            worker_output_reconciliation_plan=reconciliation_plan,
        ),
        "reconciliation_claim_map_id": "",
        "post_dispatch_review_handoff_id": handoff.post_dispatch_review_handoff_id,
        "source_rows": [
            {
                "source_ref": (
                    "apps/api/fixtures/repo_description/vnext_plus211/"
                    "repo_dispatch_reconciliation_contract_v211_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "reconciliation_source_role": "v75_reconciliation_contract_source",
                "source_horizon": "released V75-C reconciliation contract fixture",
                "limitation_note": "Contract source is review substrate with no truth authority.",
            },
            {
                "source_ref": (
                    "apps/api/fixtures/repo_description/vnext_plus211/"
                    "repo_dispatch_review_family_closeout_alignment_v211_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "reconciliation_source_role": "v75_family_closeout_source",
                "source_horizon": "released V75 family closeout alignment fixture",
                "limitation_note": (
                    "Family closeout source is review substrate with no truth authority."
                ),
            },
            {
                "source_ref": (
                    "apps/api/fixtures/repo_description/vnext_plus211/"
                    "repo_post_dispatch_review_handoff_v211_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "reconciliation_source_role": "v75_post_dispatch_review_handoff_source",
                "source_horizon": "released V75-C post-dispatch-review handoff fixture",
                "limitation_note": "Handoff source is review-only with no dispatch authority.",
            },
            {
                "source_ref": (
                    "apps/api/fixtures/repo_description/vnext_plus211/"
                    "repo_worker_output_reconciliation_plan_v211_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "reconciliation_source_role": "v75_reconciliation_plan_source",
                "source_horizon": "released V75-C reconciliation plan fixture",
                "limitation_note": (
                    "Plan source is projected review substrate with no truth authority."
                ),
            },
            {
                "source_ref": (
                    "apps/api/fixtures/repo_description/vnext_plus211/"
                    "repo_worker_output_reconciliation_plan_v211_reference.json#relation_rows"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "reconciliation_source_role": "v75_relation_row_source",
                "source_horizon": "released V75-C relation rows inside reconciliation plan fixture",
                "limitation_note": (
                    "Relation row source is review substrate with no truth authority."
                ),
            },
            {
                "source_ref": (
                    "docs/support/arc_series_mapping/"
                    "V68_V69_V70_V71_V72_V73_V74_V75_COMBINED_DOGFOOD_TEST_v0.json"
                ),
                "source_kind": "support_doc",
                "authority_layer": "support",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "reconciliation_source_role": "combined_dogfood_source",
                "source_horizon": "combined support dogfood says no worker output was observed",
                "limitation_note": (
                    "Dogfood source contextualizes review and is not truth authority."
                ),
            },
        ],
        "claim_map_rows": [
            {
                "claim_map_ref": "claim-map:v76a:product-wedge:projected-authority-blocker",
                "candidate_ref": "candidate:internal:typed_adjudication_product_wedge",
                "output_claim_ref": "output-claim:v76a:product-wedge:projected-slot",
                "claim_kind": "projected_output_slot_existence",
                "claim_label": "Product wedge projected slot exists with blocker",
                "reconciliation_plan_refs": ["reconciliation-plan:v75c:product-wedge:blocked"],
                "projected_output_slot_refs": ["projected-output:v75c:product-wedge:blocked-note"],
                "observed_worker_output_refs": [],
                "v75_source_relation_refs": [
                    "relation:v75c:product-wedge:blocked-projected-output"
                ],
                "handoff_refs": ["handoff:v75c:product-wedge:arbiter-settlement"],
                "claim_horizon": (
                    "Projected product wedge output slot exists; no observed output content."
                ),
                "claim_source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus211/"
                    "repo_worker_output_reconciliation_plan_v211_reference.json",
                    "apps/api/fixtures/repo_description/vnext_plus211/"
                    "repo_worker_output_reconciliation_plan_v211_reference.json#relation_rows",
                ],
                "claim_presence_posture": "claim_mapped_from_projected_slot",
                "output_presence_posture": "projected_not_observed",
                "claim_map_posture": "blocked_by_required_later_authority",
                "source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus211/"
                    "repo_post_dispatch_review_handoff_v211_reference.json",
                    "apps/api/fixtures/repo_description/vnext_plus211/"
                    "repo_worker_output_reconciliation_plan_v211_reference.json",
                    "apps/api/fixtures/repo_description/vnext_plus211/"
                    "repo_worker_output_reconciliation_plan_v211_reference.json#relation_rows",
                ],
                "truth_status_forbidden": True,
                "non_truth_guardrail": "Projected output slot is for review and not truth.",
                "limitation_note": (
                    "Projected product slot is not observed and remains blocked by later authority."
                ),
            },
            {
                "claim_map_ref": "claim-map:v76a:self-evidencing:projected-relation-review",
                "candidate_ref": "candidate:internal:self_evidencing_workflow_type_emergence",
                "output_claim_ref": "output-claim:v76a:self-evidencing:relation-review-need",
                "claim_kind": "projected_relation_review_need",
                "claim_label": "Self-evidencing projected slot needs relation review",
                "reconciliation_plan_refs": [
                    "reconciliation-plan:v75c:self-evidencing:projected"
                ],
                "projected_output_slot_refs": [
                    "projected-output:v75c:self-evidencing:review-note"
                ],
                "observed_worker_output_refs": [],
                "v75_source_relation_refs": [
                    "relation:v75c:self-evidencing:single-projected-output"
                ],
                "handoff_refs": ["handoff:v75c:self-evidencing:future-outcome-review"],
                "claim_horizon": (
                    "Projected relation-review need exists; no observed output content."
                ),
                "claim_source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus211/"
                    "repo_worker_output_reconciliation_plan_v211_reference.json",
                    "apps/api/fixtures/repo_description/vnext_plus211/"
                    "repo_worker_output_reconciliation_plan_v211_reference.json#relation_rows",
                ],
                "claim_presence_posture": "claim_mapped_from_projected_slot",
                "output_presence_posture": "projected_not_observed",
                "claim_map_posture": "mapped_for_reconciliation_review",
                "source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus211/"
                    "repo_post_dispatch_review_handoff_v211_reference.json",
                    "apps/api/fixtures/repo_description/vnext_plus211/"
                    "repo_worker_output_reconciliation_plan_v211_reference.json",
                    "apps/api/fixtures/repo_description/vnext_plus211/"
                    "repo_worker_output_reconciliation_plan_v211_reference.json#relation_rows",
                ],
                "truth_status_forbidden": True,
                "non_truth_guardrail": (
                    "Projected relation-review need is for review and not truth."
                ),
                "limitation_note": "Projected relation-review need is not observed output content.",
            },
        ],
        "claim_map_summary": (
            "V76-A maps released V75-C projected slots from V75-C as review substrate, "
            "not truth and not observed output content."
        ),
    }
    payload["reconciliation_claim_map_id"] = _surface_id(
        "repo_reconciliation_claim_map",
        REPO_RECONCILIATION_CLAIM_MAP_SCHEMA,
        payload,
        "reconciliation_claim_map_id",
    )
    return RepoReconciliationClaimMap.model_validate(payload)


def derive_v76a_repo_arbiter_relation_register(
    *,
    repo_root: Path | None = None,
    reconciliation_claim_map: RepoReconciliationClaimMap | None = None,
) -> RepoArbiterRelationRegister:
    claim_map = reconciliation_claim_map or derive_v76a_repo_reconciliation_claim_map(
        repo_root=repo_root
    )
    payload = {
        "schema": REPO_ARBITER_RELATION_REGISTER_SCHEMA,
        "arbiter_relation_register_id": "",
        "reconciliation_claim_map_id": claim_map.reconciliation_claim_map_id,
        "review_id": claim_map.review_id,
        "snapshot_id": claim_map.snapshot_id,
        "source_set_id": claim_map.source_set_id,
        "relation_rows": [
            {
                "arbiter_relation_ref": "arbiter-relation:v76a:product-wedge:blocked-placeholder",
                "claim_map_refs": [
                    "claim-map:v76a:product-wedge:projected-authority-blocker"
                ],
                "source_relation_refs": [
                    "relation:v75c:product-wedge:blocked-projected-output"
                ],
                "relation_kind": "single_output_no_relation",
                "relation_review_posture": "blocked_by_no_observed_output",
                "arbiter_need_posture": "arbiter_blocked_by_missing_authority",
                "required_next_review_surface": "future_product_review",
                "source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus211/"
                    "repo_worker_output_reconciliation_plan_v211_reference.json#relation_rows"
                ],
                "non_truth_guardrail": "Arbiter relation placeholder is for review and not truth.",
                "limitation_note": (
                    "Projected relation placeholder is not truth and has no settlement."
                ),
            },
            {
                "arbiter_relation_ref": "arbiter-relation:v76a:self-evidencing:single-projected",
                "claim_map_refs": [
                    "claim-map:v76a:self-evidencing:projected-relation-review"
                ],
                "source_relation_refs": [
                    "relation:v75c:self-evidencing:single-projected-output"
                ],
                "relation_kind": "single_output_no_relation",
                "relation_review_posture": "requires_arbiter_review",
                "arbiter_need_posture": "arbiter_review_needed_later",
                "required_next_review_surface": "future_reconciliation_or_arbiter_review",
                "source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus211/"
                    "repo_worker_output_reconciliation_plan_v211_reference.json#relation_rows"
                ],
                "non_truth_guardrail": "Arbiter relation review is for review and not truth.",
                "limitation_note": "Single projected relation is not truth and not settled.",
            },
        ],
        "relation_register_summary": (
            "V76-A registers V75-C relation rows for relation review, not truth and not "
            "settlement."
        ),
    }
    payload["arbiter_relation_register_id"] = _surface_id(
        "repo_arbiter_relation_register",
        REPO_ARBITER_RELATION_REGISTER_SCHEMA,
        payload,
        "arbiter_relation_register_id",
    )
    return RepoArbiterRelationRegister.model_validate(payload)


def derive_v76a_repo_reconciliation_dissent_register(
    *,
    repo_root: Path | None = None,
    reconciliation_claim_map: RepoReconciliationClaimMap | None = None,
    arbiter_relation_register: RepoArbiterRelationRegister | None = None,
) -> RepoReconciliationDissentRegister:
    claim_map = reconciliation_claim_map or derive_v76a_repo_reconciliation_claim_map(
        repo_root=repo_root
    )
    relation_register = arbiter_relation_register or derive_v76a_repo_arbiter_relation_register(
        repo_root=repo_root,
        reconciliation_claim_map=claim_map,
    )
    payload = {
        "schema": REPO_RECONCILIATION_DISSENT_REGISTER_SCHEMA,
        "reconciliation_dissent_register_id": "",
        "reconciliation_claim_map_id": claim_map.reconciliation_claim_map_id,
        "arbiter_relation_register_id": relation_register.arbiter_relation_register_id,
        "review_id": claim_map.review_id,
        "snapshot_id": claim_map.snapshot_id,
        "source_set_id": claim_map.source_set_id,
        "dissent_rows": [
            {
                "dissent_ref": "dissent:v76a:product-wedge:authority-blocker",
                "claim_map_refs": [
                    "claim-map:v76a:product-wedge:projected-authority-blocker"
                ],
                "relation_refs": [
                    "arbiter-relation:v76a:product-wedge:blocked-placeholder"
                ],
                "dissent_kind": "product_authority_dissent",
                "dissent_presence_posture": "dissent_present",
                "dissent_search_horizon_refs": [],
                "dissent_search_coverage_posture": "partially_checked",
                "checked_source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus211/"
                    "repo_post_dispatch_review_handoff_v211_reference.json"
                ],
                "unchecked_source_refs": [],
                "dissent_source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus211/"
                    "repo_post_dispatch_review_handoff_v211_reference.json"
                ],
                "dissent_carry_forward_posture": "blocking_until_reviewed",
                "limitation_note": (
                    "Product authority blocker dissent is carried with no authority."
                ),
            },
            {
                "dissent_ref": "dissent:v76a:self-evidencing:searched-none",
                "claim_map_refs": [
                    "claim-map:v76a:self-evidencing:projected-relation-review"
                ],
                "relation_refs": [
                    "arbiter-relation:v76a:self-evidencing:single-projected"
                ],
                "dissent_kind": "no_dissent_recorded",
                "dissent_presence_posture": "searched_none_found",
                "dissent_search_horizon_refs": [
                    "horizon:v76a:self-evidencing:released-v75c-fixtures"
                ],
                "dissent_search_coverage_posture": "searched_released_v75c_sources",
                "checked_source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus211/"
                    "repo_worker_output_reconciliation_plan_v211_reference.json"
                ],
                "unchecked_source_refs": [],
                "dissent_source_refs": [],
                "dissent_carry_forward_posture": "warning_only",
                "limitation_note": "Searched released V75-C sources only; no truth authority.",
            },
        ],
        "dissent_register_summary": (
            "V76-A dissent register preserves searched and dissent states, not truth."
        ),
    }
    payload["reconciliation_dissent_register_id"] = _surface_id(
        "repo_reconciliation_dissent_register",
        REPO_RECONCILIATION_DISSENT_REGISTER_SCHEMA,
        payload,
        "reconciliation_dissent_register_id",
    )
    return RepoReconciliationDissentRegister.model_validate(payload)


def validate_v76a_reconciliation_arbiter_bundle(
    *,
    worker_output_reconciliation_plan: RepoWorkerOutputReconciliationPlan,
    dispatch_reconciliation_contract: RepoDispatchReconciliationContract,
    post_dispatch_review_handoff: RepoPostDispatchReviewHandoff,
    dispatch_review_family_closeout_alignment: RepoDispatchReviewFamilyCloseoutAlignment,
    reconciliation_claim_map: RepoReconciliationClaimMap,
    arbiter_relation_register: RepoArbiterRelationRegister,
    reconciliation_dissent_register: RepoReconciliationDissentRegister,
) -> None:
    v75c_surfaces = [
        worker_output_reconciliation_plan,
        dispatch_reconciliation_contract,
        post_dispatch_review_handoff,
        dispatch_review_family_closeout_alignment,
    ]
    for surface in v75c_surfaces:
        if (
            surface.review_id,
            surface.snapshot_id,
            surface.source_set_id,
        ) != (
            "review:v75c:reconciliation-contract-handoff-closeout",
            "vNext+210-closed-on-main",
            "source-set:v75c:released-v75a-v75b-dispatch-review",
        ):
            raise ValueError("V75-C prerequisite surfaces must share closeout provenance")
    if (
        dispatch_reconciliation_contract.worker_output_reconciliation_plan_id
        != worker_output_reconciliation_plan.worker_output_reconciliation_plan_id
    ):
        raise ValueError("V75-C contract must reference the reconciliation plan")
    if (
        post_dispatch_review_handoff.worker_output_reconciliation_plan_id
        != worker_output_reconciliation_plan.worker_output_reconciliation_plan_id
    ):
        raise ValueError("V75-C handoff must reference the reconciliation plan")
    if (
        post_dispatch_review_handoff.dispatch_reconciliation_contract_id
        != dispatch_reconciliation_contract.dispatch_reconciliation_contract_id
    ):
        raise ValueError("V75-C handoff must reference reconciliation contract")
    if dispatch_review_family_closeout_alignment.family != "V75":
        raise ValueError("V75-C family closeout alignment must be for V75")
    if dispatch_review_family_closeout_alignment.closed_by_arc != "vNext+211":
        raise ValueError("V75-C family closeout alignment must close vNext+211")

    surfaces = [
        reconciliation_claim_map,
        arbiter_relation_register,
        reconciliation_dissent_register,
    ]
    for surface in surfaces:
        if (
            surface.review_id,
            surface.snapshot_id,
            surface.source_set_id,
        ) != (
            "review:v76a:claim-relation-dissent-map",
            "vNext+211-closed-on-main",
            "source-set:v76a:released-v75c-reconciliation",
        ):
            raise ValueError("V76-A surfaces must share reconciliation starter provenance")
    if (
        reconciliation_claim_map.worker_output_reconciliation_plan_id
        != worker_output_reconciliation_plan.worker_output_reconciliation_plan_id
    ):
        raise ValueError("claim map must reference released V75-C reconciliation plan")
    if (
        reconciliation_claim_map.post_dispatch_review_handoff_id
        != post_dispatch_review_handoff.post_dispatch_review_handoff_id
    ):
        raise ValueError("claim map must reference released V75-C handoff")
    if (
        arbiter_relation_register.reconciliation_claim_map_id
        != reconciliation_claim_map.reconciliation_claim_map_id
    ):
        raise ValueError("arbiter relation register must reference claim map")
    if (
        reconciliation_dissent_register.reconciliation_claim_map_id
        != reconciliation_claim_map.reconciliation_claim_map_id
    ):
        raise ValueError("dissent register must reference claim map")
    if (
        reconciliation_dissent_register.arbiter_relation_register_id
        != arbiter_relation_register.arbiter_relation_register_id
    ):
        raise ValueError("dissent register must reference relation register")

    source_refs = {row.source_ref for row in reconciliation_claim_map.source_rows}
    plan_rows = {
        row.reconciliation_plan_ref: row
        for row in worker_output_reconciliation_plan.reconciliation_plan_rows
    }
    slot_refs = {
        row.projected_output_slot_ref
        for row in worker_output_reconciliation_plan.projected_output_slot_rows
    }
    v75_relation_refs = {
        row.relation_ref for row in worker_output_reconciliation_plan.relation_rows
    }
    handoff_refs = {row.handoff_ref for row in post_dispatch_review_handoff.handoff_rows}
    claim_map_rows = {row.claim_map_ref: row for row in reconciliation_claim_map.claim_map_rows}
    relation_rows = {
        row.arbiter_relation_ref: row for row in arbiter_relation_register.relation_rows
    }

    for claim_row in reconciliation_claim_map.claim_map_rows:
        if any(
            ref not in source_refs
            for ref in claim_row.source_refs + claim_row.claim_source_refs
        ):
            raise ValueError("claim map source refs must be known source rows")
        if any(ref not in plan_rows for ref in claim_row.reconciliation_plan_refs):
            raise ValueError("claim maps must reference released V75-C reconciliation plans")
        if any(ref not in slot_refs for ref in claim_row.projected_output_slot_refs):
            raise ValueError("claim maps must reference known V75-C projected output slots")
        if any(ref not in v75_relation_refs for ref in claim_row.v75_source_relation_refs):
            raise ValueError("claim maps must reference released V75-C relation rows")
        if any(ref not in handoff_refs for ref in claim_row.handoff_refs):
            raise ValueError("claim maps must reference released V75-C handoff rows")
        if any(ref.startswith("arbiter-relation:") for ref in claim_row.v75_source_relation_refs):
            raise ValueError("claim maps must not reference V76-A relation rows")
        if (
            claim_row.output_presence_posture == "projected_not_observed"
            and claim_row.claim_kind not in _PROJECTED_ONLY_CLAIM_KINDS
        ):
            raise ValueError("projected output slots cannot become observed content claims")

    for relation_row in arbiter_relation_register.relation_rows:
        if any(ref not in claim_map_rows for ref in relation_row.claim_map_refs):
            raise ValueError("arbiter relation rows must reference known claim maps")
        if any(ref not in v75_relation_refs for ref in relation_row.source_relation_refs):
            raise ValueError("arbiter relation rows must reference released V75-C relations")
        if any(ref not in source_refs for ref in relation_row.source_refs):
            raise ValueError("arbiter relation source refs must be known source rows")
        for claim_ref in relation_row.claim_map_refs:
            claim_row = claim_map_rows[claim_ref]
            if (
                claim_row.output_presence_posture == "projected_not_observed"
                and relation_row.relation_review_posture == "visible_unsettled"
            ):
                raise ValueError("projected outputs cannot imply observed-output conflict")
        if (
            relation_row.arbiter_need_posture == "arbiter_review_needed_later"
            and relation_row.required_next_review_surface
            not in {"future_reconciliation_or_arbiter_review", "future_family_review"}
        ):
            raise ValueError("arbiter review need must route to arbiter or future-family review")

    for dissent_row in reconciliation_dissent_register.dissent_rows:
        if any(ref not in claim_map_rows for ref in dissent_row.claim_map_refs):
            raise ValueError("dissent rows must reference known claim maps")
        if any(ref not in relation_rows for ref in dissent_row.relation_refs):
            raise ValueError("dissent rows must reference known arbiter relation rows")


def derive_v76a_reconciliation_arbiter_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoReconciliationClaimMap,
    RepoArbiterRelationRegister,
    RepoReconciliationDissentRegister,
]:
    reconciliation_plan, contract, handoff, closeout = derive_v75c_dispatch_review_closeout_bundle(
        repo_root=repo_root
    )
    claim_map = derive_v76a_repo_reconciliation_claim_map(
        repo_root=repo_root,
        worker_output_reconciliation_plan=reconciliation_plan,
        post_dispatch_review_handoff=handoff,
    )
    relation_register = derive_v76a_repo_arbiter_relation_register(
        repo_root=repo_root,
        reconciliation_claim_map=claim_map,
    )
    dissent_register = derive_v76a_repo_reconciliation_dissent_register(
        repo_root=repo_root,
        reconciliation_claim_map=claim_map,
        arbiter_relation_register=relation_register,
    )
    validate_v76a_reconciliation_arbiter_bundle(
        worker_output_reconciliation_plan=reconciliation_plan,
        dispatch_reconciliation_contract=contract,
        post_dispatch_review_handoff=handoff,
        dispatch_review_family_closeout_alignment=closeout,
        reconciliation_claim_map=claim_map,
        arbiter_relation_register=relation_register,
        reconciliation_dissent_register=dissent_register,
    )
    return claim_map, relation_register, dissent_register


def _resolve_v76a_reconciliation_surfaces(
    *,
    repo_root: Path | None = None,
    reconciliation_claim_map: RepoReconciliationClaimMap | None = None,
    arbiter_relation_register: RepoArbiterRelationRegister | None = None,
    reconciliation_dissent_register: RepoReconciliationDissentRegister | None = None,
) -> tuple[
    RepoReconciliationClaimMap,
    RepoArbiterRelationRegister,
    RepoReconciliationDissentRegister,
]:
    if reconciliation_claim_map is None:
        if arbiter_relation_register is not None or reconciliation_dissent_register is not None:
            raise ValueError("partial V76-A dependencies must include the claim map")
        return derive_v76a_reconciliation_arbiter_bundle(repo_root=repo_root)

    claim_map = reconciliation_claim_map
    relation_register = (
        arbiter_relation_register
        or derive_v76a_repo_arbiter_relation_register(
            repo_root=repo_root,
            reconciliation_claim_map=claim_map,
        )
    )
    dissent_register = (
        reconciliation_dissent_register
        or derive_v76a_repo_reconciliation_dissent_register(
            repo_root=repo_root,
            reconciliation_claim_map=claim_map,
            arbiter_relation_register=relation_register,
        )
    )
    if relation_register.reconciliation_claim_map_id != claim_map.reconciliation_claim_map_id:
        raise ValueError("partial V76-A relation register must reference the supplied claim map")
    if dissent_register.reconciliation_claim_map_id != claim_map.reconciliation_claim_map_id:
        raise ValueError("partial V76-A dissent register must reference the supplied claim map")
    if (
        dissent_register.arbiter_relation_register_id
        != relation_register.arbiter_relation_register_id
    ):
        raise ValueError(
            "partial V76-A dissent register must reference the supplied relation register"
        )
    return claim_map, relation_register, dissent_register


def derive_v76b_repo_arbiter_authority_profile(
    *,
    repo_root: Path | None = None,
    reconciliation_claim_map: RepoReconciliationClaimMap | None = None,
    arbiter_relation_register: RepoArbiterRelationRegister | None = None,
    reconciliation_dissent_register: RepoReconciliationDissentRegister | None = None,
) -> RepoArbiterAuthorityProfile:
    claim_map, relation_register, dissent_register = _resolve_v76a_reconciliation_surfaces(
        repo_root=repo_root,
        reconciliation_claim_map=reconciliation_claim_map,
        arbiter_relation_register=arbiter_relation_register,
        reconciliation_dissent_register=reconciliation_dissent_register,
    )
    payload = {
        **_v76b_base_payload(
            schema=REPO_ARBITER_AUTHORITY_PROFILE_SCHEMA,
            reconciliation_claim_map=claim_map,
            arbiter_relation_register=relation_register,
            reconciliation_dissent_register=dissent_register,
        ),
        "arbiter_authority_profile_id": "",
        "authority_profile_rows": [
            {
                "authority_profile_ref": "authority-profile:v76b:self-evidencing:review-only",
                "authority_actor_kind": "maintainer",
                "authority_grant_source_kind": "repo_lock",
                "authority_source_refs": ["docs/LOCKED_CONTINUATION_vNEXT_PLUS213.md"],
                "allowed_relation_horizons": [
                    "relation-horizon:v76b:self-evidencing:projected-relation-review"
                ],
                "allowed_review_actions": [
                    "inspect_relation",
                    "preserve_dissent",
                    "request_adversarial_review",
                    "request_later_settlement_review",
                ],
                "forbidden_authority_kinds": [
                    "authorize_product_now",
                    "authorize_release_now",
                    "authorize_runtime_now",
                    "declare_truth_now",
                    "ratify_claim_now",
                    "settle_relation_now",
                ],
                "authority_gap_posture": "review_only_authority",
                "limitation_note": (
                    "Lock-bound maintainer profile may request later review; it is not truth "
                    "authority and not settlement authority."
                ),
            },
            {
                "authority_profile_ref": "authority-profile:v76b:product-wedge:authority-gap",
                "authority_actor_kind": "support_doc_context",
                "authority_grant_source_kind": "support_doc",
                "authority_source_refs": [
                    "docs/DRAFT_ADEU_RECONCILIATION_ARBITER_V76B_IMPLEMENTATION_MAPPING_v0.md"
                ],
                "allowed_relation_horizons": [
                    "relation-horizon:v76b:product-wedge:authority-blocker"
                ],
                "allowed_review_actions": [
                    "classify_gap",
                    "inspect_relation",
                    "request_future_family_review",
                ],
                "forbidden_authority_kinds": [
                    "authorize_product_now",
                    "declare_truth_now",
                    "ratify_claim_now",
                    "settle_relation_now",
                ],
                "authority_gap_posture": "blocked_pending_later_authority",
                "limitation_note": (
                    "Support context preserves product authority gap; it is not truth "
                    "authority and not settlement authority."
                ),
            },
        ],
        "authority_profile_summary": (
            "V76-B authority profiles are review posture only, not truth and not settlement."
        ),
    }
    payload["authority_profile_rows"] = sorted(
        payload["authority_profile_rows"],
        key=lambda row: row["authority_profile_ref"],
    )
    payload["arbiter_authority_profile_id"] = _surface_id(
        "repo_arbiter_authority_profile",
        REPO_ARBITER_AUTHORITY_PROFILE_SCHEMA,
        payload,
        "arbiter_authority_profile_id",
    )
    return RepoArbiterAuthorityProfile.model_validate(payload)


def derive_v76b_repo_adversarial_relation_review(
    *,
    repo_root: Path | None = None,
    reconciliation_claim_map: RepoReconciliationClaimMap | None = None,
    arbiter_relation_register: RepoArbiterRelationRegister | None = None,
) -> RepoAdversarialRelationReview:
    claim_map, relation_register, _ = _resolve_v76a_reconciliation_surfaces(
        repo_root=repo_root,
        reconciliation_claim_map=reconciliation_claim_map,
        arbiter_relation_register=arbiter_relation_register,
    )
    payload = {
        "schema": REPO_ADVERSARIAL_RELATION_REVIEW_SCHEMA,
        "adversarial_relation_review_id": "",
        "reconciliation_claim_map_id": claim_map.reconciliation_claim_map_id,
        "arbiter_relation_register_id": relation_register.arbiter_relation_register_id,
        "review_id": "review:v76b:arbiter-authority-settlement-gap",
        "snapshot_id": "vNext+212-closed-on-main",
        "source_set_id": "source-set:v76b:released-v76a-reconciliation-arbiter",
        "adversarial_review_rows": [
            {
                "adversarial_review_ref": (
                    "adversarial-review:v76b:self-evidencing:checked-projected-slot"
                ),
                "claim_map_refs": [
                    "claim-map:v76a:self-evidencing:projected-relation-review"
                ],
                "relation_refs": [
                    "arbiter-relation:v76a:self-evidencing:single-projected"
                ],
                "review_perspective": "check whether projected relation review implies truth",
                "counterclaim_horizon": (
                    "checked released V76-A projected single-output relation horizon"
                ),
                "negative_control_refs": [
                    "negative-control:v76b:self-evidencing:no-observed-output-content"
                ],
                "review_result_posture": "no_counterevidence_in_checked_horizon",
                "source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus212/"
                    "repo_arbiter_relation_register_v212_reference.json",
                    "apps/api/fixtures/repo_description/vnext_plus212/"
                    "repo_reconciliation_claim_map_v212_reference.json",
                ],
                "limitation_note": (
                    "Checked projected-only horizon; result is not truth and not settlement."
                ),
            },
            {
                "adversarial_review_ref": "adversarial-review:v76b:product-wedge:blocked",
                "claim_map_refs": [
                    "claim-map:v76a:product-wedge:projected-authority-blocker"
                ],
                "relation_refs": [
                    "arbiter-relation:v76a:product-wedge:blocked-placeholder"
                ],
                "review_perspective": "product authority blocker remains outside arbiter scope",
                "counterclaim_horizon": "product authority gap checked as future-family pressure",
                "negative_control_refs": [],
                "review_result_posture": "blocked_by_missing_source",
                "source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus212/"
                    "repo_reconciliation_claim_map_v212_reference.json",
                    "apps/api/fixtures/repo_description/vnext_plus212/"
                    "repo_reconciliation_dissent_register_v212_reference.json",
                ],
                "limitation_note": (
                    "Product authority blocker is not truth, not settlement, and not product "
                    "authorization."
                ),
            },
        ],
        "adversarial_review_summary": (
            "V76-B adversarial relation review is adversarial checking, not truth and "
            "not settlement."
        ),
    }
    payload["adversarial_review_rows"] = sorted(
        payload["adversarial_review_rows"],
        key=lambda row: row["adversarial_review_ref"],
    )
    payload["adversarial_relation_review_id"] = _surface_id(
        "repo_adversarial_relation_review",
        REPO_ADVERSARIAL_RELATION_REVIEW_SCHEMA,
        payload,
        "adversarial_relation_review_id",
    )
    return RepoAdversarialRelationReview.model_validate(payload)


def derive_v76b_repo_reconciliation_gap_scan(
    *,
    repo_root: Path | None = None,
    reconciliation_claim_map: RepoReconciliationClaimMap | None = None,
    arbiter_relation_register: RepoArbiterRelationRegister | None = None,
) -> RepoReconciliationGapScan:
    claim_map, relation_register, _ = _resolve_v76a_reconciliation_surfaces(
        repo_root=repo_root,
        reconciliation_claim_map=reconciliation_claim_map,
        arbiter_relation_register=arbiter_relation_register,
    )
    payload = {
        "schema": REPO_RECONCILIATION_GAP_SCAN_SCHEMA,
        "reconciliation_gap_scan_id": "",
        "reconciliation_claim_map_id": claim_map.reconciliation_claim_map_id,
        "arbiter_relation_register_id": relation_register.arbiter_relation_register_id,
        "review_id": "review:v76b:arbiter-authority-settlement-gap",
        "snapshot_id": "vNext+212-closed-on-main",
        "source_set_id": "source-set:v76b:released-v76a-reconciliation-arbiter",
        "gap_rows": [
            {
                "gap_ref": "gap:v76b:product-wedge:product-authority",
                "claim_map_refs": [
                    "claim-map:v76a:product-wedge:projected-authority-blocker"
                ],
                "relation_refs": [
                    "arbiter-relation:v76a:product-wedge:blocked-placeholder"
                ],
                "gap_kind": "product_authority_gap",
                "gap_severity": "blocking",
                "blocking_posture": "blocking_until_reviewed",
                "required_next_surface": "future_product_review",
                "source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus212/"
                    "repo_reconciliation_claim_map_v212_reference.json"
                ],
                "limitation_note": (
                    "Product authority gap remains a blocker and is not authority, not truth."
                ),
            },
            {
                "gap_ref": "gap:v76b:self-evidencing:projected-not-observed",
                "claim_map_refs": [
                    "claim-map:v76a:self-evidencing:projected-relation-review"
                ],
                "relation_refs": [
                    "arbiter-relation:v76a:self-evidencing:single-projected"
                ],
                "gap_kind": "projected_slot_not_observed_for_content_claim",
                "gap_severity": "warning",
                "blocking_posture": "warning_only",
                "required_next_surface": "future_reconciliation_or_arbiter_review",
                "source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus212/"
                    "repo_reconciliation_claim_map_v212_reference.json"
                ],
                "limitation_note": (
                    "Projected slot is not observed content; gap is not authority and not truth."
                ),
            },
        ],
        "gap_scan_summary": (
            "V76-B gap scan preserves gap posture, not authority and not truth."
        ),
    }
    payload["gap_rows"] = sorted(payload["gap_rows"], key=lambda row: row["gap_ref"])
    payload["reconciliation_gap_scan_id"] = _surface_id(
        "repo_reconciliation_gap_scan",
        REPO_RECONCILIATION_GAP_SCAN_SCHEMA,
        payload,
        "reconciliation_gap_scan_id",
    )
    return RepoReconciliationGapScan.model_validate(payload)


def derive_v76b_repo_reconciliation_settlement_request(
    *,
    repo_root: Path | None = None,
    reconciliation_claim_map: RepoReconciliationClaimMap | None = None,
    arbiter_relation_register: RepoArbiterRelationRegister | None = None,
    reconciliation_dissent_register: RepoReconciliationDissentRegister | None = None,
    arbiter_authority_profile: RepoArbiterAuthorityProfile | None = None,
    adversarial_relation_review: RepoAdversarialRelationReview | None = None,
    reconciliation_gap_scan: RepoReconciliationGapScan | None = None,
) -> RepoReconciliationSettlementRequest:
    claim_map, relation_register, dissent_register = _resolve_v76a_reconciliation_surfaces(
        repo_root=repo_root,
        reconciliation_claim_map=reconciliation_claim_map,
        arbiter_relation_register=arbiter_relation_register,
        reconciliation_dissent_register=reconciliation_dissent_register,
    )
    authority_profile = arbiter_authority_profile or derive_v76b_repo_arbiter_authority_profile(
        repo_root=repo_root,
        reconciliation_claim_map=claim_map,
        arbiter_relation_register=relation_register,
        reconciliation_dissent_register=dissent_register,
    )
    adversarial_review = (
        adversarial_relation_review
        or derive_v76b_repo_adversarial_relation_review(
            repo_root=repo_root,
            reconciliation_claim_map=claim_map,
            arbiter_relation_register=relation_register,
        )
    )
    gap_scan = reconciliation_gap_scan or derive_v76b_repo_reconciliation_gap_scan(
        repo_root=repo_root,
        reconciliation_claim_map=claim_map,
        arbiter_relation_register=relation_register,
    )
    payload = {
        **_v76b_base_payload(
            schema=REPO_RECONCILIATION_SETTLEMENT_REQUEST_SCHEMA,
            reconciliation_claim_map=claim_map,
            arbiter_relation_register=relation_register,
            reconciliation_dissent_register=dissent_register,
        ),
        "reconciliation_settlement_request_id": "",
        "arbiter_authority_profile_id": authority_profile.arbiter_authority_profile_id,
        "settlement_request_rows": [
            {
                "settlement_request_ref": "settlement-request:v76b:self-evidencing:later-review",
                "claim_map_refs": [
                    "claim-map:v76a:self-evidencing:projected-relation-review"
                ],
                "relation_refs": [
                    "arbiter-relation:v76a:self-evidencing:single-projected"
                ],
                "dissent_refs": ["dissent:v76a:self-evidencing:searched-none"],
                "authority_profile_refs": [
                    "authority-profile:v76b:self-evidencing:review-only"
                ],
                "requested_settlement_horizon": (
                    "relation-horizon:v76b:self-evidencing:projected-relation-review"
                ),
                "settlement_request_posture": "request_ready_for_later_review",
                "required_adversarial_review_refs": [
                    "adversarial-review:v76b:self-evidencing:checked-projected-slot"
                ],
                "carried_gap_refs": [
                    "gap:v76b:self-evidencing:projected-not-observed"
                ],
                "non_settlement_guardrail": (
                    "This request is for later review, not settlement and not truth."
                ),
                "limitation_note": (
                    "Ready only as a bounded later-review request; no settlement complete."
                ),
            },
            {
                "settlement_request_ref": "settlement-request:v76b:product-wedge:blocked",
                "claim_map_refs": [
                    "claim-map:v76a:product-wedge:projected-authority-blocker"
                ],
                "relation_refs": [
                    "arbiter-relation:v76a:product-wedge:blocked-placeholder"
                ],
                "dissent_refs": ["dissent:v76a:product-wedge:authority-blocker"],
                "authority_profile_refs": [
                    "authority-profile:v76b:product-wedge:authority-gap"
                ],
                "requested_settlement_horizon": (
                    "relation-horizon:v76b:product-wedge:authority-blocker"
                ),
                "settlement_request_posture": "blocked_by_authority_gap",
                "required_adversarial_review_refs": [
                    "adversarial-review:v76b:product-wedge:blocked"
                ],
                "carried_gap_refs": ["gap:v76b:product-wedge:product-authority"],
                "non_settlement_guardrail": (
                    "This request is for later review, not settlement and not truth."
                ),
                "limitation_note": (
                    "Product authority gap blocks settlement readiness and no product is "
                    "authorized."
                ),
            },
        ],
        "settlement_request_summary": (
            "V76-B settlement rows are requests for later review, not settlement and "
            "not truth."
        ),
    }
    payload["settlement_request_rows"] = sorted(
        payload["settlement_request_rows"],
        key=lambda row: row["settlement_request_ref"],
    )
    # Keep local variables live so callers can inject stale dependencies and
    # bundle validation still sees the same objects the request was derived from.
    _ = adversarial_review, gap_scan
    payload["reconciliation_settlement_request_id"] = _surface_id(
        "repo_reconciliation_settlement_request",
        REPO_RECONCILIATION_SETTLEMENT_REQUEST_SCHEMA,
        payload,
        "reconciliation_settlement_request_id",
    )
    return RepoReconciliationSettlementRequest.model_validate(payload)


def validate_v76b_reconciliation_arbiter_bundle(
    *,
    reconciliation_claim_map: RepoReconciliationClaimMap,
    arbiter_relation_register: RepoArbiterRelationRegister,
    reconciliation_dissent_register: RepoReconciliationDissentRegister,
    arbiter_authority_profile: RepoArbiterAuthorityProfile,
    reconciliation_settlement_request: RepoReconciliationSettlementRequest,
    adversarial_relation_review: RepoAdversarialRelationReview,
    reconciliation_gap_scan: RepoReconciliationGapScan,
) -> None:
    v76a_surfaces = [
        reconciliation_claim_map,
        arbiter_relation_register,
        reconciliation_dissent_register,
    ]
    for surface in v76a_surfaces:
        if (
            surface.review_id,
            surface.snapshot_id,
            surface.source_set_id,
        ) != (
            "review:v76a:claim-relation-dissent-map",
            "vNext+211-closed-on-main",
            "source-set:v76a:released-v75c-reconciliation",
        ):
            raise ValueError("V76-A prerequisite surfaces must share starter provenance")
    if (
        arbiter_relation_register.reconciliation_claim_map_id
        != reconciliation_claim_map.reconciliation_claim_map_id
    ):
        raise ValueError("V76-A relation register must reference claim map")
    if (
        reconciliation_dissent_register.reconciliation_claim_map_id
        != reconciliation_claim_map.reconciliation_claim_map_id
    ):
        raise ValueError("V76-A dissent register must reference claim map")
    if (
        reconciliation_dissent_register.arbiter_relation_register_id
        != arbiter_relation_register.arbiter_relation_register_id
    ):
        raise ValueError("V76-A dissent register must reference relation register")

    v76b_surfaces = [
        arbiter_authority_profile,
        reconciliation_settlement_request,
        adversarial_relation_review,
        reconciliation_gap_scan,
    ]
    for surface in v76b_surfaces:
        if (
            surface.review_id,
            surface.snapshot_id,
            surface.source_set_id,
        ) != (
            "review:v76b:arbiter-authority-settlement-gap",
            "vNext+212-closed-on-main",
            "source-set:v76b:released-v76a-reconciliation-arbiter",
        ):
            raise ValueError("V76-B surfaces must share arbiter starter provenance")
        if (
            surface.reconciliation_claim_map_id
            != reconciliation_claim_map.reconciliation_claim_map_id
        ):
            raise ValueError("V76-B surfaces must reference released V76-A claim map")
        if (
            surface.arbiter_relation_register_id
            != arbiter_relation_register.arbiter_relation_register_id
        ):
            raise ValueError("V76-B surfaces must reference released V76-A relation register")
    for surface in (arbiter_authority_profile, reconciliation_settlement_request):
        if (
            surface.reconciliation_dissent_register_id
            != reconciliation_dissent_register.reconciliation_dissent_register_id
        ):
            raise ValueError("V76-B authority/request surfaces must reference dissent register")
    if (
        reconciliation_settlement_request.arbiter_authority_profile_id
        != arbiter_authority_profile.arbiter_authority_profile_id
    ):
        raise ValueError("settlement request must reference authority profile")

    claim_rows = {row.claim_map_ref: row for row in reconciliation_claim_map.claim_map_rows}
    relation_rows = {
        row.arbiter_relation_ref: row for row in arbiter_relation_register.relation_rows
    }
    dissent_rows = {
        row.dissent_ref: row for row in reconciliation_dissent_register.dissent_rows
    }
    authority_rows = {
        row.authority_profile_ref: row
        for row in arbiter_authority_profile.authority_profile_rows
    }
    adversarial_rows = {
        row.adversarial_review_ref: row
        for row in adversarial_relation_review.adversarial_review_rows
    }
    gap_rows = {row.gap_ref: row for row in reconciliation_gap_scan.gap_rows}

    for review_row in adversarial_relation_review.adversarial_review_rows:
        if any(ref not in claim_rows for ref in review_row.claim_map_refs):
            raise ValueError("adversarial review rows must reference known claim maps")
        if any(ref not in relation_rows for ref in review_row.relation_refs):
            raise ValueError("adversarial review rows must reference known relation rows")
        if (
            review_row.review_result_posture == "no_counterevidence_in_checked_horizon"
            and not review_row.counterclaim_horizon
            and not review_row.negative_control_refs
        ):
            raise ValueError("no-counterevidence review requires checked horizon or controls")

    for gap_row in reconciliation_gap_scan.gap_rows:
        if any(ref not in claim_rows for ref in gap_row.claim_map_refs):
            raise ValueError("gap rows must reference known claim maps")
        if any(ref not in relation_rows for ref in gap_row.relation_refs):
            raise ValueError("gap rows must reference known relation rows")

    for request_row in reconciliation_settlement_request.settlement_request_rows:
        if any(ref not in claim_rows for ref in request_row.claim_map_refs):
            raise ValueError("settlement requests must reference known claim maps")
        if any(ref not in relation_rows for ref in request_row.relation_refs):
            raise ValueError("settlement requests must reference known relation rows")
        if any(ref not in dissent_rows for ref in request_row.dissent_refs):
            raise ValueError("settlement requests must reference known dissent rows")
        if any(ref not in authority_rows for ref in request_row.authority_profile_refs):
            raise ValueError("settlement requests must reference known authority profiles")
        if any(ref not in adversarial_rows for ref in request_row.required_adversarial_review_refs):
            raise ValueError("settlement requests must reference known adversarial reviews")
        if any(ref not in gap_rows for ref in request_row.carried_gap_refs):
            raise ValueError("settlement requests must reference known gap rows")
        for authority_ref in request_row.authority_profile_refs:
            allowed = authority_rows[authority_ref].allowed_relation_horizons
            if request_row.requested_settlement_horizon not in allowed:
                raise ValueError("settlement horizon must be allowed by authority profile")
        if request_row.settlement_request_posture == "request_ready_for_later_review":
            for dissent_ref in request_row.dissent_refs:
                if dissent_rows[dissent_ref].dissent_carry_forward_posture == (
                    "blocking_until_reviewed"
                ):
                    raise ValueError("settlement request cannot ignore blocking dissent")
            if any(
                gap_rows[gap_ref].gap_kind
                in {
                    "product_authority_gap",
                    "runtime_authority_gap",
                    "external_branch_gap",
                    "benchmark_truth_guardrail_missing",
                }
                for gap_ref in request_row.carried_gap_refs
            ):
                raise ValueError("downstream authority gaps cannot become settlement readiness")
        for relation_ref in request_row.relation_refs:
            relation = relation_rows[relation_ref]
            if relation.relation_kind in {"conflict", "unclear_relation"} and not (
                request_row.required_adversarial_review_refs or request_row.carried_gap_refs
            ):
                raise ValueError("conflict readiness requires adversarial review or gap")


def derive_v76b_reconciliation_arbiter_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoArbiterAuthorityProfile,
    RepoReconciliationSettlementRequest,
    RepoAdversarialRelationReview,
    RepoReconciliationGapScan,
]:
    claim_map, relation_register, dissent_register = derive_v76a_reconciliation_arbiter_bundle(
        repo_root=repo_root
    )
    authority_profile = derive_v76b_repo_arbiter_authority_profile(
        repo_root=repo_root,
        reconciliation_claim_map=claim_map,
        arbiter_relation_register=relation_register,
        reconciliation_dissent_register=dissent_register,
    )
    adversarial_review = derive_v76b_repo_adversarial_relation_review(
        repo_root=repo_root,
        reconciliation_claim_map=claim_map,
        arbiter_relation_register=relation_register,
    )
    gap_scan = derive_v76b_repo_reconciliation_gap_scan(
        repo_root=repo_root,
        reconciliation_claim_map=claim_map,
        arbiter_relation_register=relation_register,
    )
    settlement_request = derive_v76b_repo_reconciliation_settlement_request(
        repo_root=repo_root,
        reconciliation_claim_map=claim_map,
        arbiter_relation_register=relation_register,
        reconciliation_dissent_register=dissent_register,
        arbiter_authority_profile=authority_profile,
        adversarial_relation_review=adversarial_review,
        reconciliation_gap_scan=gap_scan,
    )
    validate_v76b_reconciliation_arbiter_bundle(
        reconciliation_claim_map=claim_map,
        arbiter_relation_register=relation_register,
        reconciliation_dissent_register=dissent_register,
        arbiter_authority_profile=authority_profile,
        reconciliation_settlement_request=settlement_request,
        adversarial_relation_review=adversarial_review,
        reconciliation_gap_scan=gap_scan,
    )
    return authority_profile, settlement_request, adversarial_review, gap_scan
