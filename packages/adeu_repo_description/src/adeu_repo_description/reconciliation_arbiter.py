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

_PROJECTED_ONLY_CLAIM_KINDS = {
    "projected_output_slot_existence",
    "projected_relation_review_need",
    "relation_placeholder_claim",
}


def _reject_reconciliation_overclaim(value: str, *, field_name: str) -> str:
    _reject_unnegated_authority_claim(value, field_name=field_name)
    lowered = value.lower()
    forbidden = [
        "settles truth",
        "settled truth",
        "declares truth",
        "majority agreement proves",
        "majority-as-correctness",
        "benchmark truth",
        "model selected",
        "is correct",
    ]
    negation_markers = ("no ", "not ", "without ", "forbidden ", "non-")
    for phrase in forbidden:
        index = lowered.find(phrase)
        if index == -1:
            continue
        prefix = lowered[max(0, index - 18) : index]
        if not any(marker in prefix for marker in negation_markers):
            raise ValueError(f"{field_name} may not carry truth or correctness authority")
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
