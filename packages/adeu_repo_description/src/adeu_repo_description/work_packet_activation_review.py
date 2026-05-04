from __future__ import annotations

import re
from pathlib import Path
from typing import Any, Literal

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
    CandidateSourceKind,
    CandidateSourcePresencePosture,
    OdeuLane,
)
from .semantic_implementation_spec import (
    RepoArtifactObligationMap,
    RepoImplementationSpecProjectionPacket,
    RepoIntentEdgeDecomposition,
    RepoIntentNonImplementationGuardrail,
    RepoIntentSourceIndex,
    RepoIntentToWorkPacketHandoff,
    RepoSemanticDriftAmbiguityRegister,
    RepoSemanticImplementationSpecFamilyCloseoutAlignment,
    RepoSemanticIntentContract,
    derive_v83c_semantic_implementation_projection_bundle,
    validate_v83c_semantic_implementation_projection_bundle,
)

REPO_WORK_PACKET_ACTIVATION_SOURCE_INDEX_SCHEMA = (
    "repo_work_packet_activation_source_index@1"
)
REPO_WORK_PACKET_ACTIVATION_REVIEW_REQUEST_SCHEMA = (
    "repo_work_packet_activation_review_request@1"
)
REPO_WORK_PACKET_ACTIVATION_NON_EXECUTION_GUARDRAIL_SCHEMA = (
    "repo_work_packet_activation_non_execution_guardrail@1"
)

ActivationSourceRole = Literal[
    "v83_projection_packet_source",
    "v83_quality_gate_source",
    "v83_handoff_source",
    "v83_closeout_source",
    "v83_semantic_edge_context",
    "v83_artifact_obligation_context",
    "generated_work_packet_candidate_review_source",
    "canonical_lock_requirement_source",
    "target_boundary_context_source",
    "read_dependency_context_source",
    "prospective_write_target_context_source",
    "forbidden_target_context_source",
    "morphic_ux_support_context",
    "direct_oai_support_context",
    "meta_orchestrator_support_context",
    "combined_dogfood_context",
    "support_process_context",
    "absence_marker",
]
ActivationSourceCurrentness = Literal[
    "current_released_source",
    "context_only",
    "explicit_absence_marker",
    "stale_or_superseded",
    "unknown_needs_review",
]
ProjectionAuthorityPosture = Literal[
    "projection_source_for_review_only",
    "quality_gate_source_for_review_only",
    "generated_candidate_source_only",
    "support_context_only",
    "projection_missing",
    "projection_blocked_by_carried_drift",
    "not_applicable",
]
WorkPacketAuthorityPosture = Literal[
    "work_packet_requires_later_lock",
    "work_packet_review_only",
    "no_work_packet_authority_granted",
    "work_packet_forbidden_by_this_family",
]
GenerationScopePosture = Literal[
    "not_generated",
    "generated_for_review_only",
    "generated_from_bounded_context",
    "generated_from_unbounded_context",
    "generated_source_missing",
    "generated_source_unknown",
]
GeneratingActorKind = Literal[
    "human_operator",
    "model",
    "agent",
    "reviewer",
    "tool_assisted_review",
    "mixed",
    "unknown",
]
GeneratedCandidateAuthorityPosture = Literal[
    "candidate_only",
    "candidate_blocked_by_missing_v83_projection",
    "candidate_blocked_by_missing_quality_gate",
    "candidate_blocked_by_unbounded_target",
    "candidate_blocked_by_missing_review",
]
ActivationRequestRecordabilityPosture = Literal[
    "recordable_from_released_v83_projection",
    "recordable_from_released_v83_handoff",
    "recordable_from_generated_work_packet_candidate",
    "recordable_from_operator_request_with_absence_markers",
    "recordable_from_support_context_only",
    "not_recordable_missing_projection_source",
]
ActivationReviewEligibilityPosture = Literal[
    "eligible_for_work_packet_activation_review",
    "request_recorded_for_review_only",
    "blocked_by_missing_projection_packet",
    "blocked_by_missing_quality_gate",
    "blocked_by_carried_semantic_drift",
    "blocked_by_generated_candidate_provenance_gap",
    "blocked_by_unbounded_target_surface",
    "blocked_by_missing_validation_evidence",
    "blocked_by_missing_canonical_lock_requirement",
    "blocked_by_authority_gap",
    "future_family_only",
    "rejected_out_of_scope",
]
RequestedWorkPacketHorizon = Literal[
    "repo_description_implementation_slice_review",
    "morphic_ux_projection_implementation_review",
    "direct_oai_harness_implementation_review",
    "meta_orchestrator_workflow_activation_review",
    "product_implementation_review",
    "graph_memory_implementation_review",
    "future_family_only",
]
RequestedActivationReviewHorizon = Literal[
    "implementation_lock_review_package",
    "morphic_ux_runtime_ui_authority_review_package",
    "direct_oai_provider_runtime_authority_review_package",
    "meta_orchestrator_workflow_runtime_authority_review_package",
    "future_family_only",
]
TargetSurfacePosture = Literal[
    "bounded_for_later_review",
    "warning_future_family_boundary",
    "blocked_by_unbounded_target_surface",
    "future_family_only",
]
ValidationEvidencePosture = Literal[
    "edge_bound_for_later_review",
    "tests_listed_not_sufficient",
    "blocked_by_missing_validation_evidence",
    "future_family_only",
]
CanonicalLockRequirement = Literal[
    "canonical_implementation_lock_required",
    "morphic_ux_runtime_authority_review_required",
    "direct_oai_runtime_authority_review_required",
    "meta_orchestrator_runtime_authority_review_required",
    "future_family_only",
]
ActivationAuthorityPosture = Literal[
    "no_activation_authority_granted_by_v84",
    "activation_requires_later_canonical_lock",
    "activation_forbidden_by_this_family",
]
ImplementationLockStatus = Literal[
    "no_implementation_lock_created_by_v84",
    "later_implementation_lock_review_requested",
    "later_selector_required",
    "deferred_no_selection",
]
TargetFamilyBoundaryPosture = Literal[
    "repo_description_implementation_allowed_for_later_lock_review",
    "morphic_ux_requires_runtime_ui_authority_review",
    "direct_oai_requires_provider_runtime_authority_review",
    "meta_orchestrator_requires_workflow_runtime_authority_review",
    "product_requires_product_authority_review",
    "graph_requires_graph_memory_authority_review",
    "future_family_only",
]
ActivationExecutionPosture = Literal[
    "no_activation_performed_by_v84",
    "activation_requires_later_canonical_lock",
    "activation_forbidden_by_this_family",
]
WorkPacketExecutionPosture = Literal[
    "no_work_packet_execution_performed_by_v84",
    "work_packet_execution_requires_later_lock",
    "work_packet_execution_forbidden_by_this_family",
]
ImplementationExecutionPosture = Literal[
    "no_implementation_performed_by_v84",
    "implementation_requires_later_lock",
    "implementation_forbidden_by_this_family",
]
TargetMutationPosture = Literal[
    "no_target_mutation_performed_by_v84",
    "target_mutation_requires_later_lock",
    "target_mutation_forbidden_by_this_family",
]
PullRequestPosture = Literal[
    "no_pr_created_by_v84",
    "pr_requires_later_lock",
    "pr_forbidden_by_this_family",
]
ForbiddenImplementationAction = Literal[
    "activate_work_packet",
    "create_scope_contract",
    "create_target_boundary",
    "create_validation_plan",
    "edit_code",
    "execute_work_packet",
    "open_pr",
    "commit_change",
    "merge_change",
    "release_change",
    "write_implementation",
]
ForbiddenRuntimeAction = Literal[
    "activate_direct_oai_runtime",
    "change_morphic_ux_runtime",
    "dispatch_worker",
    "invoke_tool_for_effect",
    "mutate_meta_orchestrator_runtime",
    "mutate_target_state",
    "run_command",
]
ForbiddenDownstreamAuthority = Literal[
    "activation_authority",
    "graph_memory_authority",
    "implementation_authority",
    "product_authorization",
    "recursive_policy_amendment",
    "release_authority",
    "runtime_authority",
    "v85_selection",
    "work_packet_execution_authority",
]

_ELIGIBLE_SOURCE_ROLES = {
    "v83_projection_packet_source",
    "v83_handoff_source",
}
_SUPPORT_ONLY_SOURCE_ROLES = {
    "combined_dogfood_context",
    "direct_oai_support_context",
    "meta_orchestrator_support_context",
    "morphic_ux_support_context",
    "support_process_context",
}
_REQUIRED_FORBIDDEN_IMPLEMENTATION_ACTIONS = {
    "activate_work_packet",
    "edit_code",
    "execute_work_packet",
    "open_pr",
    "commit_change",
    "merge_change",
    "release_change",
    "write_implementation",
}
_REQUIRED_FORBIDDEN_RUNTIME_ACTIONS = {
    "dispatch_worker",
    "invoke_tool_for_effect",
    "mutate_target_state",
    "run_command",
}
_REQUIRED_FORBIDDEN_DOWNSTREAM_AUTHORITIES = {
    "activation_authority",
    "implementation_authority",
    "product_authorization",
    "release_authority",
    "v85_selection",
    "work_packet_execution_authority",
}
_V83_PROJECTION_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus235/"
    "repo_implementation_spec_projection_packet_v235_reference.json"
)
_V83_HANDOFF_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus235/"
    "repo_intent_to_work_packet_handoff_v235_reference.json"
)
_V83_CLOSEOUT_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus235/"
    "repo_semantic_implementation_spec_family_closeout_alignment_v235_reference.json"
)
_V84_MAPPING_DOC = (
    "docs/DRAFT_ADEU_WORK_PACKET_ACTIVATION_REVIEW_V84_IMPLEMENTATION_MAPPING_v0.md"
)
_V84A_MAPPING_DOC = (
    "docs/DRAFT_ADEU_WORK_PACKET_ACTIVATION_REVIEW_V84A_IMPLEMENTATION_MAPPING_v0.md"
)
_V83_COMBINED_DOGFOOD_JSON = (
    "docs/support/arc_series_mapping/"
    "V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_"
    "COMBINED_DOGFOOD_TEST_v0.json"
)


def _source_path(path: str) -> str:
    _repo_ref(path, field_name="source_ref")
    return path


def _validate_sorted_refs(values: list[str], *, field_name: str) -> list[str]:
    return _sorted_unique(values, field_name=field_name)


def _validate_repo_refs(values: list[str], *, field_name: str) -> list[str]:
    normalized = [_repo_ref(value, field_name=field_name) for value in values]
    return _sorted_unique(normalized, field_name=field_name)


def _assert_surface_id(
    *,
    surface_name: str,
    schema: str,
    payload: dict[str, Any],
    id_key: str,
    actual: str,
) -> None:
    expected = _surface_id(surface_name, schema, payload, id_key)
    if actual != expected:
        raise ValueError(f"{id_key} must match canonical surface id")


def _require_terms(value: str, *, field_name: str, terms: tuple[str, ...]) -> str:
    normalized = _non_empty(value, field_name=field_name)
    lowered = normalized.lower()
    missing = [term for term in terms if term not in lowered]
    if missing:
        raise ValueError(f"{field_name} must mention {', '.join(missing)}")
    return normalized


def _reject_v84_action_claim(value: str, *, field_name: str) -> str:
    lowered = value.lower()
    forbidden_patterns = [
        r"\bactivation authority granted\b",
        r"\bactivation performed\b",
        r"\bcode (?:edited|implemented|written)\b",
        r"\bcommand (?:executed|run)\b",
        r"\bcommit(?:ted)? (?:changes|code|diff|implementation|work|to main)\b",
        r"\bdirect oai runtime (?:activated|changed)\b",
        r"\bfile (?:edited|mutated|written)\b",
        r"\bimplementation (?:authorized|executed|performed)\b",
        r"\bimplementation lock (?:created|opened)\b",
        r"\bmerge(?:d)? (?:pr|pull request|branch|changes)\b",
        r"\bmeta[- ]orchestrator runtime (?:mutated|transitioned)\b",
        r"\bmorphic ux runtime (?:changed|updated)\b",
        r"\bpr (?:created|opened)\b",
        r"\bready to implement now\b",
        r"\brelease(?:d)? (?:artifact|authority|build|package|truth|version)\b",
        r"\btarget (?:mutated|changed|updated)\b",
        r"\btool (?:invoked|executed)\b",
        r"\bv85 (?:selected|selection)\b",
        r"\bwork[- ]packet (?:activated|executed|authority granted)\b",
    ]

    def is_negated(match: re.Match[str]) -> bool:
        prefix = lowered[max(0, match.start() - 28) : match.start()]
        suffix = lowered[match.end() : min(len(lowered), match.end() + 28)]
        return bool(
            re.search(
                r"(?:\bno\b|\bnot\b|\bwithout\b|\bmust not\b|\bdoes not\b|\bno[- ])\W*$",
                prefix,
            )
            or re.search(
                r"\b(?:is|are|was|were|remains?|stays?)?\W*"
                r"(?:forbidden|not authorized|not permitted|not granted|requires later)\b",
                suffix,
            )
        )

    for pattern in forbidden_patterns:
        match = re.search(pattern, lowered)
        if match is None:
            continue
        if not is_negated(match):
            raise ValueError(
                f"{field_name} may not carry V84 activation or implementation authority"
            )
    return value


class RepoGeneratedWorkPacketCandidateRow(_CartographyBase):
    generated_candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    generating_actor_kind: GeneratingActorKind
    prompt_context_refs: list[str] = Field(default_factory=list)
    model_or_agent_profile_refs: list[str] = Field(default_factory=list)
    input_projection_packet_refs: list[str] = Field(default_factory=list)
    input_quality_gate_refs: list[str] = Field(default_factory=list)
    generated_output_refs: list[str] = Field(default_factory=list)
    reviewer_amendment_refs: list[str] = Field(default_factory=list)
    generation_scope_posture: GenerationScopePosture
    candidate_authority_posture: GeneratedCandidateAuthorityPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_candidate(self) -> "RepoGeneratedWorkPacketCandidateRow":
        _non_empty(
            self.generated_candidate_ref,
            field_name="generated_candidate_ref",
        )
        _validate_repo_refs(self.source_refs, field_name="source_refs")
        _validate_repo_refs(
            self.prompt_context_refs,
            field_name="prompt_context_refs",
        )
        _validate_repo_refs(
            self.model_or_agent_profile_refs,
            field_name="model_or_agent_profile_refs",
        )
        _validate_sorted_refs(
            self.input_projection_packet_refs,
            field_name="input_projection_packet_refs",
        )
        _validate_sorted_refs(
            self.input_quality_gate_refs,
            field_name="input_quality_gate_refs",
        )
        _validate_repo_refs(
            self.generated_output_refs,
            field_name="generated_output_refs",
        )
        _validate_repo_refs(
            self.reviewer_amendment_refs,
            field_name="reviewer_amendment_refs",
        )
        _reject_v84_action_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("candidate", "review", "no implementation"),
            ),
            field_name="limitation_note",
        )
        if self.generating_actor_kind in {"model", "agent", "tool_assisted_review", "mixed"}:
            if not self.prompt_context_refs or not self.model_or_agent_profile_refs:
                raise ValueError(
                    "generated candidates require prompt and model/agent profile refs"
                )
            if not self.input_projection_packet_refs or not self.input_quality_gate_refs:
                raise ValueError(
                    "generated candidates require V83 projection and quality gate refs"
                )
            if not self.generated_output_refs:
                raise ValueError("generated candidates require generated output refs")
            if self.candidate_authority_posture != "candidate_only":
                raise ValueError("generated candidates must remain candidate-only")
        if self.generation_scope_posture == "generated_from_unbounded_context":
            raise ValueError("generated candidates may not use unbounded generation context")
        return self


class RepoWorkPacketActivationSourceRow(_CartographyBase):
    source_ref: str
    source_kind: CandidateSourceKind
    source_status: SourceStatus
    source_presence_posture: CandidateSourcePresencePosture
    activation_source_role: ActivationSourceRole
    source_currentness: ActivationSourceCurrentness
    projection_authority_posture: ProjectionAuthorityPosture
    work_packet_authority_posture: WorkPacketAuthorityPosture
    generation_posture: GenerationScopePosture
    odeu_lane: OdeuLane
    limitation_note: str

    @model_validator(mode="after")
    def _validate_source_row(self) -> "RepoWorkPacketActivationSourceRow":
        _source_path(self.source_ref)
        _reject_v84_action_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("review", "no implementation"),
            ),
            field_name="limitation_note",
        )
        if self.activation_source_role == "absence_marker":
            if self.source_currentness != "explicit_absence_marker":
                raise ValueError("absence source rows require explicit absence currentness")
            if self.source_presence_posture == "present":
                raise ValueError("absence source rows may not be present")
        if self.activation_source_role in _SUPPORT_ONLY_SOURCE_ROLES:
            if self.projection_authority_posture != "support_context_only":
                raise ValueError("support context rows must not carry projection authority")
            if self.source_currentness == "current_released_source":
                raise ValueError("support context rows cannot be current released sources")
        if self.activation_source_role in {
            "v83_projection_packet_source",
            "v83_quality_gate_source",
            "v83_handoff_source",
            "v83_closeout_source",
        }:
            if self.source_currentness != "current_released_source":
                raise ValueError("released V83 sources require current released source currentness")
            if self.source_presence_posture != "present":
                raise ValueError("released V83 sources must be present")
        if self.activation_source_role == "v83_quality_gate_source":
            if self.projection_authority_posture != "quality_gate_source_for_review_only":
                raise ValueError("quality gate sources must be review-only quality gate sources")
        if self.activation_source_role == "generated_work_packet_candidate_review_source":
            if self.generation_posture == "not_generated":
                raise ValueError("generated candidate sources require generated posture")
            if self.projection_authority_posture != "generated_candidate_source_only":
                raise ValueError("generated candidate sources must be candidate-only sources")
        return self


class RepoWorkPacketActivationSourceIndex(_CartographyBase):
    schema: Literal[REPO_WORK_PACKET_ACTIVATION_SOURCE_INDEX_SCHEMA]
    work_packet_activation_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    source_rows: list[RepoWorkPacketActivationSourceRow] = Field(min_length=1)
    generated_work_packet_candidate_rows: list[RepoGeneratedWorkPacketCandidateRow] = Field(
        default_factory=list
    )
    source_index_summary: str

    @model_validator(mode="after")
    def _validate_source_index(self) -> "RepoWorkPacketActivationSourceIndex":
        _non_empty(
            self.work_packet_activation_source_index_id,
            field_name="work_packet_activation_source_index_id",
        )
        _non_empty(self.review_id, field_name="review_id")
        _non_empty(self.snapshot_id, field_name="snapshot_id")
        _non_empty(self.source_set_id, field_name="source_set_id")
        _sorted_unique_by_ref(
            self.source_rows,
            attr="source_ref",
            field_name="source_rows",
        )
        _sorted_unique_by_ref(
            self.generated_work_packet_candidate_rows,
            attr="generated_candidate_ref",
            field_name="generated_work_packet_candidate_rows",
        )
        known_sources = {row.source_ref for row in self.source_rows}
        for candidate_row in self.generated_work_packet_candidate_rows:
            if any(ref not in known_sources for ref in candidate_row.source_refs):
                raise ValueError("generated candidate source refs must be indexed sources")
        _reject_v84_action_claim(
            _require_terms(
                self.source_index_summary,
                field_name="source_index_summary",
                terms=("source", "review", "no implementation"),
            ),
            field_name="source_index_summary",
        )
        _assert_surface_id(
            surface_name="repo_work_packet_activation_source_index",
            schema=REPO_WORK_PACKET_ACTIVATION_SOURCE_INDEX_SCHEMA,
            payload=self.model_dump(mode="json"),
            id_key="work_packet_activation_source_index_id",
            actual=self.work_packet_activation_source_index_id,
        )
        return self


class RepoWorkPacketActivationReviewRequestRow(_CartographyBase):
    activation_request_ref: str
    activation_package_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    projection_packet_refs: list[str] = Field(default_factory=list)
    quality_gate_refs: list[str] = Field(default_factory=list)
    implementation_spec_refs: list[str] = Field(default_factory=list)
    intent_contract_refs: list[str] = Field(default_factory=list)
    edge_decomposition_refs: list[str] = Field(default_factory=list)
    artifact_obligation_refs: list[str] = Field(default_factory=list)
    drift_register_refs: list[str] = Field(default_factory=list)
    handoff_refs: list[str] = Field(default_factory=list)
    generated_candidate_refs: list[str] = Field(default_factory=list)
    canonical_lock_requirement_refs: list[str] = Field(default_factory=list)
    guardrail_refs: list[str] = Field(min_length=1)
    requested_work_packet_horizon: RequestedWorkPacketHorizon
    requested_activation_review_horizon: RequestedActivationReviewHorizon
    activation_request_recordability_posture: ActivationRequestRecordabilityPosture
    activation_review_eligibility_posture: ActivationReviewEligibilityPosture
    projection_authority_posture: ProjectionAuthorityPosture
    work_packet_authority_posture: WorkPacketAuthorityPosture
    target_surface_posture: TargetSurfacePosture
    validation_evidence_posture: ValidationEvidencePosture
    canonical_lock_requirement: CanonicalLockRequirement
    activation_authority_posture: ActivationAuthorityPosture
    implementation_lock_status: ImplementationLockStatus
    target_family_boundary_posture: TargetFamilyBoundaryPosture
    carried_blocker_refs: list[str] = Field(default_factory=list)
    carried_warning_refs: list[str] = Field(default_factory=list)
    activation_execution_posture: ActivationExecutionPosture
    work_packet_execution_posture: WorkPacketExecutionPosture
    implementation_execution_posture: ImplementationExecutionPosture
    target_mutation_posture: TargetMutationPosture
    pull_request_posture: PullRequestPosture
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_request_row(self) -> "RepoWorkPacketActivationReviewRequestRow":
        for attr in (
            "activation_request_ref",
            "activation_package_ref",
            "candidate_ref",
        ):
            _non_empty(getattr(self, attr), field_name=attr)
        _validate_repo_refs(self.source_refs, field_name="source_refs")
        for attr in (
            "projection_packet_refs",
            "quality_gate_refs",
            "implementation_spec_refs",
            "intent_contract_refs",
            "edge_decomposition_refs",
            "artifact_obligation_refs",
            "drift_register_refs",
            "handoff_refs",
            "generated_candidate_refs",
            "canonical_lock_requirement_refs",
            "guardrail_refs",
            "carried_blocker_refs",
            "carried_warning_refs",
        ):
            _validate_sorted_refs(getattr(self, attr), field_name=attr)
        _sorted_unique(self.odeu_lanes, field_name="odeu_lanes")
        _reject_v84_action_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("review", "no implementation", "later lock"),
            ),
            field_name="limitation_note",
        )
        if (
            self.activation_review_eligibility_posture
            == "eligible_for_work_packet_activation_review"
        ):
            if self.activation_request_recordability_posture in {
                "recordable_from_operator_request_with_absence_markers",
                "recordable_from_support_context_only",
            }:
                raise ValueError("support or absence-only requests cannot be eligible")
            required_lists = {
                "projection_packet_refs": self.projection_packet_refs,
                "quality_gate_refs": self.quality_gate_refs,
                "implementation_spec_refs": self.implementation_spec_refs,
                "intent_contract_refs": self.intent_contract_refs,
                "edge_decomposition_refs": self.edge_decomposition_refs,
                "artifact_obligation_refs": self.artifact_obligation_refs,
                "handoff_refs": self.handoff_refs,
                "canonical_lock_requirement_refs": self.canonical_lock_requirement_refs,
                "guardrail_refs": self.guardrail_refs,
            }
            missing = [name for name, refs in required_lists.items() if not refs]
            if missing:
                raise ValueError(
                    f"eligible activation review requires {', '.join(sorted(missing))}"
                )
            if self.carried_blocker_refs:
                raise ValueError("eligible activation review may not carry blockers")
            if self.target_surface_posture != "bounded_for_later_review":
                raise ValueError(
                    "eligible activation review requires bounded target surface posture"
                )
            if self.validation_evidence_posture != "edge_bound_for_later_review":
                raise ValueError(
                    "eligible activation review requires edge-bound validation evidence"
                )
            if self.canonical_lock_requirement != "canonical_implementation_lock_required":
                raise ValueError(
                    "eligible activation review requires canonical implementation lock"
                )
            if self.work_packet_authority_posture != "work_packet_requires_later_lock":
                raise ValueError("eligible activation review requires later work-packet lock")
            if self.projection_authority_posture != "projection_source_for_review_only":
                raise ValueError(
                    "eligible activation review requires review-only projection source"
                )
            if self.activation_authority_posture == "activation_forbidden_by_this_family":
                raise ValueError("eligible activation review cannot be activation-forbidden")
            if self.implementation_lock_status != "no_implementation_lock_created_by_v84":
                raise ValueError("V84-A cannot create an implementation lock")
            if self.activation_execution_posture != "no_activation_performed_by_v84":
                raise ValueError("V84-A cannot perform activation")
            if self.work_packet_execution_posture != "no_work_packet_execution_performed_by_v84":
                raise ValueError("V84-A cannot execute work packets")
            if self.implementation_execution_posture != "no_implementation_performed_by_v84":
                raise ValueError("V84-A cannot perform implementation")
            if self.target_mutation_posture != "no_target_mutation_performed_by_v84":
                raise ValueError("V84-A cannot mutate targets")
            if self.pull_request_posture != "no_pr_created_by_v84":
                raise ValueError("V84-A cannot create pull requests")
            if self.target_family_boundary_posture == "future_family_only":
                raise ValueError(
                    "eligible activation review cannot target future-family-only posture"
                )
        if (
            self.validation_evidence_posture == "tests_listed_not_sufficient"
            and self.activation_review_eligibility_posture
            == "eligible_for_work_packet_activation_review"
        ):
            raise ValueError("tests listed without edge-bound validation cannot be eligible")
        return self


class RepoWorkPacketActivationReviewRequest(_CartographyBase):
    schema: Literal[REPO_WORK_PACKET_ACTIVATION_REVIEW_REQUEST_SCHEMA]
    work_packet_activation_review_request_id: str
    work_packet_activation_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    activation_request_rows: list[RepoWorkPacketActivationReviewRequestRow] = Field(min_length=1)
    activation_review_summary: str

    @model_validator(mode="after")
    def _validate_request_surface(self) -> "RepoWorkPacketActivationReviewRequest":
        _non_empty(
            self.work_packet_activation_review_request_id,
            field_name="work_packet_activation_review_request_id",
        )
        _non_empty(
            self.work_packet_activation_source_index_id,
            field_name="work_packet_activation_source_index_id",
        )
        _non_empty(self.review_id, field_name="review_id")
        _non_empty(self.snapshot_id, field_name="snapshot_id")
        _non_empty(self.source_set_id, field_name="source_set_id")
        _sorted_unique_by_ref(
            self.activation_request_rows,
            attr="activation_request_ref",
            field_name="activation_request_rows",
        )
        _reject_v84_action_claim(
            _require_terms(
                self.activation_review_summary,
                field_name="activation_review_summary",
                terms=("activation review", "no implementation", "later lock"),
            ),
            field_name="activation_review_summary",
        )
        _assert_surface_id(
            surface_name="repo_work_packet_activation_review_request",
            schema=REPO_WORK_PACKET_ACTIVATION_REVIEW_REQUEST_SCHEMA,
            payload=self.model_dump(mode="json"),
            id_key="work_packet_activation_review_request_id",
            actual=self.work_packet_activation_review_request_id,
        )
        return self


class RepoWorkPacketActivationNonExecutionGuardrailRow(_CartographyBase):
    guardrail_ref: str
    candidate_ref: str
    activation_package_ref: str
    source_refs: list[str] = Field(min_length=1)
    activation_request_refs: list[str] = Field(min_length=1)
    forbidden_implementation_actions: list[ForbiddenImplementationAction] = Field(min_length=1)
    forbidden_runtime_actions: list[ForbiddenRuntimeAction] = Field(min_length=1)
    forbidden_downstream_authority: list[ForbiddenDownstreamAuthority] = Field(min_length=1)
    required_later_authority_refs: list[str] = Field(default_factory=list)
    activation_authority_posture: ActivationAuthorityPosture
    implementation_lock_status: ImplementationLockStatus
    activation_execution_posture: ActivationExecutionPosture
    work_packet_execution_posture: WorkPacketExecutionPosture
    implementation_execution_posture: ImplementationExecutionPosture
    target_mutation_posture: TargetMutationPosture
    pull_request_posture: PullRequestPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_guardrail_row(self) -> "RepoWorkPacketActivationNonExecutionGuardrailRow":
        for attr in ("guardrail_ref", "candidate_ref", "activation_package_ref"):
            _non_empty(getattr(self, attr), field_name=attr)
        _validate_repo_refs(self.source_refs, field_name="source_refs")
        for attr in (
            "activation_request_refs",
            "forbidden_implementation_actions",
            "forbidden_runtime_actions",
            "forbidden_downstream_authority",
            "required_later_authority_refs",
        ):
            _validate_sorted_refs(getattr(self, attr), field_name=attr)
        missing_impl = _REQUIRED_FORBIDDEN_IMPLEMENTATION_ACTIONS.difference(
            self.forbidden_implementation_actions
        )
        if missing_impl:
            raise ValueError(
                "guardrails must forbid required implementation actions: "
                + ", ".join(sorted(missing_impl))
            )
        missing_runtime = _REQUIRED_FORBIDDEN_RUNTIME_ACTIONS.difference(
            self.forbidden_runtime_actions
        )
        if missing_runtime:
            raise ValueError(
                "guardrails must forbid required runtime actions: "
                + ", ".join(sorted(missing_runtime))
            )
        missing_authority = _REQUIRED_FORBIDDEN_DOWNSTREAM_AUTHORITIES.difference(
            self.forbidden_downstream_authority
        )
        if missing_authority:
            raise ValueError(
                "guardrails must forbid required downstream authority: "
                + ", ".join(sorted(missing_authority))
            )
        if self.activation_authority_posture != "no_activation_authority_granted_by_v84":
            raise ValueError("V84-A guardrails cannot grant activation authority")
        if self.implementation_lock_status != "no_implementation_lock_created_by_v84":
            raise ValueError("V84-A guardrails cannot create implementation locks")
        if self.activation_execution_posture != "no_activation_performed_by_v84":
            raise ValueError("V84-A guardrails cannot perform activation")
        if self.work_packet_execution_posture != "no_work_packet_execution_performed_by_v84":
            raise ValueError("V84-A guardrails cannot execute work packets")
        if self.implementation_execution_posture != "no_implementation_performed_by_v84":
            raise ValueError("V84-A guardrails cannot perform implementation")
        if self.target_mutation_posture != "no_target_mutation_performed_by_v84":
            raise ValueError("V84-A guardrails cannot mutate targets")
        if self.pull_request_posture != "no_pr_created_by_v84":
            raise ValueError("V84-A guardrails cannot create pull requests")
        _reject_v84_action_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("guardrail", "no implementation", "no activation"),
            ),
            field_name="limitation_note",
        )
        return self


class RepoWorkPacketActivationNonExecutionGuardrail(_CartographyBase):
    schema: Literal[REPO_WORK_PACKET_ACTIVATION_NON_EXECUTION_GUARDRAIL_SCHEMA]
    work_packet_activation_non_execution_guardrail_id: str
    work_packet_activation_review_request_id: str
    work_packet_activation_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    guardrail_rows: list[RepoWorkPacketActivationNonExecutionGuardrailRow] = Field(min_length=1)
    guardrail_summary: str

    @model_validator(mode="after")
    def _validate_guardrail_surface(self) -> "RepoWorkPacketActivationNonExecutionGuardrail":
        _non_empty(
            self.work_packet_activation_non_execution_guardrail_id,
            field_name="work_packet_activation_non_execution_guardrail_id",
        )
        _non_empty(
            self.work_packet_activation_review_request_id,
            field_name="work_packet_activation_review_request_id",
        )
        _non_empty(
            self.work_packet_activation_source_index_id,
            field_name="work_packet_activation_source_index_id",
        )
        _non_empty(self.review_id, field_name="review_id")
        _non_empty(self.snapshot_id, field_name="snapshot_id")
        _non_empty(self.source_set_id, field_name="source_set_id")
        _sorted_unique_by_ref(
            self.guardrail_rows,
            attr="guardrail_ref",
            field_name="guardrail_rows",
        )
        _reject_v84_action_claim(
            _require_terms(
                self.guardrail_summary,
                field_name="guardrail_summary",
                terms=("guardrail", "no implementation", "no activation"),
            ),
            field_name="guardrail_summary",
        )
        _assert_surface_id(
            surface_name="repo_work_packet_activation_non_execution_guardrail",
            schema=REPO_WORK_PACKET_ACTIVATION_NON_EXECUTION_GUARDRAIL_SCHEMA,
            payload=self.model_dump(mode="json"),
            id_key="work_packet_activation_non_execution_guardrail_id",
            actual=self.work_packet_activation_non_execution_guardrail_id,
        )
        return self


def _v83c_released_bundle(
    repo_root: Path | None = None,
) -> tuple[
    RepoIntentSourceIndex,
    RepoSemanticIntentContract,
    RepoIntentNonImplementationGuardrail,
    RepoIntentEdgeDecomposition,
    RepoArtifactObligationMap,
    RepoSemanticDriftAmbiguityRegister,
    RepoImplementationSpecProjectionPacket,
    RepoIntentToWorkPacketHandoff,
    RepoSemanticImplementationSpecFamilyCloseoutAlignment,
]:
    return derive_v83c_semantic_implementation_projection_bundle(repo_root=repo_root)


def _v84_source_rows() -> list[dict[str, object]]:
    rows = [
        {
            "source_ref": _V83_PROJECTION_FIXTURE,
            "source_kind": "fixture_file",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "activation_source_role": "v83_projection_packet_source",
            "source_currentness": "current_released_source",
            "projection_authority_posture": "projection_source_for_review_only",
            "work_packet_authority_posture": "work_packet_requires_later_lock",
            "generation_posture": "not_generated",
            "odeu_lane": "epistemic",
            "limitation_note": (
                "Released V83-C projection packet source for activation review only; "
                "no implementation."
            ),
        },
        {
            "source_ref": _V83_HANDOFF_FIXTURE,
            "source_kind": "fixture_file",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "activation_source_role": "v83_handoff_source",
            "source_currentness": "current_released_source",
            "projection_authority_posture": "projection_source_for_review_only",
            "work_packet_authority_posture": "work_packet_requires_later_lock",
            "generation_posture": "not_generated",
            "odeu_lane": "epistemic",
            "limitation_note": (
                "Released V83-C handoff source for activation review only; no implementation."
            ),
        },
        {
            "source_ref": _V83_CLOSEOUT_FIXTURE,
            "source_kind": "fixture_file",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "activation_source_role": "v83_closeout_source",
            "source_currentness": "current_released_source",
            "projection_authority_posture": "projection_source_for_review_only",
            "work_packet_authority_posture": "work_packet_requires_later_lock",
            "generation_posture": "not_generated",
            "odeu_lane": "epistemic",
            "limitation_note": (
                "Released V83 family closeout source for activation review only; "
                "no implementation."
            ),
        },
        {
            "source_ref": "docs/ASSESSMENT_vNEXT_PLUS236_EDGES.md",
            "source_kind": "planning_doc",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "activation_source_role": "canonical_lock_requirement_source",
            "source_currentness": "current_released_source",
            "projection_authority_posture": "support_context_only",
            "work_packet_authority_posture": "work_packet_requires_later_lock",
            "generation_posture": "not_generated",
            "odeu_lane": "deontic",
            "limitation_note": (
                "V84-A assessment records later lock requirements for review; "
                "no implementation."
            ),
        },
        {
            "source_ref": _V84A_MAPPING_DOC,
            "source_kind": "planning_doc",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "activation_source_role": "support_process_context",
            "source_currentness": "context_only",
            "projection_authority_posture": "support_context_only",
            "work_packet_authority_posture": "work_packet_review_only",
            "generation_posture": "not_generated",
            "odeu_lane": "utility",
            "limitation_note": (
                "V84-A support mapping contextualizes activation review; no implementation."
            ),
        },
        {
            "source_ref": "docs/DRAFT_NEXT_ARC_OPTIONS_v74.md",
            "source_kind": "planning_doc",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "activation_source_role": "support_process_context",
            "source_currentness": "context_only",
            "projection_authority_posture": "support_context_only",
            "work_packet_authority_posture": "work_packet_review_only",
            "generation_posture": "not_generated",
            "odeu_lane": "utility",
            "limitation_note": (
                "V84 selector is support context for activation review; no implementation."
            ),
        },
        {
            "source_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS236.md",
            "source_kind": "planning_doc",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "activation_source_role": "canonical_lock_requirement_source",
            "source_currentness": "current_released_source",
            "projection_authority_posture": "support_context_only",
            "work_packet_authority_posture": "work_packet_requires_later_lock",
            "generation_posture": "not_generated",
            "odeu_lane": "deontic",
            "limitation_note": (
                "V84-A lock defines review scope and later lock requirements; "
                "no implementation."
            ),
        },
        {
            "source_ref": _V83_COMBINED_DOGFOOD_JSON,
            "source_kind": "support_doc",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "activation_source_role": "combined_dogfood_context",
            "source_currentness": "context_only",
            "projection_authority_posture": "support_context_only",
            "work_packet_authority_posture": "work_packet_review_only",
            "generation_posture": "not_generated",
            "odeu_lane": "epistemic",
            "limitation_note": (
                "Combined dogfood is context for activation review only; no implementation."
            ),
        },
        {
            "source_ref": "docs/support/morphic_ux. v2.md",
            "source_kind": "support_doc",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "activation_source_role": "morphic_ux_support_context",
            "source_currentness": "context_only",
            "projection_authority_posture": "support_context_only",
            "work_packet_authority_posture": "work_packet_review_only",
            "generation_posture": "not_generated",
            "odeu_lane": "utility",
            "limitation_note": (
                "Morphic UX support remains runtime-UI context for review only; "
                "no implementation."
            ),
        },
        {
            "source_ref": _V84_MAPPING_DOC,
            "source_kind": "planning_doc",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "activation_source_role": "generated_work_packet_candidate_review_source",
            "source_currentness": "context_only",
            "projection_authority_posture": "generated_candidate_source_only",
            "work_packet_authority_posture": "work_packet_review_only",
            "generation_posture": "generated_for_review_only",
            "odeu_lane": "utility",
            "limitation_note": (
                "Generated work-packet candidate context is candidate review only; "
                "no implementation."
            ),
        },
    ]
    return sorted(rows, key=lambda row: str(row["source_ref"]))


def derive_v84a_repo_work_packet_activation_source_index(
    *,
    repo_root: Path | None = None,
) -> RepoWorkPacketActivationSourceIndex:
    _ = repo_root
    (
        _intent_source_index,
        _contract,
        _guardrail,
        _edge_decomposition,
        _obligation_map,
        _drift_register,
        projection_packet,
        _handoff,
        _closeout,
    ) = _v83c_released_bundle(repo_root=repo_root)
    packet_row = projection_packet.projection_packet_rows[0]
    quality_gate_ref = packet_row.implementation_spec_quality_gate_rows[0].quality_gate_ref
    payload = {
        "schema": REPO_WORK_PACKET_ACTIVATION_SOURCE_INDEX_SCHEMA,
        "work_packet_activation_source_index_id": "",
        "review_id": "vNext+236",
        "snapshot_id": "vNext+236-work-packet-activation-review-start",
        "source_set_id": "source-set:v84a:work-packet-activation-review",
        "source_rows": _v84_source_rows(),
        "generated_work_packet_candidate_rows": [
            {
                "generated_candidate_ref": "generated-candidate:v84a:intent-to-spec-work-packet",
                "source_refs": [_V84_MAPPING_DOC],
                "generating_actor_kind": "agent",
                "prompt_context_refs": ["docs/DRAFT_NEXT_ARC_OPTIONS_v74.md"],
                "model_or_agent_profile_refs": [
                    "docs/LOCKED_CONTINUATION_vNEXT_PLUS236.md"
                ],
                "input_projection_packet_refs": [packet_row.projection_packet_ref],
                "input_quality_gate_refs": [quality_gate_ref],
                "generated_output_refs": [_V84A_MAPPING_DOC],
                "reviewer_amendment_refs": ["docs/ASSESSMENT_vNEXT_PLUS236_EDGES.md"],
                "generation_scope_posture": "generated_for_review_only",
                "candidate_authority_posture": "candidate_only",
                "limitation_note": (
                    "Generated work-packet candidate remains candidate-only for review; "
                    "no implementation."
                ),
            }
        ],
        "source_index_summary": (
            "V84-A source index binds released V83 projection and handoff sources plus "
            "support context for activation review with no implementation."
        ),
    }
    payload["work_packet_activation_source_index_id"] = _surface_id(
        "repo_work_packet_activation_source_index",
        REPO_WORK_PACKET_ACTIVATION_SOURCE_INDEX_SCHEMA,
        payload,
        "work_packet_activation_source_index_id",
    )
    return RepoWorkPacketActivationSourceIndex.model_validate(payload)


def _v84_request_rows(
    *,
    source_index: RepoWorkPacketActivationSourceIndex,
    projection_packet: RepoImplementationSpecProjectionPacket,
    handoff: RepoIntentToWorkPacketHandoff,
) -> list[dict[str, object]]:
    packet_row = projection_packet.projection_packet_rows[0]
    quality_gate_ref = packet_row.implementation_spec_quality_gate_rows[0].quality_gate_ref
    implementation_spec_refs = sorted(
        spec.implementation_spec_ref for spec in packet_row.implementation_spec_rows
    )
    artifact_obligation_refs = sorted(
        {
            ref
            for spec in packet_row.implementation_spec_rows
            for ref in spec.artifact_obligation_refs
        }
    )
    projection_source = _V83_PROJECTION_FIXTURE
    handoff_source = _V83_HANDOFF_FIXTURE
    closeout_source = _V83_CLOSEOUT_FIXTURE
    lock_source = "docs/LOCKED_CONTINUATION_vNEXT_PLUS236.md"
    assessment_source = "docs/ASSESSMENT_vNEXT_PLUS236_EDGES.md"
    support_source = _V84A_MAPPING_DOC
    morphic_source = "docs/support/morphic_ux. v2.md"
    implementation_handoff = next(
        row
        for row in handoff.handoff_rows
        if row.handoff_ref == "handoff:v83c:implementation-slice-review"
    )
    morphic_handoff = next(
        row
        for row in handoff.handoff_rows
        if row.handoff_ref == "handoff:v83c:morphic-ux-projection-review"
    )
    workflow_handoff = next(
        row
        for row in handoff.handoff_rows
        if row.handoff_ref == "handoff:v83c:workflow-orchestrator-review"
    )
    _ = source_index
    return [
        {
            "activation_request_ref": "activation-request:v84a:intent-to-spec-lock-review",
            "activation_package_ref": "activation-package:v84a:intent-to-spec-lock-review",
            "candidate_ref": packet_row.candidate_ref,
            "source_refs": sorted(
                [
                    assessment_source,
                    closeout_source,
                    handoff_source,
                    lock_source,
                    projection_source,
                ]
            ),
            "projection_packet_refs": [packet_row.projection_packet_ref],
            "quality_gate_refs": [quality_gate_ref],
            "implementation_spec_refs": implementation_spec_refs,
            "intent_contract_refs": sorted(packet_row.intent_contract_refs),
            "edge_decomposition_refs": sorted(packet_row.edge_decomposition_refs),
            "artifact_obligation_refs": artifact_obligation_refs,
            "drift_register_refs": sorted(packet_row.drift_register_refs),
            "handoff_refs": [implementation_handoff.handoff_ref],
            "generated_candidate_refs": ["generated-candidate:v84a:intent-to-spec-work-packet"],
            "canonical_lock_requirement_refs": [
                "canonical-lock-requirement:v84a:intent-to-spec-lock-review"
            ],
            "guardrail_refs": ["guardrail:v84a:intent-to-spec-lock-review"],
            "requested_work_packet_horizon": "repo_description_implementation_slice_review",
            "requested_activation_review_horizon": "implementation_lock_review_package",
            "activation_request_recordability_posture": "recordable_from_released_v83_projection",
            "activation_review_eligibility_posture": "eligible_for_work_packet_activation_review",
            "projection_authority_posture": "projection_source_for_review_only",
            "work_packet_authority_posture": "work_packet_requires_later_lock",
            "target_surface_posture": "bounded_for_later_review",
            "validation_evidence_posture": "edge_bound_for_later_review",
            "canonical_lock_requirement": "canonical_implementation_lock_required",
            "activation_authority_posture": "no_activation_authority_granted_by_v84",
            "implementation_lock_status": "no_implementation_lock_created_by_v84",
            "target_family_boundary_posture": (
                "repo_description_implementation_allowed_for_later_lock_review"
            ),
            "carried_blocker_refs": [],
            "carried_warning_refs": [],
            "activation_execution_posture": "no_activation_performed_by_v84",
            "work_packet_execution_posture": "no_work_packet_execution_performed_by_v84",
            "implementation_execution_posture": "no_implementation_performed_by_v84",
            "target_mutation_posture": "no_target_mutation_performed_by_v84",
            "pull_request_posture": "no_pr_created_by_v84",
            "odeu_lanes": sorted(["deontic", "epistemic", "utility"]),
            "limitation_note": (
                "Activation review is eligible only for later lock package review; "
                "no implementation and no later lock is created here."
            ),
        },
        {
            "activation_request_ref": "activation-request:v84a:meta-orchestrator-review",
            "activation_package_ref": "activation-package:v84a:meta-orchestrator-review",
            "candidate_ref": packet_row.candidate_ref,
            "source_refs": sorted([handoff_source, support_source]),
            "projection_packet_refs": [packet_row.projection_packet_ref],
            "quality_gate_refs": [quality_gate_ref],
            "implementation_spec_refs": [],
            "intent_contract_refs": sorted(packet_row.intent_contract_refs),
            "edge_decomposition_refs": sorted(packet_row.edge_decomposition_refs),
            "artifact_obligation_refs": [],
            "drift_register_refs": sorted(packet_row.drift_register_refs),
            "handoff_refs": [workflow_handoff.handoff_ref],
            "generated_candidate_refs": [],
            "canonical_lock_requirement_refs": [
                "canonical-lock-requirement:v84a:meta-orchestrator-runtime-review"
            ],
            "guardrail_refs": ["guardrail:v84a:meta-orchestrator-review"],
            "requested_work_packet_horizon": "meta_orchestrator_workflow_activation_review",
            "requested_activation_review_horizon": (
                "meta_orchestrator_workflow_runtime_authority_review_package"
            ),
            "activation_request_recordability_posture": "recordable_from_released_v83_handoff",
            "activation_review_eligibility_posture": "request_recorded_for_review_only",
            "projection_authority_posture": "projection_source_for_review_only",
            "work_packet_authority_posture": "work_packet_requires_later_lock",
            "target_surface_posture": "warning_future_family_boundary",
            "validation_evidence_posture": "future_family_only",
            "canonical_lock_requirement": "meta_orchestrator_runtime_authority_review_required",
            "activation_authority_posture": "no_activation_authority_granted_by_v84",
            "implementation_lock_status": "no_implementation_lock_created_by_v84",
            "target_family_boundary_posture": (
                "meta_orchestrator_requires_workflow_runtime_authority_review"
            ),
            "carried_blocker_refs": [],
            "carried_warning_refs": sorted(workflow_handoff.carried_drift_refs),
            "activation_execution_posture": "no_activation_performed_by_v84",
            "work_packet_execution_posture": "no_work_packet_execution_performed_by_v84",
            "implementation_execution_posture": "no_implementation_performed_by_v84",
            "target_mutation_posture": "no_target_mutation_performed_by_v84",
            "pull_request_posture": "no_pr_created_by_v84",
            "odeu_lanes": sorted(["deontic", "utility"]),
            "limitation_note": (
                "Meta-orchestrator pressure is recorded for later lock review; "
                "no implementation and no runtime transition occurs."
            ),
        },
        {
            "activation_request_ref": "activation-request:v84a:morphic-ux-review",
            "activation_package_ref": "activation-package:v84a:morphic-ux-review",
            "candidate_ref": packet_row.candidate_ref,
            "source_refs": sorted([handoff_source, morphic_source, support_source]),
            "projection_packet_refs": [packet_row.projection_packet_ref],
            "quality_gate_refs": [quality_gate_ref],
            "implementation_spec_refs": [],
            "intent_contract_refs": sorted(packet_row.intent_contract_refs),
            "edge_decomposition_refs": sorted(packet_row.edge_decomposition_refs),
            "artifact_obligation_refs": [],
            "drift_register_refs": sorted(packet_row.drift_register_refs),
            "handoff_refs": [morphic_handoff.handoff_ref],
            "generated_candidate_refs": [],
            "canonical_lock_requirement_refs": [
                "canonical-lock-requirement:v84a:morphic-runtime-ui-review"
            ],
            "guardrail_refs": ["guardrail:v84a:morphic-ux-review"],
            "requested_work_packet_horizon": "morphic_ux_projection_implementation_review",
            "requested_activation_review_horizon": "morphic_ux_runtime_ui_authority_review_package",
            "activation_request_recordability_posture": "recordable_from_released_v83_handoff",
            "activation_review_eligibility_posture": "request_recorded_for_review_only",
            "projection_authority_posture": "projection_source_for_review_only",
            "work_packet_authority_posture": "work_packet_requires_later_lock",
            "target_surface_posture": "warning_future_family_boundary",
            "validation_evidence_posture": "future_family_only",
            "canonical_lock_requirement": "morphic_ux_runtime_authority_review_required",
            "activation_authority_posture": "no_activation_authority_granted_by_v84",
            "implementation_lock_status": "no_implementation_lock_created_by_v84",
            "target_family_boundary_posture": "morphic_ux_requires_runtime_ui_authority_review",
            "carried_blocker_refs": [],
            "carried_warning_refs": sorted(morphic_handoff.carried_drift_refs),
            "activation_execution_posture": "no_activation_performed_by_v84",
            "work_packet_execution_posture": "no_work_packet_execution_performed_by_v84",
            "implementation_execution_posture": "no_implementation_performed_by_v84",
            "target_mutation_posture": "no_target_mutation_performed_by_v84",
            "pull_request_posture": "no_pr_created_by_v84",
            "odeu_lanes": sorted(["deontic", "utility"]),
            "limitation_note": (
                "Morphic UX pressure is recorded for later lock review; no implementation "
                "and no runtime UI change."
            ),
        },
    ]


def derive_v84a_repo_work_packet_activation_review_request(
    *,
    repo_root: Path | None = None,
    work_packet_activation_source_index: RepoWorkPacketActivationSourceIndex | None = None,
) -> RepoWorkPacketActivationReviewRequest:
    if work_packet_activation_source_index is None:
        work_packet_activation_source_index = derive_v84a_repo_work_packet_activation_source_index(
            repo_root=repo_root
        )
    (
        _intent_source_index,
        _contract,
        _guardrail,
        _edge_decomposition,
        _obligation_map,
        _drift_register,
        projection_packet,
        handoff,
        _closeout,
    ) = _v83c_released_bundle(repo_root=repo_root)
    payload = {
        "schema": REPO_WORK_PACKET_ACTIVATION_REVIEW_REQUEST_SCHEMA,
        "work_packet_activation_review_request_id": "",
        "work_packet_activation_source_index_id": (
            work_packet_activation_source_index.work_packet_activation_source_index_id
        ),
        "review_id": work_packet_activation_source_index.review_id,
        "snapshot_id": work_packet_activation_source_index.snapshot_id,
        "source_set_id": work_packet_activation_source_index.source_set_id,
        "activation_request_rows": _v84_request_rows(
            source_index=work_packet_activation_source_index,
            projection_packet=projection_packet,
            handoff=handoff,
        ),
        "activation_review_summary": (
            "V84-A records activation review requests for later lock packages with "
            "no implementation and no later lock created here."
        ),
    }
    payload["work_packet_activation_review_request_id"] = _surface_id(
        "repo_work_packet_activation_review_request",
        REPO_WORK_PACKET_ACTIVATION_REVIEW_REQUEST_SCHEMA,
        payload,
        "work_packet_activation_review_request_id",
    )
    return RepoWorkPacketActivationReviewRequest.model_validate(payload)


def _v84_guardrail_rows(
    *, activation_review_request: RepoWorkPacketActivationReviewRequest
) -> list[dict[str, object]]:
    projection_source = _V83_PROJECTION_FIXTURE
    handoff_source = _V83_HANDOFF_FIXTURE
    support_source = _V84A_MAPPING_DOC
    rows_by_ref: dict[str, dict[str, object]] = {}
    for request_row in activation_review_request.activation_request_rows:
        for guardrail_ref in request_row.guardrail_refs:
            row = rows_by_ref.setdefault(
                guardrail_ref,
                {
                    "guardrail_ref": guardrail_ref,
                    "candidate_ref": request_row.candidate_ref,
                    "activation_package_ref": request_row.activation_package_ref,
                    "source_refs": [],
                    "activation_request_refs": [],
                    "forbidden_implementation_actions": sorted(
                        _REQUIRED_FORBIDDEN_IMPLEMENTATION_ACTIONS
                    ),
                    "forbidden_runtime_actions": sorted(
                        _REQUIRED_FORBIDDEN_RUNTIME_ACTIONS.union(
                            {
                                "activate_direct_oai_runtime",
                                "change_morphic_ux_runtime",
                                "mutate_meta_orchestrator_runtime",
                            }
                        )
                    ),
                    "forbidden_downstream_authority": sorted(
                        _REQUIRED_FORBIDDEN_DOWNSTREAM_AUTHORITIES
                    ),
                    "required_later_authority_refs": [],
                    "activation_authority_posture": "no_activation_authority_granted_by_v84",
                    "implementation_lock_status": "no_implementation_lock_created_by_v84",
                    "activation_execution_posture": "no_activation_performed_by_v84",
                    "work_packet_execution_posture": (
                        "no_work_packet_execution_performed_by_v84"
                    ),
                    "implementation_execution_posture": "no_implementation_performed_by_v84",
                    "target_mutation_posture": "no_target_mutation_performed_by_v84",
                    "pull_request_posture": "no_pr_created_by_v84",
                    "limitation_note": (
                        "Guardrail preserves activation review only with no activation, "
                        "no implementation, no command, no PR, and no release."
                    ),
                },
            )
            if row["candidate_ref"] != request_row.candidate_ref:
                raise ValueError("shared guardrail refs must use one candidate")
            if row["activation_package_ref"] != request_row.activation_package_ref:
                raise ValueError("shared guardrail refs must use one activation package")
            row["source_refs"] = sorted(
                set(row["source_refs"]).union({handoff_source, projection_source, support_source})
            )
            row["activation_request_refs"] = sorted(
                set(row["activation_request_refs"]).union({request_row.activation_request_ref})
            )
            row["required_later_authority_refs"] = sorted(
                set(row["required_later_authority_refs"]).union(
                    request_row.canonical_lock_requirement_refs
                )
            )
    return sorted(rows_by_ref.values(), key=lambda row: str(row["guardrail_ref"]))


def derive_v84a_repo_work_packet_activation_non_execution_guardrail(
    *,
    repo_root: Path | None = None,
    work_packet_activation_source_index: RepoWorkPacketActivationSourceIndex | None = None,
    work_packet_activation_review_request: RepoWorkPacketActivationReviewRequest | None = None,
) -> RepoWorkPacketActivationNonExecutionGuardrail:
    if work_packet_activation_source_index is None:
        work_packet_activation_source_index = derive_v84a_repo_work_packet_activation_source_index(
            repo_root=repo_root
        )
    if work_packet_activation_review_request is None:
        work_packet_activation_review_request = (
            derive_v84a_repo_work_packet_activation_review_request(
                repo_root=repo_root,
                work_packet_activation_source_index=work_packet_activation_source_index,
            )
        )
    payload = {
        "schema": REPO_WORK_PACKET_ACTIVATION_NON_EXECUTION_GUARDRAIL_SCHEMA,
        "work_packet_activation_non_execution_guardrail_id": "",
        "work_packet_activation_review_request_id": (
            work_packet_activation_review_request.work_packet_activation_review_request_id
        ),
        "work_packet_activation_source_index_id": (
            work_packet_activation_source_index.work_packet_activation_source_index_id
        ),
        "review_id": work_packet_activation_source_index.review_id,
        "snapshot_id": work_packet_activation_source_index.snapshot_id,
        "source_set_id": work_packet_activation_source_index.source_set_id,
        "guardrail_rows": _v84_guardrail_rows(
            activation_review_request=work_packet_activation_review_request
        ),
        "guardrail_summary": (
            "V84-A non-execution guardrails keep activation review from becoming "
            "activation authority, implementation, PR work, or release; no activation "
            "and no implementation."
        ),
    }
    payload["work_packet_activation_non_execution_guardrail_id"] = _surface_id(
        "repo_work_packet_activation_non_execution_guardrail",
        REPO_WORK_PACKET_ACTIVATION_NON_EXECUTION_GUARDRAIL_SCHEMA,
        payload,
        "work_packet_activation_non_execution_guardrail_id",
    )
    return RepoWorkPacketActivationNonExecutionGuardrail.model_validate(payload)


def validate_v84a_work_packet_activation_review_bundle(
    *,
    v83_intent_source_index: RepoIntentSourceIndex,
    v83_semantic_intent_contract: RepoSemanticIntentContract,
    v83_intent_non_implementation_guardrail: RepoIntentNonImplementationGuardrail,
    v83_intent_edge_decomposition: RepoIntentEdgeDecomposition,
    v83_artifact_obligation_map: RepoArtifactObligationMap,
    v83_semantic_drift_ambiguity_register: RepoSemanticDriftAmbiguityRegister,
    v83_implementation_spec_projection_packet: RepoImplementationSpecProjectionPacket,
    v83_intent_to_work_packet_handoff: RepoIntentToWorkPacketHandoff,
    v83_semantic_implementation_spec_family_closeout_alignment: (
        RepoSemanticImplementationSpecFamilyCloseoutAlignment
    ),
    work_packet_activation_source_index: RepoWorkPacketActivationSourceIndex,
    work_packet_activation_review_request: RepoWorkPacketActivationReviewRequest,
    work_packet_activation_non_execution_guardrail: (
        RepoWorkPacketActivationNonExecutionGuardrail
    ),
) -> None:
    validate_v83c_semantic_implementation_projection_bundle(
        intent_source_index=v83_intent_source_index,
        semantic_intent_contract=v83_semantic_intent_contract,
        intent_non_implementation_guardrail=v83_intent_non_implementation_guardrail,
        intent_edge_decomposition=v83_intent_edge_decomposition,
        artifact_obligation_map=v83_artifact_obligation_map,
        semantic_drift_ambiguity_register=v83_semantic_drift_ambiguity_register,
        implementation_spec_projection_packet=v83_implementation_spec_projection_packet,
        intent_to_work_packet_handoff=v83_intent_to_work_packet_handoff,
        semantic_implementation_spec_family_closeout_alignment=(
            v83_semantic_implementation_spec_family_closeout_alignment
        ),
    )
    if (
        work_packet_activation_review_request.work_packet_activation_source_index_id
        != work_packet_activation_source_index.work_packet_activation_source_index_id
    ):
        raise ValueError("V84-A request must reference released V84-A source index")
    if (
        work_packet_activation_non_execution_guardrail.work_packet_activation_source_index_id
        != work_packet_activation_source_index.work_packet_activation_source_index_id
        or work_packet_activation_non_execution_guardrail.work_packet_activation_review_request_id
        != work_packet_activation_review_request.work_packet_activation_review_request_id
    ):
        raise ValueError(
            "V84-A guardrails must reference released V84-A request and source index"
        )

    known_source_roles = {
        row.source_ref: row.activation_source_role
        for row in work_packet_activation_source_index.source_rows
    }
    known_source_refs = set(known_source_roles)
    known_generated = {
        row.generated_candidate_ref: row
        for row in work_packet_activation_source_index.generated_work_packet_candidate_rows
    }
    known_projection_packets = {
        row.projection_packet_ref: row
        for row in v83_implementation_spec_projection_packet.projection_packet_rows
    }
    known_quality_gates = {
        gate.quality_gate_ref: gate
        for packet in known_projection_packets.values()
        for gate in packet.implementation_spec_quality_gate_rows
    }
    known_specs = {
        spec.implementation_spec_ref
        for packet in known_projection_packets.values()
        for spec in packet.implementation_spec_rows
    }
    known_handoffs = {
        row.handoff_ref: row for row in v83_intent_to_work_packet_handoff.handoff_rows
    }
    known_guardrails = {
        row.guardrail_ref: row
        for row in work_packet_activation_non_execution_guardrail.guardrail_rows
    }
    known_requests = {
        row.activation_request_ref: row
        for row in work_packet_activation_review_request.activation_request_rows
    }

    for candidate_row in work_packet_activation_source_index.generated_work_packet_candidate_rows:
        if any(
            ref not in known_projection_packets
            for ref in candidate_row.input_projection_packet_refs
        ):
            raise ValueError(
                "generated candidate projection refs must be released V83 projection refs"
            )
        if any(ref not in known_quality_gates for ref in candidate_row.input_quality_gate_refs):
            raise ValueError(
                "generated candidate quality gate refs must be released V83 quality gates"
            )

    for request_row in work_packet_activation_review_request.activation_request_rows:
        if any(ref not in known_source_refs for ref in request_row.source_refs):
            raise ValueError("activation request source refs must be indexed")
        if any(ref not in known_projection_packets for ref in request_row.projection_packet_refs):
            raise ValueError(
                "activation request projection refs must be released V83 projection refs"
            )
        if any(ref not in known_quality_gates for ref in request_row.quality_gate_refs):
            raise ValueError(
                "activation request quality gate refs must be released V83 quality gates"
            )
        if any(ref not in known_specs for ref in request_row.implementation_spec_refs):
            raise ValueError(
                "activation request spec refs must be released V83 implementation specs"
            )
        if any(ref not in known_handoffs for ref in request_row.handoff_refs):
            raise ValueError("activation request handoff refs must be released V83 handoff refs")
        if any(ref not in known_generated for ref in request_row.generated_candidate_refs):
            raise ValueError("activation request generated candidate refs must be indexed")
        if any(ref not in known_guardrails for ref in request_row.guardrail_refs):
            raise ValueError("activation request guardrail refs must be released V84-A guardrails")
        for guardrail_ref in request_row.guardrail_refs:
            guardrail_row = known_guardrails[guardrail_ref]
            if request_row.activation_request_ref not in guardrail_row.activation_request_refs:
                raise ValueError("activation request guardrails must link back to request")
            if guardrail_row.candidate_ref != request_row.candidate_ref:
                raise ValueError("activation request guardrails must match candidate")
            if guardrail_row.activation_package_ref != request_row.activation_package_ref:
                raise ValueError("activation request guardrails must match activation package")
        if request_row.activation_review_eligibility_posture == (
            "eligible_for_work_packet_activation_review"
        ):
            roles = {known_source_roles[ref] for ref in request_row.source_refs}
            if roles.issubset(_SUPPORT_ONLY_SOURCE_ROLES):
                raise ValueError("support-only sources cannot make activation review eligible")
            if not roles.intersection(_ELIGIBLE_SOURCE_ROLES):
                raise ValueError(
                    "eligible activation request requires released V83 projection or handoff"
                )
            for generated_ref in request_row.generated_candidate_refs:
                generated_row = known_generated[generated_ref]
                if generated_row.candidate_authority_posture != "candidate_only":
                    raise ValueError("generated work-packet candidates must remain candidate-only")
                if (
                    not generated_row.input_projection_packet_refs
                    or not generated_row.input_quality_gate_refs
                ):
                    raise ValueError("generated candidates require released V83 provenance")

    for guardrail_row in work_packet_activation_non_execution_guardrail.guardrail_rows:
        if any(ref not in known_source_refs for ref in guardrail_row.source_refs):
            raise ValueError("guardrail source refs must be indexed")
        if any(ref not in known_requests for ref in guardrail_row.activation_request_refs):
            raise ValueError("guardrail request refs must be released V84-A requests")
        request_packages = {
            known_requests[ref].activation_package_ref
            for ref in guardrail_row.activation_request_refs
        }
        if request_packages != {guardrail_row.activation_package_ref}:
            raise ValueError("guardrail activation package must match request package")


def derive_v84a_work_packet_activation_review_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoIntentSourceIndex,
    RepoSemanticIntentContract,
    RepoIntentNonImplementationGuardrail,
    RepoIntentEdgeDecomposition,
    RepoArtifactObligationMap,
    RepoSemanticDriftAmbiguityRegister,
    RepoImplementationSpecProjectionPacket,
    RepoIntentToWorkPacketHandoff,
    RepoSemanticImplementationSpecFamilyCloseoutAlignment,
    RepoWorkPacketActivationSourceIndex,
    RepoWorkPacketActivationReviewRequest,
    RepoWorkPacketActivationNonExecutionGuardrail,
]:
    (
        intent_source_index,
        semantic_intent_contract,
        intent_non_implementation_guardrail,
        intent_edge_decomposition,
        artifact_obligation_map,
        semantic_drift_ambiguity_register,
        implementation_spec_projection_packet,
        intent_to_work_packet_handoff,
        semantic_implementation_spec_family_closeout_alignment,
    ) = _v83c_released_bundle(repo_root=repo_root)
    source_index = derive_v84a_repo_work_packet_activation_source_index(repo_root=repo_root)
    request = derive_v84a_repo_work_packet_activation_review_request(
        repo_root=repo_root,
        work_packet_activation_source_index=source_index,
    )
    guardrail = derive_v84a_repo_work_packet_activation_non_execution_guardrail(
        repo_root=repo_root,
        work_packet_activation_source_index=source_index,
        work_packet_activation_review_request=request,
    )
    validate_v84a_work_packet_activation_review_bundle(
        v83_intent_source_index=intent_source_index,
        v83_semantic_intent_contract=semantic_intent_contract,
        v83_intent_non_implementation_guardrail=intent_non_implementation_guardrail,
        v83_intent_edge_decomposition=intent_edge_decomposition,
        v83_artifact_obligation_map=artifact_obligation_map,
        v83_semantic_drift_ambiguity_register=semantic_drift_ambiguity_register,
        v83_implementation_spec_projection_packet=implementation_spec_projection_packet,
        v83_intent_to_work_packet_handoff=intent_to_work_packet_handoff,
        v83_semantic_implementation_spec_family_closeout_alignment=(
            semantic_implementation_spec_family_closeout_alignment
        ),
        work_packet_activation_source_index=source_index,
        work_packet_activation_review_request=request,
        work_packet_activation_non_execution_guardrail=guardrail,
    )
    return (
        intent_source_index,
        semantic_intent_contract,
        intent_non_implementation_guardrail,
        intent_edge_decomposition,
        artifact_obligation_map,
        semantic_drift_ambiguity_register,
        implementation_spec_projection_packet,
        intent_to_work_packet_handoff,
        semantic_implementation_spec_family_closeout_alignment,
        source_index,
        request,
        guardrail,
    )
