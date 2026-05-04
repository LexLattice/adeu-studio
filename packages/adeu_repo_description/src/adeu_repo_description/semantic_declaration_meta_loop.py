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
    CandidateAuthorityLayer,
    CandidateSourceKind,
    CandidateSourcePresencePosture,
    OdeuLane,
)
from .work_packet_activation_review import (
    RepoPostWorkPacketActivationReviewHandoff,
    RepoWorkPacketActivationFamilyCloseoutAlignment,
    RepoWorkPacketActivationReadinessSummary,
    derive_v84c_work_packet_activation_closeout_bundle,
)

REPO_TURN_SEMANTIC_DECLARATION_REQUEST_SCHEMA = "repo_turn_semantic_declaration_request@1"
REPO_SEMANTIC_DECLARATION_SOURCE_INDEX_SCHEMA = "repo_semantic_declaration_source_index@1"
REPO_SEMANTIC_DECLARATION_NON_AUTHORITY_GUARDRAIL_SCHEMA = (
    "repo_semantic_declaration_non_authority_guardrail@1"
)
REPO_CANONICAL_META_LOOKUP_INDEX_SCHEMA = "repo_canonical_meta_lookup_index@1"
REPO_SEMANTIC_OPERATOR_CLASS_REGISTRY_SCHEMA = "repo_semantic_operator_class_registry@1"
REPO_OBLIGATION_FAMILY_REGISTRY_SCHEMA = "repo_obligation_family_registry@1"
REPO_SEMANTIC_POINTER_LOOKUP_FIXTURE_SCHEMA = "repo_semantic_pointer_lookup_fixture@1"

SemanticDeclarationSourceRole = Literal[
    "v84_readiness_summary_source",
    "v84_handoff_source",
    "v84_closeout_source",
    "v83_projection_packet_context",
    "combined_dogfood_context",
    "post_v84_roadmap_source",
    "canonical_meta_loop_support_source",
    "morphic_ux_support_context",
    "direct_oai_support_context",
    "meta_orchestrator_support_context",
    "operator_turn_source",
    "repo_task_context_source",
    "natural_task_context_source",
    "code_context_source",
    "canonical_pointer_context",
    "opaque_pointer_context",
    "generated_declaration_candidate_source",
    "model_or_agent_profile_source",
    "reviewer_amendment_source",
    "explicit_absence_marker",
    "support_process_context",
]
SemanticDeclarationSourceCurrentness = Literal[
    "current_concrete_source",
    "current_operator_turn",
    "support_context_only",
    "historical_context_only",
    "explicit_absence_marker",
    "stale_or_superseded",
    "unknown_needs_review",
]
DeclarationAuthorityPosture = Literal[
    "source_for_review_only",
    "candidate_only",
    "support_context_not_authority",
    "authority_requires_later_lock",
    "authority_explicitly_absent",
    "not_applicable",
]
LoopAuthorityPosture = Literal[
    "loop_sequence_meaning_owned_by_harness",
    "model_output_candidate_only",
    "transition_requires_later_table",
    "no_loop_authority_granted",
    "not_applicable",
]
WitnessedElement = Literal[
    "operator",
    "object_class",
    "source_class",
    "target_class",
    "target_context",
    "modifier",
    "negative_cue",
    "uncertainty",
]
WitnessStrength = Literal[
    "direct",
    "indirect",
    "contextual",
    "support_only",
    "absence_marker",
    "conflict_marker",
]
WitnessCurrentness = Literal[
    "current_turn_witness",
    "current_repo_context",
    "support_context_only",
    "explicit_absence_marker",
    "stale_or_superseded",
    "unknown_needs_review",
]
NegativeCueKind = Literal[
    "asks_to_implement_now",
    "asks_to_execute_now",
    "asks_to_select_next_family",
    "asks_to_authorize_runtime",
    "asks_to_productize",
    "asks_to_release",
    "asks_to_expand_obligations_now",
    "asks_to_skip_lookup",
    "asks_to_invent_class",
]
NegativeCueEffect = Literal[
    "blocks_eligibility",
    "routes_to_guardrail",
    "routes_to_future_family_only",
    "allowed_context_only",
]
ResidentModelCompetencyKind = Literal[
    "pointer_obedience",
    "artifact_shape_obedience",
    "bounded_local_judgment",
    "declared_uncertainty_routing",
    "order_preservation",
    "duplicate_preservation",
    "unknown_pointer_abstention",
    "no_unauthorized_transition",
    "stop_at_schema_boundary",
]
CompetencyRequiredPosture = Literal[
    "required_for_declaration_review",
    "required_for_future_lookup_review",
    "not_claimed_by_v85a",
]
CompetencyFailureRoutingPosture = Literal[
    "route_to_uncertainty_slot",
    "route_to_abstain",
    "route_to_registry_gap",
    "route_to_guardrail",
    "route_to_future_family_only",
]
DeclarationBindingPosture = Literal[
    "selected",
    "ambiguous",
    "abstain",
    "registry_gap",
    "malformed",
    "blocked_by_missing_source",
    "future_family_only",
    "rejected_out_of_scope",
]
BindingResolutionPosture = Literal[
    "selected_for_later_lookup_review",
    "ambiguous_requires_review",
    "abstain_declared",
    "registry_gap_declared",
    "malformed_input_declared",
    "blocked_by_missing_witness",
    "support_only_not_selected",
]
DeclarationCandidateStatus = Literal[
    "candidate_recorded_for_review",
    "ambiguous_candidate",
    "abstain_candidate",
    "registry_gap_candidate",
    "malformed_candidate",
    "support_context_only_candidate",
]
CanonicalLookupStatus = Literal[
    "lookup_not_selected_by_v85a",
    "lookup_required_later",
    "lookup_blocked_by_missing_pointer",
    "lookup_blocked_by_registry_gap",
    "lookup_not_applicable",
]
DeclarationSelectionStatus = Literal[
    "not_selected_by_v85a",
    "ambiguous_not_selected",
    "abstained_not_selected",
    "registry_gap_not_selected",
    "blocked_not_selected",
]
DeclarationRecordabilityPosture = Literal[
    "recordable_from_concrete_operator_turn",
    "recordable_from_repo_context",
    "recordable_from_support_context_only",
    "recordable_from_generated_declaration_candidate",
    "recordable_with_absence_markers",
    "not_recordable_missing_source",
]
DeclarationReviewEligibilityPosture = Literal[
    "eligible_for_semantic_declaration_review",
    "blocked_by_missing_turn_source",
    "blocked_by_missing_repo_context",
    "blocked_by_support_only_source",
    "blocked_by_generated_declaration_provenance_gap",
    "blocked_by_ambiguous_binding",
    "blocked_by_registry_gap",
    "blocked_by_missing_witness",
    "blocked_by_missing_guardrail",
    "future_family_only",
    "rejected_out_of_scope",
]
CanonicalLookupRequiredPosture = Literal[
    "lookup_required_later",
    "lookup_not_selected_by_v85a",
    "lookup_blocked_by_missing_pointer",
    "lookup_blocked_by_registry_gap",
    "lookup_not_applicable",
]
CanonicalStatus = Literal[
    "canonical_pointer_claimed_for_later_lookup",
    "canonical_status_unverified_by_v85a",
    "candidate_class_only",
    "unknown_class_registry_gap",
    "not_applicable",
]
AmbiguityPosture = Literal[
    "not_ambiguous",
    "ambiguous_requires_review",
    "ambiguous_support_context_only",
]
RegistryGapPosture = Literal[
    "no_registry_gap_claimed",
    "unknown_class_registry_gap",
    "unknown_operator_registry_gap",
    "unknown_version_registry_gap",
]
DeclarationHorizon = Literal[
    "semantic_act_declaration",
    "semantic_pointer_candidate",
    "resident_model_competency",
    "future_family_only",
]
RequestedDeclarationReviewHorizon = Literal[
    "semantic_declaration_review",
    "ambiguity_review",
    "registry_gap_review",
    "support_context_review",
    "future_family_only",
]
DeclarationNonAuthorityPosture = Literal[
    "no_declaration_authority_granted_by_v85",
    "declaration_requires_later_lookup_review",
    "declaration_forbidden_as_authority",
]
ObligationExpansionPosture = Literal[
    "no_obligation_expansion_performed_by_v85a",
    "obligation_expansion_requires_v86_or_later",
    "obligation_expansion_forbidden_by_this_slice",
]
ImplementationPosture = Literal[
    "no_implementation_performed_by_v85a",
    "implementation_requires_later_lock",
    "implementation_forbidden_by_this_family",
]
RuntimeTransitionPosture = Literal[
    "no_runtime_transition_performed_by_v85a",
    "runtime_transition_requires_later_authority",
    "runtime_transition_forbidden_by_this_family",
]
FutureFamilySelectionPosture = Literal[
    "no_future_family_selected_by_v85a",
    "future_family_selection_requires_later_selector",
    "future_family_selection_forbidden_by_this_slice",
]
ForbiddenDeclarationAction = Literal[
    "expand_obligations",
    "emit_evidence_contract",
    "emit_edge_probe_plan",
    "emit_reviewer_taskpack",
    "emit_audit_report",
    "run_closeout_transition_table",
    "create_canonical_lookup_index",
    "create_operator_class_registry",
    "create_obligation_family_registry",
    "create_pointer_lookup_fixture",
    "create_declaration_summary",
    "create_post_declaration_handoff",
]
ForbiddenDownstreamAction = Literal[
    "create_implementation_lock",
    "activate_work_packet",
    "execute_work_packet",
    "edit_code",
    "run_command",
    "invoke_tool_for_effect",
    "mutate_target",
    "open_pr",
    "commit_changes",
    "merge_or_release",
    "authorize_product",
    "create_graph_memory_authority",
    "amend_recursive_policy",
    "select_v86",
]
LookupInputKind = Literal[
    "opaque_pointer",
    "explicit_semantic_pointer",
    "natural_binding_candidate",
    "registry_gap_candidate",
    "support_context_only",
]
LookupPosture = Literal[
    "exact_match_for_review_only",
    "ambiguous_match",
    "unknown_pointer_abstained",
    "registry_gap",
    "conflict_requires_review",
    "blocked_by_missing_source",
    "future_family_only",
]
V85BCanonicalLookupStatus = Literal[
    "exact_match_for_review_only",
    "ambiguous_match",
    "unknown_pointer_abstained",
    "registry_gap",
    "conflict_requires_review",
    "lookup_blocked_by_missing_source",
    "future_family_only",
]
PointerParsePosture = Literal[
    "parsed_exact",
    "parsed_with_alias",
    "malformed_pointer",
    "unknown_operator",
    "unknown_class",
    "unknown_version",
    "ambiguous_parse",
    "abstain_required",
]
PointerNormalizationPosture = Literal[
    "normalization_not_required",
    "alias_normalized_by_registry",
    "normalization_rejected",
    "normalization_not_authorized",
    "not_applicable",
]
PointerCompetencyKind = Literal[
    "opaque_pointer_obedience",
    "explicit_pointer_lookup",
    "natural_binding_candidate_lookup",
    "registry_gap_detection",
    "conflict_detection",
    "distractor_resistance",
]
CompetencyClaimHorizon = Literal[
    "pointer_obedience_only",
    "exact_lookup_only",
    "natural_binding_not_claimed",
    "obligation_expansion_not_claimed",
    "implementation_not_claimed",
]
OrderPreservationPosture = Literal[
    "order_preserved_for_review",
    "order_normalized_by_declared_rule",
    "order_not_applicable",
]
DuplicatePreservationPosture = Literal[
    "duplicates_preserved_for_review",
    "duplicates_normalized_by_declared_rule",
    "duplicates_not_present",
]
UnknownPointerPosture = Literal[
    "unknown_pointer_not_present",
    "unknown_pointer_abstained",
    "unknown_pointer_registry_gap",
    "unknown_pointer_conflict_requires_review",
]
ConflictPosture = Literal[
    "no_conflict",
    "conflict_requires_review",
    "conflict_blocked_by_registry_gap",
    "conflict_not_applicable",
]
LookupObligationExpansionPosture = Literal[
    "lookup_result_only",
    "named_for_later_expansion_only",
    "expansion_requires_v86_or_later",
    "expansion_blocked_by_ambiguity",
    "expansion_blocked_by_registry_gap",
    "expansion_not_authorized_by_v85",
]
RegistryEntryKind = Literal[
    "operator_entry",
    "class_entry",
    "alias_entry",
    "support_context_entry",
    "registry_gap_marker",
]
RegistryDomain = Literal[
    "operator",
    "object_class",
    "source_class",
    "target_class",
    "modifier",
    "relation_class",
    "obligation_family",
]
RegistryEntryStatus = Literal[
    "current_registry_entry",
    "candidate_for_review_only",
    "deprecated_context",
    "registry_gap",
]
RegistryEntryCurrentness = Literal[
    "current_registry_entry",
    "support_context_only",
    "historical_context_only",
    "stale_or_superseded",
    "unknown_needs_review",
]
RegistryEntryScopePosture = Literal[
    "lookup_review_only",
    "support_context_only",
    "future_family_only",
]
OperatorSemanticsPosture = Literal[
    "action_verb_for_declaration_only",
    "guard_or_route_for_later_authority_review",
    "not_runtime_behavior",
]
ClassSemanticsPosture = Literal[
    "semantic_class_for_lookup_only",
    "not_runtime_class_behavior",
    "not_implementation_target",
]
ObligationFamilyRelationKind = Literal[
    "applies_by_operator",
    "applies_by_object_class",
    "applies_by_target_context",
    "applies_by_modifier",
    "applies_by_negative_cue",
    "applies_by_authority_boundary",
    "conflict_or_exclusion",
    "requires_later_disambiguation",
]
ObligationFamilyActivationPosture = Literal[
    "lookup_result_only",
    "named_for_later_expansion_only",
    "expansion_requires_v86_or_later",
    "expansion_blocked_by_ambiguity",
    "expansion_blocked_by_registry_gap",
    "expansion_not_authorized_by_v85",
]
FutureExpansionPosture = Literal[
    "named_for_later_expansion_only",
    "expansion_requires_future_family",
    "expansion_blocked_by_missing_registry",
    "expansion_not_authorized_by_v85",
]
EvidenceContractRequiredPosture = Literal[
    "evidence_contract_required_later",
    "evidence_contract_not_created_by_v85b",
    "not_applicable",
]
WaiverPosture = Literal[
    "waiver_not_present",
    "waiver_requires_later_review",
    "waiver_not_applicable",
]
LookupFixtureKind = Literal[
    "opaque_pointer_exact_lookup",
    "opaque_pointer_duplicate_preservation",
    "opaque_pointer_unknown_abstain",
    "explicit_semantic_pointer_lookup",
    "explicit_semantic_pointer_registry_gap",
    "distractor_ignored",
    "conflict_requires_review",
]
FixturePosture = Literal[
    "fixture_passes_for_review_only",
    "fixture_records_expected_abstain",
    "fixture_records_registry_gap",
    "fixture_blocked_by_conflict",
    "fixture_future_family_only",
]
ExpectedOrderPosture = Literal[
    "order_preserved",
    "order_normalized_by_rule",
    "order_not_applicable",
]
ExpectedDuplicatePosture = Literal[
    "duplicates_preserved",
    "duplicates_normalized_by_rule",
    "duplicates_absent",
]
ExpectedUnknownPosture = Literal[
    "unknown_absent",
    "unknown_pointer_abstained",
    "unknown_registry_gap",
]
ExpectedConflictPosture = Literal[
    "conflict_absent",
    "conflict_requires_review",
    "conflict_blocked",
]

_V84C_READINESS_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus238/"
    "repo_work_packet_activation_readiness_summary_v238_reference.json"
)
_V84C_HANDOFF_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus238/"
    "repo_post_work_packet_activation_review_handoff_v238_reference.json"
)
_V84C_CLOSEOUT_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus238/"
    "repo_work_packet_activation_family_closeout_alignment_v238_reference.json"
)
_V84_FAMILY_CLOSEOUT_DOC = "docs/DRAFT_ADEU_WORK_PACKET_ACTIVATION_REVIEW_V84_FAMILY_CLOSEOUT_v0.md"
_V85_SELECTOR_DOC = "docs/DRAFT_NEXT_ARC_OPTIONS_v75.md"
_V85_ARCHITECTURE_DOC = "docs/ARCHITECTURE_ADEU_SEMANTIC_DECLARATION_META_LOOP_FAMILY_v0.md"
_V85_MAPPING_DOC = "docs/DRAFT_ADEU_SEMANTIC_DECLARATION_META_LOOP_V85_IMPLEMENTATION_MAPPING_v0.md"
_V85A_MAPPING_DOC = (
    "docs/DRAFT_ADEU_SEMANTIC_DECLARATION_META_LOOP_V85A_IMPLEMENTATION_MAPPING_v0.md"
)
_POST_V84_ROADMAP_DOC = "docs/DRAFT_MULTI_ARC_ROADMAP_POST_V84_v0.md"
_CANONICAL_META_LOOP_SUPPORT_DOC = (
    "docs/support/ARCHITECTURE_ADEU_CANONICAL_SEMANTIC_DECLARATION_META_LOOP_v0.md"
)
_MORPHIC_UX_SUPPORT_DOC = "docs/support/morphic_ux. v2.md"
_V84_COMBINED_DOGFOOD_JSON = (
    "docs/support/arc_series_mapping/"
    "V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_V84_"
    "COMBINED_DOGFOOD_TEST_v0.json"
)
_V85A_SOURCE_INDEX_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus239/"
    "repo_semantic_declaration_source_index_v239_reference.json"
)
_V85A_REQUEST_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus239/"
    "repo_turn_semantic_declaration_request_v239_reference.json"
)
_V85A_GUARDRAIL_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus239/"
    "repo_semantic_declaration_non_authority_guardrail_v239_reference.json"
)
_V85B_LOCK_DOC = "docs/LOCKED_CONTINUATION_vNEXT_PLUS240.md"
_V85B_MAPPING_DOC = (
    "docs/DRAFT_ADEU_SEMANTIC_DECLARATION_META_LOOP_V85B_IMPLEMENTATION_MAPPING_v0.md"
)
_OPERATOR_TURN_SOURCE = "operator-turn:v85a:semantic-declaration-meta-loop-request"
_OPAQUE_POINTER_CONTEXT = "opaque-pointer:v85a:M-42-context"

_ELIGIBLE_SOURCE_ROLES = {
    "v84_readiness_summary_source",
    "v84_handoff_source",
    "v84_closeout_source",
}
_CURRENT_TASK_SOURCE_ROLES = {
    "operator_turn_source",
    "repo_task_context_source",
    "natural_task_context_source",
    "code_context_source",
}
_SUPPORT_ONLY_SOURCE_ROLES = {
    "canonical_meta_loop_support_source",
    "combined_dogfood_context",
    "direct_oai_support_context",
    "meta_orchestrator_support_context",
    "morphic_ux_support_context",
    "post_v84_roadmap_source",
    "support_process_context",
}
_REQUIRED_COMPETENCIES = {
    "artifact_shape_obedience",
    "bounded_local_judgment",
    "declared_uncertainty_routing",
    "duplicate_preservation",
    "no_unauthorized_transition",
    "order_preservation",
    "pointer_obedience",
    "stop_at_schema_boundary",
    "unknown_pointer_abstention",
}
_REQUIRED_FORBIDDEN_DECLARATION_ACTIONS = {
    "create_canonical_lookup_index",
    "create_declaration_summary",
    "create_obligation_family_registry",
    "create_operator_class_registry",
    "create_pointer_lookup_fixture",
    "create_post_declaration_handoff",
    "emit_audit_report",
    "emit_edge_probe_plan",
    "emit_evidence_contract",
    "emit_reviewer_taskpack",
    "expand_obligations",
    "run_closeout_transition_table",
}
_REQUIRED_FORBIDDEN_DOWNSTREAM_ACTIONS = {
    "activate_work_packet",
    "amend_recursive_policy",
    "authorize_product",
    "commit_changes",
    "create_graph_memory_authority",
    "create_implementation_lock",
    "edit_code",
    "execute_work_packet",
    "invoke_tool_for_effect",
    "merge_or_release",
    "mutate_target",
    "open_pr",
    "run_command",
    "select_v86",
}


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


def _reject_v85_authority_claim(value: str, *, field_name: str) -> str:
    lowered = value.lower()
    forbidden_patterns = [
        r"\bcanonical lookup (?:created|performed)\b",
        r"\bcode (?:edited|implemented|written)\b",
        r"\bcommand (?:executed|run)\b",
        r"\bdeclaration authority granted\b",
        r"\bdeterministic transition table (?:created|run)\b",
        r"\bevidence contract (?:created|emitted)\b",
        r"\bgraph[- ]memory authority (?:created|granted)\b",
        r"\bimplementation (?:authorized|executed|performed)\b",
        r"\bimplementation lock (?:created|opened)\b",
        r"\bobligation(?:s)? (?:expanded|executed)\b",
        r"\boperator[/ -]?class registry (?:created|opened)\b",
        r"\bpointer lookup fixture (?:created|executed)\b",
        r"\bproduct (?:authorized|launched)\b",
        r"\bpr (?:created|opened)\b",
        r"\brelease(?:d)? (?:authority|truth|version)\b",
        r"\bruntime (?:authorized|transitioned)\b",
        r"\bselected declaration\b",
        r"\btarget (?:mutated|changed|updated)\b",
        r"\btool (?:invoked|executed)\b",
        r"\bv86 (?:selected|selection)\b",
        r"\bwork[- ]packet (?:activated|executed)\b",
    ]

    def is_negated(match: re.Match[str]) -> bool:
        prefix = lowered[max(0, match.start() - 32) : match.start()]
        suffix = lowered[match.end() : min(len(lowered), match.end() + 32)]
        return bool(
            re.search(
                r"(?:\bno\b|\bnot\b|\bwithout\b|\bmust not\b|\bdoes not\b|\bno[- ])\W*$",
                prefix,
            )
            or re.search(
                r"\b(?:is|are|was|were|remains?|stays?)?\W*"
                r"(?:forbidden|not authorized|not selected|not performed|requires later)\b",
                suffix,
            )
        )

    for pattern in forbidden_patterns:
        for match in re.finditer(pattern, lowered):
            if not is_negated(match):
                raise ValueError(f"{field_name} may not carry V85 declaration authority")
    return value


class RepoSemanticActWitnessRow(_CartographyBase):
    witness_ref: str
    semantic_declaration_session_ref: str
    source_refs: list[str] = Field(min_length=1)
    witnessed_element: WitnessedElement
    witness_strength: WitnessStrength
    witness_currentness: WitnessCurrentness
    limitation_note: str

    @model_validator(mode="after")
    def _validate_witness(self) -> "RepoSemanticActWitnessRow":
        _non_empty(self.witness_ref, field_name="witness_ref")
        _non_empty(
            self.semantic_declaration_session_ref,
            field_name="semantic_declaration_session_ref",
        )
        _validate_repo_refs(self.source_refs, field_name="source_refs")
        _reject_v85_authority_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("witness", "review"),
            ),
            field_name="limitation_note",
        )
        if self.witness_strength == "direct" and self.witness_currentness not in {
            "current_turn_witness",
            "current_repo_context",
        }:
            raise ValueError("direct semantic act witnesses must be current")
        if self.witness_strength == "support_only" and self.witness_currentness not in {
            "support_context_only",
            "stale_or_superseded",
        }:
            raise ValueError("support-only witnesses must stay support context")
        return self


class RepoSemanticDeclarationNegativeCueRow(_CartographyBase):
    negative_cue_ref: str
    semantic_declaration_session_ref: str
    source_refs: list[str] = Field(min_length=1)
    cue_kind: NegativeCueKind
    effect_on_declaration: NegativeCueEffect
    limitation_note: str

    @model_validator(mode="after")
    def _validate_negative_cue(self) -> "RepoSemanticDeclarationNegativeCueRow":
        _non_empty(self.negative_cue_ref, field_name="negative_cue_ref")
        _non_empty(
            self.semantic_declaration_session_ref,
            field_name="semantic_declaration_session_ref",
        )
        _validate_repo_refs(self.source_refs, field_name="source_refs")
        if self.cue_kind in {
            "asks_to_implement_now",
            "asks_to_execute_now",
            "asks_to_select_next_family",
            "asks_to_authorize_runtime",
            "asks_to_productize",
            "asks_to_release",
            "asks_to_expand_obligations_now",
            "asks_to_skip_lookup",
            "asks_to_invent_class",
        } and self.effect_on_declaration not in {
            "blocks_eligibility",
            "routes_to_guardrail",
            "routes_to_future_family_only",
        }:
            raise ValueError("authority-shaped negative cues must route to guardrail or blocker")
        _reject_v85_authority_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("cue", "review"),
            ),
            field_name="limitation_note",
        )
        return self


class RepoResidentModelCompetencyRow(_CartographyBase):
    competency_ref: str
    semantic_declaration_session_ref: str
    competency_kind: ResidentModelCompetencyKind
    required_posture: CompetencyRequiredPosture
    evidence_or_fixture_refs: list[str] = Field(default_factory=list)
    failure_routing_posture: CompetencyFailureRoutingPosture
    non_authority_guardrail_refs: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_competency(self) -> "RepoResidentModelCompetencyRow":
        _non_empty(self.competency_ref, field_name="competency_ref")
        _non_empty(
            self.semantic_declaration_session_ref,
            field_name="semantic_declaration_session_ref",
        )
        _validate_sorted_refs(
            self.evidence_or_fixture_refs,
            field_name="evidence_or_fixture_refs",
        )
        _validate_sorted_refs(
            self.non_authority_guardrail_refs,
            field_name="non_authority_guardrail_refs",
        )
        if (
            self.competency_kind == "no_unauthorized_transition"
            and self.failure_routing_posture != "route_to_guardrail"
        ):
            raise ValueError("unauthorized transition failures must route to guardrail")
        if (
            self.competency_kind == "unknown_pointer_abstention"
            and self.failure_routing_posture not in {"route_to_abstain", "route_to_registry_gap"}
        ):
            raise ValueError("unknown pointer failures must route to abstain or registry gap")
        return self


class RepoSemanticDeclarationSourceRow(_CartographyBase):
    source_ref: str
    source_kind: CandidateSourceKind
    authority_layer: CandidateAuthorityLayer
    source_status: SourceStatus
    source_presence_posture: CandidateSourcePresencePosture
    semantic_declaration_source_role: SemanticDeclarationSourceRole
    source_currentness: SemanticDeclarationSourceCurrentness
    declaration_authority_posture: DeclarationAuthorityPosture
    loop_authority_posture: LoopAuthorityPosture
    odeu_lane: OdeuLane
    limitation_note: str

    @model_validator(mode="after")
    def _validate_source_row(self) -> "RepoSemanticDeclarationSourceRow":
        _source_path(self.source_ref)
        _reject_v85_authority_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("review", "no implementation"),
            ),
            field_name="limitation_note",
        )
        if self.semantic_declaration_source_role == "explicit_absence_marker":
            if self.source_currentness != "explicit_absence_marker":
                raise ValueError("absence source rows require explicit absence currentness")
            if self.source_presence_posture == "present":
                raise ValueError("absence source rows may not be present")
        if self.semantic_declaration_source_role in _SUPPORT_ONLY_SOURCE_ROLES:
            if self.declaration_authority_posture != "support_context_not_authority":
                raise ValueError("support context rows cannot carry declaration authority")
            if self.source_currentness == "current_concrete_source":
                raise ValueError("support context rows cannot be concrete current sources")
        if self.semantic_declaration_source_role in _ELIGIBLE_SOURCE_ROLES:
            if self.source_currentness != "current_concrete_source":
                raise ValueError("released V84-C source rows require current concrete source")
            if self.source_presence_posture != "present":
                raise ValueError("released V84-C source rows must be present")
            if self.declaration_authority_posture != "source_for_review_only":
                raise ValueError("released V84-C rows are review-only sources")
        if self.semantic_declaration_source_role == "operator_turn_source":
            if self.source_kind != "operator_turn":
                raise ValueError("operator turn sources must use operator_turn source kind")
            if self.source_currentness != "current_operator_turn":
                raise ValueError("operator turn sources must be current operator turns")
        if self.semantic_declaration_source_role == "generated_declaration_candidate_source":
            if self.declaration_authority_posture != "candidate_only":
                raise ValueError("generated declaration sources must remain candidate-only")
        return self


class RepoSemanticDeclarationSourceIndex(_CartographyBase):
    schema: Literal[REPO_SEMANTIC_DECLARATION_SOURCE_INDEX_SCHEMA]
    semantic_declaration_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    source_rows: list[RepoSemanticDeclarationSourceRow] = Field(min_length=1)
    semantic_act_witness_rows: list[RepoSemanticActWitnessRow] = Field(min_length=1)
    negative_cue_rows: list[RepoSemanticDeclarationNegativeCueRow] = Field(default_factory=list)
    resident_model_competency_rows: list[RepoResidentModelCompetencyRow] = Field(min_length=1)
    source_index_summary: str

    @model_validator(mode="after")
    def _validate_source_index(self) -> "RepoSemanticDeclarationSourceIndex":
        _non_empty(
            self.semantic_declaration_source_index_id,
            field_name="semantic_declaration_source_index_id",
        )
        _non_empty(self.review_id, field_name="review_id")
        _non_empty(self.snapshot_id, field_name="snapshot_id")
        _non_empty(self.source_set_id, field_name="source_set_id")
        _sorted_unique_by_ref(self.source_rows, attr="source_ref", field_name="source_rows")
        _sorted_unique_by_ref(
            self.semantic_act_witness_rows,
            attr="witness_ref",
            field_name="semantic_act_witness_rows",
        )
        _sorted_unique_by_ref(
            self.negative_cue_rows,
            attr="negative_cue_ref",
            field_name="negative_cue_rows",
        )
        _sorted_unique_by_ref(
            self.resident_model_competency_rows,
            attr="competency_ref",
            field_name="resident_model_competency_rows",
        )
        known_sources = {row.source_ref for row in self.source_rows}
        for witness_row in self.semantic_act_witness_rows:
            if any(ref not in known_sources for ref in witness_row.source_refs):
                raise ValueError("semantic act witness refs must be indexed sources")
        for cue_row in self.negative_cue_rows:
            if any(ref not in known_sources for ref in cue_row.source_refs):
                raise ValueError("negative cue source refs must be indexed sources")
        required = _REQUIRED_COMPETENCIES
        observed = {row.competency_kind for row in self.resident_model_competency_rows}
        missing = sorted(required.difference(observed))
        if missing:
            raise ValueError("resident model competencies missing: " + ", ".join(missing))
        _reject_v85_authority_claim(
            _require_terms(
                self.source_index_summary,
                field_name="source_index_summary",
                terms=("source", "review", "no implementation"),
            ),
            field_name="source_index_summary",
        )
        _assert_surface_id(
            surface_name="repo_semantic_declaration_source_index",
            schema=REPO_SEMANTIC_DECLARATION_SOURCE_INDEX_SCHEMA,
            payload=self.model_dump(mode="json"),
            id_key="semantic_declaration_source_index_id",
            actual=self.semantic_declaration_source_index_id,
        )
        return self


class RepoDeclaredSemanticActRow(_CartographyBase):
    semantic_act_ref: str
    semantic_declaration_session_ref: str
    operator: str
    object_class: str
    source_class: str | None = None
    target_class: str | None = None
    target_context_refs: list[str] = Field(default_factory=list)
    modifiers: list[str] = Field(default_factory=list)
    binding_basis_refs: list[str] = Field(min_length=1)
    source_witness_refs: list[str] = Field(min_length=1)
    ambiguity_posture: AmbiguityPosture
    registry_gap_posture: RegistryGapPosture
    declaration_candidate_status: DeclarationCandidateStatus
    declaration_selection_status: DeclarationSelectionStatus
    canonical_status: CanonicalStatus
    limitation_note: str

    @model_validator(mode="after")
    def _validate_act_row(self) -> "RepoDeclaredSemanticActRow":
        for attr in (
            "semantic_act_ref",
            "semantic_declaration_session_ref",
            "operator",
            "object_class",
        ):
            _non_empty(getattr(self, attr), field_name=attr)
        _validate_sorted_refs(self.target_context_refs, field_name="target_context_refs")
        _validate_sorted_refs(self.modifiers, field_name="modifiers")
        _validate_sorted_refs(self.binding_basis_refs, field_name="binding_basis_refs")
        _validate_sorted_refs(self.source_witness_refs, field_name="source_witness_refs")
        if not set(self.binding_basis_refs).issubset(self.source_witness_refs):
            raise ValueError("binding basis refs must be a subset of source witness refs")
        if self.declaration_selection_status != "not_selected_by_v85a":
            raise ValueError("V85-A declaration act rows cannot be selected declarations")
        if self.ambiguity_posture != "not_ambiguous" and self.declaration_candidate_status not in {
            "ambiguous_candidate",
            "support_context_only_candidate",
        }:
            raise ValueError("ambiguous acts must remain ambiguous candidates")
        if (
            self.declaration_candidate_status == "ambiguous_candidate"
            and self.ambiguity_posture == "not_ambiguous"
        ):
            raise ValueError("ambiguous candidates must carry an ambiguous posture")
        if (
            self.declaration_candidate_status == "registry_gap_candidate"
            and self.registry_gap_posture == "no_registry_gap_claimed"
        ):
            raise ValueError("registry-gap candidates must carry registry-gap posture")
        if self.registry_gap_posture != "no_registry_gap_claimed":
            if self.canonical_status != "unknown_class_registry_gap":
                raise ValueError("registry gap acts must use unknown_class_registry_gap")
            if self.declaration_candidate_status != "registry_gap_candidate":
                raise ValueError("registry gap acts must remain registry-gap candidates")
        if (
            self.canonical_status == "canonical_pointer_claimed_for_later_lookup"
            and self.registry_gap_posture != "no_registry_gap_claimed"
        ):
            raise ValueError("unknown class cannot be repaired into a canonical pointer")
        _reject_v85_authority_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("candidate", "review"),
            ),
            field_name="limitation_note",
        )
        return self


class RepoTurnSemanticDeclarationRequestRow(_CartographyBase):
    declaration_request_ref: str
    semantic_declaration_session_ref: str
    candidate_ref: str
    turn_ref: str
    source_refs: list[str] = Field(min_length=1)
    source_witness_refs: list[str] = Field(min_length=1)
    operator_turn_refs: list[str] = Field(default_factory=list)
    repo_context_refs: list[str] = Field(default_factory=list)
    declared_semantic_act_rows: list[RepoDeclaredSemanticActRow] = Field(min_length=1)
    semantic_act_witness_rows: list[RepoSemanticActWitnessRow] = Field(min_length=1)
    negative_cue_rows: list[RepoSemanticDeclarationNegativeCueRow] = Field(default_factory=list)
    resident_model_competency_rows: list[RepoResidentModelCompetencyRow] = Field(min_length=1)
    declaration_horizon: DeclarationHorizon
    requested_declaration_review_horizon: RequestedDeclarationReviewHorizon
    binding_posture: DeclarationBindingPosture
    binding_resolution_posture: BindingResolutionPosture
    binding_basis_refs: list[str] = Field(min_length=1)
    negative_cue_refs: list[str] = Field(default_factory=list)
    uncertainty_slot_refs: list[str] = Field(default_factory=list)
    canonical_lookup_required_posture: CanonicalLookupRequiredPosture
    declaration_candidate_status: DeclarationCandidateStatus
    canonical_lookup_status: CanonicalLookupStatus
    declaration_selection_status: DeclarationSelectionStatus
    declaration_recordability_posture: DeclarationRecordabilityPosture
    declaration_review_eligibility_posture: DeclarationReviewEligibilityPosture
    guardrail_refs: list[str] = Field(min_length=1)
    non_authority_posture: DeclarationNonAuthorityPosture
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_request_row(self) -> "RepoTurnSemanticDeclarationRequestRow":
        for attr in (
            "declaration_request_ref",
            "semantic_declaration_session_ref",
            "candidate_ref",
            "turn_ref",
        ):
            _non_empty(getattr(self, attr), field_name=attr)
        for attr in ("source_refs", "operator_turn_refs", "repo_context_refs"):
            _validate_repo_refs(getattr(self, attr), field_name=attr)
        for attr in (
            "source_witness_refs",
            "binding_basis_refs",
            "negative_cue_refs",
            "uncertainty_slot_refs",
            "guardrail_refs",
            "odeu_lanes",
        ):
            _validate_sorted_refs(getattr(self, attr), field_name=attr)
        _sorted_unique_by_ref(
            self.declared_semantic_act_rows,
            attr="semantic_act_ref",
            field_name="declared_semantic_act_rows",
        )
        _sorted_unique_by_ref(
            self.semantic_act_witness_rows,
            attr="witness_ref",
            field_name="semantic_act_witness_rows",
        )
        _sorted_unique_by_ref(
            self.negative_cue_rows,
            attr="negative_cue_ref",
            field_name="negative_cue_rows",
        )
        _sorted_unique_by_ref(
            self.resident_model_competency_rows,
            attr="competency_ref",
            field_name="resident_model_competency_rows",
        )
        for act in self.declared_semantic_act_rows:
            if act.semantic_declaration_session_ref != self.semantic_declaration_session_ref:
                raise ValueError("declared acts must share semantic declaration session")
        for witness in self.semantic_act_witness_rows:
            if witness.semantic_declaration_session_ref != self.semantic_declaration_session_ref:
                raise ValueError("semantic act witnesses must share declaration session")
        for cue in self.negative_cue_rows:
            if cue.semantic_declaration_session_ref != self.semantic_declaration_session_ref:
                raise ValueError("negative cue rows must share declaration session")
        for competency in self.resident_model_competency_rows:
            if competency.semantic_declaration_session_ref != self.semantic_declaration_session_ref:
                raise ValueError("resident model competencies must share declaration session")
        observed_competencies = {row.competency_kind for row in self.resident_model_competency_rows}
        missing_competencies = sorted(_REQUIRED_COMPETENCIES.difference(observed_competencies))
        if missing_competencies:
            raise ValueError(
                "resident model competency rows missing: " + ", ".join(missing_competencies)
            )
        witness_refs = {row.witness_ref for row in self.semantic_act_witness_rows}
        if any(ref not in witness_refs for ref in self.source_witness_refs):
            raise ValueError("source_witness_refs must resolve to semantic act witnesses")
        if any(ref not in witness_refs for ref in self.binding_basis_refs):
            raise ValueError("binding_basis_refs must resolve to semantic act witnesses")
        if not set(self.binding_basis_refs).issubset(self.source_witness_refs):
            raise ValueError("binding basis refs must be a subset of source witness refs")
        cue_refs = {row.negative_cue_ref for row in self.negative_cue_rows}
        if any(ref not in cue_refs for ref in self.negative_cue_refs):
            raise ValueError("negative_cue_refs must resolve to negative cue rows")
        _reject_v85_authority_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("declaration", "review", "no implementation"),
            ),
            field_name="limitation_note",
        )
        if self.declaration_selection_status not in {
            "not_selected_by_v85a",
            "ambiguous_not_selected",
            "abstained_not_selected",
            "registry_gap_not_selected",
            "blocked_not_selected",
        }:
            raise ValueError("V85-A cannot select canonical declarations")
        if self.canonical_lookup_status not in {
            "lookup_not_selected_by_v85a",
            "lookup_required_later",
            "lookup_blocked_by_missing_pointer",
            "lookup_blocked_by_registry_gap",
            "lookup_not_applicable",
        }:
            raise ValueError("V85-A cannot create canonical lookup results")
        if (
            self.declaration_review_eligibility_posture
            == "eligible_for_semantic_declaration_review"
        ):
            if self.declaration_recordability_posture in {
                "recordable_from_support_context_only",
                "recordable_with_absence_markers",
                "not_recordable_missing_source",
            }:
                raise ValueError("support or absence-only declarations cannot be eligible")
            if self.binding_resolution_posture != "selected_for_later_lookup_review":
                raise ValueError("eligible declarations require selected-for-lookup posture")
            if self.declaration_candidate_status != "candidate_recorded_for_review":
                raise ValueError("eligible declarations must remain recorded candidates")
            if self.binding_posture != "selected":
                raise ValueError("eligible declarations require selected binding posture")
            if self.canonical_lookup_status not in {
                "lookup_not_selected_by_v85a",
                "lookup_required_later",
            }:
                raise ValueError("eligible declarations cannot carry lookup blockers")
            direct_witnesses = [
                row
                for row in self.semantic_act_witness_rows
                if row.witness_ref in self.source_witness_refs
                and row.witness_strength == "direct"
                and row.witness_currentness in {"current_turn_witness", "current_repo_context"}
            ]
            if not direct_witnesses:
                raise ValueError("eligible semantic declaration requires direct/current witnesses")
            if any(
                act.ambiguity_posture != "not_ambiguous" for act in self.declared_semantic_act_rows
            ):
                raise ValueError("ambiguous declarations cannot be eligible")
            if any(
                act.registry_gap_posture != "no_registry_gap_claimed"
                for act in self.declared_semantic_act_rows
            ):
                raise ValueError("registry-gap declarations cannot be eligible")
            blocking_cues = [
                cue
                for cue in self.negative_cue_rows
                if cue.effect_on_declaration == "blocks_eligibility"
            ]
            if blocking_cues:
                raise ValueError("negative cue blockers cannot be eligible")
        act_statuses = {act.declaration_candidate_status for act in self.declared_semantic_act_rows}
        if (
            self.declaration_candidate_status == "candidate_recorded_for_review"
            and "candidate_recorded_for_review" not in act_statuses
        ):
            raise ValueError("recorded-candidate request requires at least one recorded act")
        if (
            self.declaration_candidate_status == "ambiguous_candidate"
            and "ambiguous_candidate" not in act_statuses
        ):
            raise ValueError("ambiguous request requires at least one ambiguous act")
        if (
            self.declaration_candidate_status == "registry_gap_candidate"
            and "registry_gap_candidate" not in act_statuses
        ):
            raise ValueError("registry-gap request requires at least one registry-gap act")
        if self.binding_resolution_posture == "abstain_declared":
            if self.declaration_candidate_status != "abstain_candidate":
                raise ValueError("abstain declarations must remain abstain candidates")
            if self.canonical_lookup_required_posture != "lookup_not_applicable":
                raise ValueError("abstain declarations cannot require lookup")
        if self.binding_resolution_posture == "registry_gap_declared":
            if self.canonical_lookup_required_posture != "lookup_blocked_by_registry_gap":
                raise ValueError("registry-gap declarations must block lookup")
        return self


class RepoTurnSemanticDeclarationRequest(_CartographyBase):
    schema: Literal[REPO_TURN_SEMANTIC_DECLARATION_REQUEST_SCHEMA]
    turn_semantic_declaration_request_id: str
    semantic_declaration_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    declaration_request_rows: list[RepoTurnSemanticDeclarationRequestRow] = Field(min_length=1)
    declaration_review_summary: str

    @model_validator(mode="after")
    def _validate_request_surface(self) -> "RepoTurnSemanticDeclarationRequest":
        _non_empty(
            self.turn_semantic_declaration_request_id,
            field_name="turn_semantic_declaration_request_id",
        )
        _non_empty(
            self.semantic_declaration_source_index_id,
            field_name="semantic_declaration_source_index_id",
        )
        _non_empty(self.review_id, field_name="review_id")
        _non_empty(self.snapshot_id, field_name="snapshot_id")
        _non_empty(self.source_set_id, field_name="source_set_id")
        _sorted_unique_by_ref(
            self.declaration_request_rows,
            attr="declaration_request_ref",
            field_name="declaration_request_rows",
        )
        _reject_v85_authority_claim(
            _require_terms(
                self.declaration_review_summary,
                field_name="declaration_review_summary",
                terms=("semantic declaration", "review", "no implementation"),
            ),
            field_name="declaration_review_summary",
        )
        _assert_surface_id(
            surface_name="repo_turn_semantic_declaration_request",
            schema=REPO_TURN_SEMANTIC_DECLARATION_REQUEST_SCHEMA,
            payload=self.model_dump(mode="json"),
            id_key="turn_semantic_declaration_request_id",
            actual=self.turn_semantic_declaration_request_id,
        )
        return self


class RepoSemanticDeclarationNonAuthorityGuardrailRow(_CartographyBase):
    guardrail_ref: str
    semantic_declaration_session_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    declaration_request_refs: list[str] = Field(min_length=1)
    forbidden_declaration_actions: list[ForbiddenDeclarationAction] = Field(min_length=1)
    forbidden_downstream_actions: list[ForbiddenDownstreamAction] = Field(min_length=1)
    required_later_authority_refs: list[str] = Field(default_factory=list)
    declaration_non_authority_posture: DeclarationNonAuthorityPosture
    obligation_expansion_posture: ObligationExpansionPosture
    implementation_posture: ImplementationPosture
    runtime_transition_posture: RuntimeTransitionPosture
    future_family_selection_posture: FutureFamilySelectionPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_guardrail_row(self) -> "RepoSemanticDeclarationNonAuthorityGuardrailRow":
        for attr in ("guardrail_ref", "semantic_declaration_session_ref", "candidate_ref"):
            _non_empty(getattr(self, attr), field_name=attr)
        _validate_repo_refs(self.source_refs, field_name="source_refs")
        for attr in (
            "declaration_request_refs",
            "forbidden_declaration_actions",
            "forbidden_downstream_actions",
            "required_later_authority_refs",
        ):
            _validate_sorted_refs(getattr(self, attr), field_name=attr)
        missing_declaration = _REQUIRED_FORBIDDEN_DECLARATION_ACTIONS.difference(
            self.forbidden_declaration_actions
        )
        if missing_declaration:
            raise ValueError(
                "guardrails must forbid required declaration actions: "
                + ", ".join(sorted(missing_declaration))
            )
        missing_downstream = _REQUIRED_FORBIDDEN_DOWNSTREAM_ACTIONS.difference(
            self.forbidden_downstream_actions
        )
        if missing_downstream:
            raise ValueError(
                "guardrails must forbid required downstream actions: "
                + ", ".join(sorted(missing_downstream))
            )
        if self.declaration_non_authority_posture != "no_declaration_authority_granted_by_v85":
            raise ValueError("V85-A guardrails cannot grant declaration authority")
        if self.obligation_expansion_posture != "no_obligation_expansion_performed_by_v85a":
            raise ValueError("V85-A guardrails cannot expand obligations")
        if self.implementation_posture != "no_implementation_performed_by_v85a":
            raise ValueError("V85-A guardrails cannot perform implementation")
        if self.runtime_transition_posture != "no_runtime_transition_performed_by_v85a":
            raise ValueError("V85-A guardrails cannot transition runtime")
        if self.future_family_selection_posture != "no_future_family_selected_by_v85a":
            raise ValueError("V85-A guardrails cannot select V86")
        _reject_v85_authority_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("guardrail", "no implementation", "no obligation"),
            ),
            field_name="limitation_note",
        )
        return self


class RepoSemanticDeclarationNonAuthorityGuardrail(_CartographyBase):
    schema: Literal[REPO_SEMANTIC_DECLARATION_NON_AUTHORITY_GUARDRAIL_SCHEMA]
    semantic_declaration_non_authority_guardrail_id: str
    turn_semantic_declaration_request_id: str
    semantic_declaration_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    guardrail_rows: list[RepoSemanticDeclarationNonAuthorityGuardrailRow] = Field(min_length=1)
    guardrail_summary: str

    @model_validator(mode="after")
    def _validate_guardrail_surface(self) -> "RepoSemanticDeclarationNonAuthorityGuardrail":
        _non_empty(
            self.semantic_declaration_non_authority_guardrail_id,
            field_name="semantic_declaration_non_authority_guardrail_id",
        )
        _non_empty(
            self.turn_semantic_declaration_request_id,
            field_name="turn_semantic_declaration_request_id",
        )
        _non_empty(
            self.semantic_declaration_source_index_id,
            field_name="semantic_declaration_source_index_id",
        )
        _non_empty(self.review_id, field_name="review_id")
        _non_empty(self.snapshot_id, field_name="snapshot_id")
        _non_empty(self.source_set_id, field_name="source_set_id")
        _sorted_unique_by_ref(
            self.guardrail_rows,
            attr="guardrail_ref",
            field_name="guardrail_rows",
        )
        _reject_v85_authority_claim(
            _require_terms(
                self.guardrail_summary,
                field_name="guardrail_summary",
                terms=("guardrail", "no implementation", "no obligation"),
            ),
            field_name="guardrail_summary",
        )
        _assert_surface_id(
            surface_name="repo_semantic_declaration_non_authority_guardrail",
            schema=REPO_SEMANTIC_DECLARATION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            payload=self.model_dump(mode="json"),
            id_key="semantic_declaration_non_authority_guardrail_id",
            actual=self.semantic_declaration_non_authority_guardrail_id,
        )
        return self


def _v84c_released_bundle(
    repo_root: Path | None = None,
) -> tuple[
    RepoWorkPacketActivationReadinessSummary,
    RepoPostWorkPacketActivationReviewHandoff,
    RepoWorkPacketActivationFamilyCloseoutAlignment,
]:
    bundle = derive_v84c_work_packet_activation_closeout_bundle(repo_root=repo_root)
    return bundle[-3], bundle[-2], bundle[-1]


def _v85_source_rows() -> list[dict[str, object]]:
    rows = [
        {
            "source_ref": _V84C_READINESS_FIXTURE,
            "source_kind": "fixture_file",
            "authority_layer": "fixture",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "semantic_declaration_source_role": "v84_readiness_summary_source",
            "source_currentness": "current_concrete_source",
            "declaration_authority_posture": "source_for_review_only",
            "loop_authority_posture": "no_loop_authority_granted",
            "odeu_lane": "epistemic",
            "limitation_note": (
                "Released V84-C readiness source for semantic declaration review; "
                "no implementation."
            ),
        },
        {
            "source_ref": _V84C_HANDOFF_FIXTURE,
            "source_kind": "fixture_file",
            "authority_layer": "fixture",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "semantic_declaration_source_role": "v84_handoff_source",
            "source_currentness": "current_concrete_source",
            "declaration_authority_posture": "source_for_review_only",
            "loop_authority_posture": "no_loop_authority_granted",
            "odeu_lane": "epistemic",
            "limitation_note": (
                "Released V84-C handoff source for semantic declaration review; no implementation."
            ),
        },
        {
            "source_ref": _V84C_CLOSEOUT_FIXTURE,
            "source_kind": "fixture_file",
            "authority_layer": "fixture",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "semantic_declaration_source_role": "v84_closeout_source",
            "source_currentness": "current_concrete_source",
            "declaration_authority_posture": "source_for_review_only",
            "loop_authority_posture": "no_loop_authority_granted",
            "odeu_lane": "epistemic",
            "limitation_note": (
                "Released V84 family closeout source for semantic declaration review; "
                "no implementation."
            ),
        },
        {
            "source_ref": _OPERATOR_TURN_SOURCE,
            "source_kind": "operator_turn",
            "authority_layer": "support",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "semantic_declaration_source_role": "operator_turn_source",
            "source_currentness": "current_operator_turn",
            "declaration_authority_posture": "source_for_review_only",
            "loop_authority_posture": "model_output_candidate_only",
            "odeu_lane": "ontological",
            "limitation_note": (
                "Operator turn asks for V85-A implementation as semantic declaration "
                "review pressure; no implementation authority."
            ),
        },
        {
            "source_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS239.md",
            "source_kind": "planning_doc",
            "authority_layer": "lock",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "semantic_declaration_source_role": "repo_task_context_source",
            "source_currentness": "current_concrete_source",
            "declaration_authority_posture": "source_for_review_only",
            "loop_authority_posture": "transition_requires_later_table",
            "odeu_lane": "deontic",
            "limitation_note": (
                "V85-A lock is repo task context for declaration review; no implementation "
                "authority beyond this bounded slice."
            ),
        },
        {
            "source_ref": _POST_V84_ROADMAP_DOC,
            "source_kind": "planning_doc",
            "authority_layer": "planning",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "semantic_declaration_source_role": "post_v84_roadmap_source",
            "source_currentness": "support_context_only",
            "declaration_authority_posture": "support_context_not_authority",
            "loop_authority_posture": "no_loop_authority_granted",
            "odeu_lane": "utility",
            "limitation_note": (
                "Post-V84 roadmap contextualizes semantic declaration review; no implementation."
            ),
        },
        {
            "source_ref": _CANONICAL_META_LOOP_SUPPORT_DOC,
            "source_kind": "support_doc",
            "authority_layer": "support",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "semantic_declaration_source_role": "canonical_meta_loop_support_source",
            "source_currentness": "support_context_only",
            "declaration_authority_posture": "support_context_not_authority",
            "loop_authority_posture": "loop_sequence_meaning_owned_by_harness",
            "odeu_lane": "ontological",
            "limitation_note": (
                "Canonical meta-loop support remains doctrine context for review; "
                "no implementation."
            ),
        },
        {
            "source_ref": _V85A_MAPPING_DOC,
            "source_kind": "planning_doc",
            "authority_layer": "support",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "semantic_declaration_source_role": "support_process_context",
            "source_currentness": "support_context_only",
            "declaration_authority_posture": "support_context_not_authority",
            "loop_authority_posture": "no_loop_authority_granted",
            "odeu_lane": "utility",
            "limitation_note": (
                "V85-A support mapping contextualizes declaration review; no implementation."
            ),
        },
        {
            "source_ref": _V85_SELECTOR_DOC,
            "source_kind": "planning_doc",
            "authority_layer": "planning",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "semantic_declaration_source_role": "support_process_context",
            "source_currentness": "support_context_only",
            "declaration_authority_posture": "support_context_not_authority",
            "loop_authority_posture": "no_loop_authority_granted",
            "odeu_lane": "utility",
            "limitation_note": (
                "V85 selector contextualizes declaration review sequencing; no implementation."
            ),
        },
        {
            "source_ref": _MORPHIC_UX_SUPPORT_DOC,
            "source_kind": "support_doc",
            "authority_layer": "support",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "semantic_declaration_source_role": "morphic_ux_support_context",
            "source_currentness": "support_context_only",
            "declaration_authority_posture": "support_context_not_authority",
            "loop_authority_posture": "no_loop_authority_granted",
            "odeu_lane": "utility",
            "limitation_note": (
                "Morphic UX support is semantic declaration review context only; no implementation."
            ),
        },
        {
            "source_ref": _V84_COMBINED_DOGFOOD_JSON,
            "source_kind": "support_doc",
            "authority_layer": "support",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "semantic_declaration_source_role": "combined_dogfood_context",
            "source_currentness": "support_context_only",
            "declaration_authority_posture": "support_context_not_authority",
            "loop_authority_posture": "no_loop_authority_granted",
            "odeu_lane": "epistemic",
            "limitation_note": (
                "Combined dogfood is context for semantic declaration review; no implementation."
            ),
        },
        {
            "source_ref": _OPAQUE_POINTER_CONTEXT,
            "source_kind": "model_output",
            "authority_layer": "support",
            "source_status": "integrated_shaping_source",
            "source_presence_posture": "present",
            "semantic_declaration_source_role": "opaque_pointer_context",
            "source_currentness": "support_context_only",
            "declaration_authority_posture": "support_context_not_authority",
            "loop_authority_posture": "model_output_candidate_only",
            "odeu_lane": "epistemic",
            "limitation_note": (
                "Opaque pointer context may test obedience for review; no implementation."
            ),
        },
    ]
    return sorted(rows, key=lambda row: str(row["source_ref"]))


def _base_witness_rows() -> list[dict[str, object]]:
    session = "semantic-declaration-session:v85a:intent-to-declaration-office"
    return [
        {
            "witness_ref": "witness:v85a:direct:object-class",
            "semantic_declaration_session_ref": session,
            "source_refs": [_OPERATOR_TURN_SOURCE],
            "witnessed_element": "object_class",
            "witness_strength": "direct",
            "witness_currentness": "current_turn_witness",
            "limitation_note": "Direct witness for candidate object class in declaration review.",
        },
        {
            "witness_ref": "witness:v85a:direct:operator",
            "semantic_declaration_session_ref": session,
            "source_refs": [_OPERATOR_TURN_SOURCE],
            "witnessed_element": "operator",
            "witness_strength": "direct",
            "witness_currentness": "current_turn_witness",
            "limitation_note": "Direct witness for declaration operator in review.",
        },
        {
            "witness_ref": "witness:v85a:direct:target-context",
            "semantic_declaration_session_ref": session,
            "source_refs": ["docs/LOCKED_CONTINUATION_vNEXT_PLUS239.md"],
            "witnessed_element": "target_context",
            "witness_strength": "direct",
            "witness_currentness": "current_repo_context",
            "limitation_note": "Direct repo context witness for declaration review target.",
        },
        {
            "witness_ref": "witness:v85a:support:canonical-loop",
            "semantic_declaration_session_ref": session,
            "source_refs": [_CANONICAL_META_LOOP_SUPPORT_DOC],
            "witnessed_element": "modifier",
            "witness_strength": "support_only",
            "witness_currentness": "support_context_only",
            "limitation_note": "Support witness contextualizes declaration review only.",
        },
    ]


def _base_negative_cue_rows() -> list[dict[str, object]]:
    session = "semantic-declaration-session:v85a:intent-to-declaration-office"
    return [
        {
            "negative_cue_ref": "negative-cue:v85a:asks-to-implement",
            "semantic_declaration_session_ref": session,
            "source_refs": [_OPERATOR_TURN_SOURCE],
            "cue_kind": "asks_to_implement_now",
            "effect_on_declaration": "routes_to_guardrail",
            "limitation_note": "Implementation-shaped cue routes to guardrail during review.",
        },
        {
            "negative_cue_ref": "negative-cue:v85a:select-v86",
            "semantic_declaration_session_ref": session,
            "source_refs": [_V85_SELECTOR_DOC],
            "cue_kind": "asks_to_select_next_family",
            "effect_on_declaration": "routes_to_future_family_only",
            "limitation_note": "Future-family cue routes to later selector review.",
        },
    ]


def _base_competency_rows() -> list[dict[str, object]]:
    session = "semantic-declaration-session:v85a:intent-to-declaration-office"
    rows: list[dict[str, object]] = []
    routing_by_kind: dict[str, str] = {
        "unknown_pointer_abstention": "route_to_abstain",
        "no_unauthorized_transition": "route_to_guardrail",
    }
    for kind in sorted(_REQUIRED_COMPETENCIES):
        rows.append(
            {
                "competency_ref": f"competency:v85a:{kind}",
                "semantic_declaration_session_ref": session,
                "competency_kind": kind,
                "required_posture": "required_for_declaration_review",
                "evidence_or_fixture_refs": [],
                "failure_routing_posture": routing_by_kind.get(kind, "route_to_uncertainty_slot"),
                "non_authority_guardrail_refs": ["guardrail:v85a:intent-to-declaration-office"],
            }
        )
    return rows


def derive_v85a_repo_semantic_declaration_source_index(
    *,
    repo_root: Path | None = None,
) -> RepoSemanticDeclarationSourceIndex:
    _ = repo_root
    payload = {
        "schema": REPO_SEMANTIC_DECLARATION_SOURCE_INDEX_SCHEMA,
        "semantic_declaration_source_index_id": "",
        "review_id": "vNext+239",
        "snapshot_id": "vNext+239-semantic-declaration-start",
        "source_set_id": "source-set:v85a:semantic-declaration-review",
        "source_rows": _v85_source_rows(),
        "semantic_act_witness_rows": _base_witness_rows(),
        "negative_cue_rows": _base_negative_cue_rows(),
        "resident_model_competency_rows": _base_competency_rows(),
        "source_index_summary": (
            "V85-A source index binds released V84-C substrate, current operator "
            "turn context, and support doctrine for semantic declaration review with "
            "no implementation."
        ),
    }
    payload["semantic_declaration_source_index_id"] = _surface_id(
        "repo_semantic_declaration_source_index",
        REPO_SEMANTIC_DECLARATION_SOURCE_INDEX_SCHEMA,
        payload,
        "semantic_declaration_source_index_id",
    )
    return RepoSemanticDeclarationSourceIndex.model_validate(payload)


def _selected_act_rows() -> list[dict[str, object]]:
    session = "semantic-declaration-session:v85a:intent-to-declaration-office"
    return [
        {
            "semantic_act_ref": "semantic-act:v85a:create-declaration-office",
            "semantic_declaration_session_ref": session,
            "operator": "CREATE",
            "object_class": "semantic.declaration@v1",
            "source_class": None,
            "target_class": "repo.review_surface@v1",
            "target_context_refs": ["packages/adeu_repo_description"],
            "modifiers": ["candidate_only", "review_only"],
            "binding_basis_refs": [
                "witness:v85a:direct:object-class",
                "witness:v85a:direct:operator",
                "witness:v85a:direct:target-context",
            ],
            "source_witness_refs": [
                "witness:v85a:direct:object-class",
                "witness:v85a:direct:operator",
                "witness:v85a:direct:target-context",
            ],
            "ambiguity_posture": "not_ambiguous",
            "registry_gap_posture": "no_registry_gap_claimed",
            "declaration_candidate_status": "candidate_recorded_for_review",
            "declaration_selection_status": "not_selected_by_v85a",
            "canonical_status": "canonical_status_unverified_by_v85a",
            "limitation_note": (
                "Declared semantic act remains a candidate for review; no implementation."
            ),
        }
    ]


def _v85_request_rows(
    *,
    source_index: RepoSemanticDeclarationSourceIndex,
) -> list[dict[str, object]]:
    session = "semantic-declaration-session:v85a:intent-to-declaration-office"
    witness_rows = [row.model_dump(mode="json") for row in source_index.semantic_act_witness_rows]
    competency_rows = [
        row.model_dump(mode="json") for row in source_index.resident_model_competency_rows
    ]
    negative_cue_rows = [row.model_dump(mode="json") for row in source_index.negative_cue_rows]
    eligible_sources = sorted(
        [
            _OPERATOR_TURN_SOURCE,
            _V84C_CLOSEOUT_FIXTURE,
            _V84C_HANDOFF_FIXTURE,
            _V84C_READINESS_FIXTURE,
            "docs/LOCKED_CONTINUATION_vNEXT_PLUS239.md",
        ]
    )
    return [
        {
            "declaration_request_ref": "declaration-request:v85a:intent-to-declaration-office",
            "semantic_declaration_session_ref": session,
            "candidate_ref": "candidate:v85:semantic-declaration-office",
            "turn_ref": "turn:v85a:implement-slice-a",
            "source_refs": eligible_sources,
            "source_witness_refs": [
                "witness:v85a:direct:object-class",
                "witness:v85a:direct:operator",
                "witness:v85a:direct:target-context",
            ],
            "operator_turn_refs": [_OPERATOR_TURN_SOURCE],
            "repo_context_refs": ["docs/LOCKED_CONTINUATION_vNEXT_PLUS239.md"],
            "declared_semantic_act_rows": _selected_act_rows(),
            "semantic_act_witness_rows": witness_rows,
            "negative_cue_rows": [],
            "resident_model_competency_rows": competency_rows,
            "declaration_horizon": "semantic_act_declaration",
            "requested_declaration_review_horizon": "semantic_declaration_review",
            "binding_posture": "selected",
            "binding_resolution_posture": "selected_for_later_lookup_review",
            "binding_basis_refs": [
                "witness:v85a:direct:object-class",
                "witness:v85a:direct:operator",
                "witness:v85a:direct:target-context",
            ],
            "negative_cue_refs": [],
            "uncertainty_slot_refs": [],
            "canonical_lookup_required_posture": "lookup_required_later",
            "declaration_candidate_status": "candidate_recorded_for_review",
            "canonical_lookup_status": "lookup_required_later",
            "declaration_selection_status": "not_selected_by_v85a",
            "declaration_recordability_posture": "recordable_from_concrete_operator_turn",
            "declaration_review_eligibility_posture": "eligible_for_semantic_declaration_review",
            "guardrail_refs": ["guardrail:v85a:intent-to-declaration-office"],
            "non_authority_posture": "no_declaration_authority_granted_by_v85",
            "odeu_lanes": sorted(["deontic", "epistemic", "ontological", "utility"]),
            "limitation_note": (
                "Semantic declaration request is eligible for review only; no implementation "
                "and no obligation expansion."
            ),
        },
        {
            "declaration_request_ref": "declaration-request:v85a:ambiguous-natural-binding",
            "semantic_declaration_session_ref": session,
            "candidate_ref": "candidate:v85:semantic-declaration-office",
            "turn_ref": "turn:v85a:ambiguous-natural-binding",
            "source_refs": sorted([_OPERATOR_TURN_SOURCE, _CANONICAL_META_LOOP_SUPPORT_DOC]),
            "source_witness_refs": ["witness:v85a:support:canonical-loop"],
            "operator_turn_refs": [_OPERATOR_TURN_SOURCE],
            "repo_context_refs": [],
            "declared_semantic_act_rows": [
                {
                    **_selected_act_rows()[0],
                    "semantic_act_ref": "semantic-act:v85a:ambiguous-natural-binding",
                    "ambiguity_posture": "ambiguous_requires_review",
                    "declaration_candidate_status": "ambiguous_candidate",
                    "canonical_status": "candidate_class_only",
                    "limitation_note": (
                        "Ambiguous semantic act remains candidate-only for review; "
                        "no implementation."
                    ),
                }
            ],
            "semantic_act_witness_rows": witness_rows,
            "negative_cue_rows": [],
            "resident_model_competency_rows": competency_rows,
            "declaration_horizon": "semantic_act_declaration",
            "requested_declaration_review_horizon": "ambiguity_review",
            "binding_posture": "ambiguous",
            "binding_resolution_posture": "ambiguous_requires_review",
            "binding_basis_refs": ["witness:v85a:support:canonical-loop"],
            "negative_cue_refs": [],
            "uncertainty_slot_refs": ["uncertainty:v85a:ambiguous-natural-binding"],
            "canonical_lookup_required_posture": "lookup_required_later",
            "declaration_candidate_status": "ambiguous_candidate",
            "canonical_lookup_status": "lookup_required_later",
            "declaration_selection_status": "ambiguous_not_selected",
            "declaration_recordability_posture": "recordable_from_concrete_operator_turn",
            "declaration_review_eligibility_posture": "blocked_by_ambiguous_binding",
            "guardrail_refs": ["guardrail:v85a:ambiguous-natural-binding"],
            "non_authority_posture": "no_declaration_authority_granted_by_v85",
            "odeu_lanes": sorted(["epistemic", "ontological"]),
            "limitation_note": (
                "Ambiguous binding is recorded for declaration review only; no implementation."
            ),
        },
        {
            "declaration_request_ref": "declaration-request:v85a:unknown-class-registry-gap",
            "semantic_declaration_session_ref": session,
            "candidate_ref": "candidate:v85:semantic-declaration-office",
            "turn_ref": "turn:v85a:unknown-class-registry-gap",
            "source_refs": sorted([_OPERATOR_TURN_SOURCE, _V85A_MAPPING_DOC]),
            "source_witness_refs": ["witness:v85a:direct:object-class"],
            "operator_turn_refs": [_OPERATOR_TURN_SOURCE],
            "repo_context_refs": [],
            "declared_semantic_act_rows": [
                {
                    **_selected_act_rows()[0],
                    "semantic_act_ref": "semantic-act:v85a:unknown-class-registry-gap",
                    "object_class": "semantic.declaration.office@v1",
                    "registry_gap_posture": "unknown_class_registry_gap",
                    "declaration_candidate_status": "registry_gap_candidate",
                    "canonical_status": "unknown_class_registry_gap",
                    "limitation_note": (
                        "Unknown class remains registry-gap candidate for review; "
                        "no implementation."
                    ),
                }
            ],
            "semantic_act_witness_rows": witness_rows,
            "negative_cue_rows": [],
            "resident_model_competency_rows": competency_rows,
            "declaration_horizon": "semantic_pointer_candidate",
            "requested_declaration_review_horizon": "registry_gap_review",
            "binding_posture": "registry_gap",
            "binding_resolution_posture": "registry_gap_declared",
            "binding_basis_refs": ["witness:v85a:direct:object-class"],
            "negative_cue_refs": [],
            "uncertainty_slot_refs": ["uncertainty:v85a:unknown-class-registry-gap"],
            "canonical_lookup_required_posture": "lookup_blocked_by_registry_gap",
            "declaration_candidate_status": "registry_gap_candidate",
            "canonical_lookup_status": "lookup_blocked_by_registry_gap",
            "declaration_selection_status": "registry_gap_not_selected",
            "declaration_recordability_posture": "recordable_from_concrete_operator_turn",
            "declaration_review_eligibility_posture": "blocked_by_registry_gap",
            "guardrail_refs": ["guardrail:v85a:unknown-class-registry-gap"],
            "non_authority_posture": "no_declaration_authority_granted_by_v85",
            "odeu_lanes": sorted(["epistemic", "ontological"]),
            "limitation_note": (
                "Registry-gap declaration is recorded for review only; no implementation."
            ),
        },
        {
            "declaration_request_ref": "declaration-request:v85a:support-context-only",
            "semantic_declaration_session_ref": session,
            "candidate_ref": "candidate:v85:semantic-declaration-office",
            "turn_ref": "turn:v85a:support-context-only",
            "source_refs": sorted([_CANONICAL_META_LOOP_SUPPORT_DOC, _POST_V84_ROADMAP_DOC]),
            "source_witness_refs": ["witness:v85a:support:canonical-loop"],
            "operator_turn_refs": [],
            "repo_context_refs": [],
            "declared_semantic_act_rows": [
                {
                    **_selected_act_rows()[0],
                    "semantic_act_ref": "semantic-act:v85a:support-context-only",
                    "declaration_candidate_status": "support_context_only_candidate",
                    "canonical_status": "candidate_class_only",
                    "limitation_note": (
                        "Support-context semantic act remains candidate-only for review; "
                        "no implementation."
                    ),
                }
            ],
            "semantic_act_witness_rows": witness_rows,
            "negative_cue_rows": negative_cue_rows,
            "resident_model_competency_rows": competency_rows,
            "declaration_horizon": "semantic_act_declaration",
            "requested_declaration_review_horizon": "support_context_review",
            "binding_posture": "blocked_by_missing_source",
            "binding_resolution_posture": "support_only_not_selected",
            "binding_basis_refs": ["witness:v85a:support:canonical-loop"],
            "negative_cue_refs": [
                "negative-cue:v85a:asks-to-implement",
                "negative-cue:v85a:select-v86",
            ],
            "uncertainty_slot_refs": ["uncertainty:v85a:support-context-only"],
            "canonical_lookup_required_posture": "lookup_not_selected_by_v85a",
            "declaration_candidate_status": "support_context_only_candidate",
            "canonical_lookup_status": "lookup_not_selected_by_v85a",
            "declaration_selection_status": "blocked_not_selected",
            "declaration_recordability_posture": "recordable_from_support_context_only",
            "declaration_review_eligibility_posture": "blocked_by_support_only_source",
            "guardrail_refs": ["guardrail:v85a:support-context-only"],
            "non_authority_posture": "no_declaration_authority_granted_by_v85",
            "odeu_lanes": sorted(["ontological", "utility"]),
            "limitation_note": (
                "Support-context declaration is recorded for review only; no implementation."
            ),
        },
    ]


def derive_v85a_repo_turn_semantic_declaration_request(
    *,
    repo_root: Path | None = None,
    semantic_declaration_source_index: RepoSemanticDeclarationSourceIndex | None = None,
) -> RepoTurnSemanticDeclarationRequest:
    _ = repo_root
    if semantic_declaration_source_index is None:
        semantic_declaration_source_index = derive_v85a_repo_semantic_declaration_source_index(
            repo_root=repo_root
        )
    payload = {
        "schema": REPO_TURN_SEMANTIC_DECLARATION_REQUEST_SCHEMA,
        "turn_semantic_declaration_request_id": "",
        "semantic_declaration_source_index_id": (
            semantic_declaration_source_index.semantic_declaration_source_index_id
        ),
        "review_id": semantic_declaration_source_index.review_id,
        "snapshot_id": semantic_declaration_source_index.snapshot_id,
        "source_set_id": semantic_declaration_source_index.source_set_id,
        "declaration_request_rows": sorted(
            _v85_request_rows(source_index=semantic_declaration_source_index),
            key=lambda row: str(row["declaration_request_ref"]),
        ),
        "declaration_review_summary": (
            "V85-A records semantic declaration requests for review with "
            "no implementation and no obligation expansion."
        ),
    }
    payload["turn_semantic_declaration_request_id"] = _surface_id(
        "repo_turn_semantic_declaration_request",
        REPO_TURN_SEMANTIC_DECLARATION_REQUEST_SCHEMA,
        payload,
        "turn_semantic_declaration_request_id",
    )
    return RepoTurnSemanticDeclarationRequest.model_validate(payload)


def _v85_guardrail_rows(
    *,
    turn_semantic_declaration_request: RepoTurnSemanticDeclarationRequest,
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for request_row in turn_semantic_declaration_request.declaration_request_rows:
        for guardrail_ref in request_row.guardrail_refs:
            rows.append(
                {
                    "guardrail_ref": guardrail_ref,
                    "semantic_declaration_session_ref": (
                        request_row.semantic_declaration_session_ref
                    ),
                    "candidate_ref": request_row.candidate_ref,
                    "source_refs": sorted(set(request_row.source_refs).union({_V85A_MAPPING_DOC})),
                    "declaration_request_refs": [request_row.declaration_request_ref],
                    "forbidden_declaration_actions": sorted(
                        _REQUIRED_FORBIDDEN_DECLARATION_ACTIONS
                    ),
                    "forbidden_downstream_actions": sorted(_REQUIRED_FORBIDDEN_DOWNSTREAM_ACTIONS),
                    "required_later_authority_refs": [
                        "later-authority:v85a:canonical-lookup-review"
                    ],
                    "declaration_non_authority_posture": (
                        "no_declaration_authority_granted_by_v85"
                    ),
                    "obligation_expansion_posture": ("no_obligation_expansion_performed_by_v85a"),
                    "implementation_posture": "no_implementation_performed_by_v85a",
                    "runtime_transition_posture": ("no_runtime_transition_performed_by_v85a"),
                    "future_family_selection_posture": ("no_future_family_selected_by_v85a"),
                    "limitation_note": (
                        "Guardrail keeps semantic declaration as review only with "
                        "no implementation, no obligation expansion, and no V86 selection."
                    ),
                }
            )
    return sorted(rows, key=lambda row: str(row["guardrail_ref"]))


def derive_v85a_repo_semantic_declaration_non_authority_guardrail(
    *,
    repo_root: Path | None = None,
    semantic_declaration_source_index: RepoSemanticDeclarationSourceIndex | None = None,
    turn_semantic_declaration_request: RepoTurnSemanticDeclarationRequest | None = None,
) -> RepoSemanticDeclarationNonAuthorityGuardrail:
    if semantic_declaration_source_index is None:
        semantic_declaration_source_index = derive_v85a_repo_semantic_declaration_source_index(
            repo_root=repo_root
        )
    if turn_semantic_declaration_request is None:
        turn_semantic_declaration_request = derive_v85a_repo_turn_semantic_declaration_request(
            repo_root=repo_root,
            semantic_declaration_source_index=semantic_declaration_source_index,
        )
    payload = {
        "schema": REPO_SEMANTIC_DECLARATION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
        "semantic_declaration_non_authority_guardrail_id": "",
        "turn_semantic_declaration_request_id": (
            turn_semantic_declaration_request.turn_semantic_declaration_request_id
        ),
        "semantic_declaration_source_index_id": (
            semantic_declaration_source_index.semantic_declaration_source_index_id
        ),
        "review_id": semantic_declaration_source_index.review_id,
        "snapshot_id": semantic_declaration_source_index.snapshot_id,
        "source_set_id": semantic_declaration_source_index.source_set_id,
        "guardrail_rows": _v85_guardrail_rows(
            turn_semantic_declaration_request=turn_semantic_declaration_request
        ),
        "guardrail_summary": (
            "V85-A non-authority guardrails keep semantic declaration from becoming "
            "obligation expansion, implementation, runtime transition, or later-family "
            "selection; no implementation and no obligation expansion."
        ),
    }
    payload["semantic_declaration_non_authority_guardrail_id"] = _surface_id(
        "repo_semantic_declaration_non_authority_guardrail",
        REPO_SEMANTIC_DECLARATION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
        payload,
        "semantic_declaration_non_authority_guardrail_id",
    )
    return RepoSemanticDeclarationNonAuthorityGuardrail.model_validate(payload)


def validate_v85a_semantic_declaration_review_bundle(
    *,
    v84_work_packet_activation_readiness_summary: RepoWorkPacketActivationReadinessSummary,
    v84_post_work_packet_activation_review_handoff: RepoPostWorkPacketActivationReviewHandoff,
    v84_work_packet_activation_family_closeout_alignment: (
        RepoWorkPacketActivationFamilyCloseoutAlignment
    ),
    semantic_declaration_source_index: RepoSemanticDeclarationSourceIndex,
    turn_semantic_declaration_request: RepoTurnSemanticDeclarationRequest,
    semantic_declaration_non_authority_guardrail: RepoSemanticDeclarationNonAuthorityGuardrail,
) -> None:
    _non_empty(
        v84_work_packet_activation_readiness_summary.work_packet_activation_readiness_summary_id,
        field_name="work_packet_activation_readiness_summary_id",
    )
    _non_empty(
        v84_post_work_packet_activation_review_handoff.post_work_packet_activation_review_handoff_id,
        field_name="post_work_packet_activation_review_handoff_id",
    )
    _non_empty(
        v84_work_packet_activation_family_closeout_alignment.work_packet_activation_family_closeout_alignment_id,
        field_name="work_packet_activation_family_closeout_alignment_id",
    )
    if (
        turn_semantic_declaration_request.semantic_declaration_source_index_id
        != semantic_declaration_source_index.semantic_declaration_source_index_id
    ):
        raise ValueError("V85-A request must reference released V85-A source index")
    if (
        semantic_declaration_non_authority_guardrail.semantic_declaration_source_index_id
        != semantic_declaration_source_index.semantic_declaration_source_index_id
        or semantic_declaration_non_authority_guardrail.turn_semantic_declaration_request_id
        != turn_semantic_declaration_request.turn_semantic_declaration_request_id
    ):
        raise ValueError("V85-A guardrails must reference released V85-A request and source index")
    if (
        semantic_declaration_non_authority_guardrail.review_id
        != semantic_declaration_source_index.review_id
        or turn_semantic_declaration_request.review_id
        != semantic_declaration_source_index.review_id
        or semantic_declaration_non_authority_guardrail.snapshot_id
        != semantic_declaration_source_index.snapshot_id
        or turn_semantic_declaration_request.snapshot_id
        != semantic_declaration_source_index.snapshot_id
        or semantic_declaration_non_authority_guardrail.source_set_id
        != semantic_declaration_source_index.source_set_id
        or turn_semantic_declaration_request.source_set_id
        != semantic_declaration_source_index.source_set_id
    ):
        raise ValueError("V85-A bundle components must share review, snapshot, and source set IDs")

    known_source_roles = {
        row.source_ref: row.semantic_declaration_source_role
        for row in semantic_declaration_source_index.source_rows
    }
    known_sources = set(known_source_roles)
    known_witnesses = {
        row.witness_ref: row for row in semantic_declaration_source_index.semantic_act_witness_rows
    }
    known_cues = {
        row.negative_cue_ref: row for row in semantic_declaration_source_index.negative_cue_rows
    }
    known_competencies = {
        row.competency_ref: row
        for row in semantic_declaration_source_index.resident_model_competency_rows
    }
    known_guardrails = {
        row.guardrail_ref: row
        for row in semantic_declaration_non_authority_guardrail.guardrail_rows
    }
    known_requests = {
        row.declaration_request_ref: row
        for row in turn_semantic_declaration_request.declaration_request_rows
    }

    for request_row in turn_semantic_declaration_request.declaration_request_rows:
        if any(ref not in known_sources for ref in request_row.source_refs):
            raise ValueError("semantic declaration request source refs must be indexed")
        if any(ref not in known_witnesses for ref in request_row.source_witness_refs):
            raise ValueError("semantic declaration witness refs must be indexed")
        if any(ref not in known_cues for ref in request_row.negative_cue_refs):
            raise ValueError("semantic declaration negative cue refs must be indexed")
        if any(ref not in known_guardrails for ref in request_row.guardrail_refs):
            raise ValueError("semantic declaration request guardrail refs must be indexed")
        for guardrail_ref in request_row.guardrail_refs:
            guardrail_row = known_guardrails[guardrail_ref]
            if request_row.declaration_request_ref not in guardrail_row.declaration_request_refs:
                raise ValueError("semantic declaration guardrails must link back to request")
            if guardrail_row.candidate_ref != request_row.candidate_ref:
                raise ValueError("semantic declaration guardrails must match candidate")
            if (
                guardrail_row.semantic_declaration_session_ref
                != request_row.semantic_declaration_session_ref
            ):
                raise ValueError("semantic declaration guardrails must match declaration session")
        for competency_ref in [
            row.competency_ref for row in request_row.resident_model_competency_rows
        ]:
            if competency_ref not in known_competencies:
                raise ValueError("resident model competency refs must be indexed")
        if (
            request_row.declaration_review_eligibility_posture
            == "eligible_for_semantic_declaration_review"
        ):
            roles = {known_source_roles[ref] for ref in request_row.source_refs}
            if roles.issubset(_SUPPORT_ONLY_SOURCE_ROLES):
                raise ValueError("support-only sources cannot make declaration review eligible")
            if not roles.intersection(_ELIGIBLE_SOURCE_ROLES):
                raise ValueError("eligible declaration requires released V84-C substrate")
            if "opaque_pointer_context" in roles and not roles.intersection(
                _CURRENT_TASK_SOURCE_ROLES
            ):
                raise ValueError("opaque pointer competence cannot establish natural binding")
            if not roles.intersection(_CURRENT_TASK_SOURCE_ROLES):
                raise ValueError("eligible declaration requires current turn or repo task source")
            direct_witnesses = [
                known_witnesses[ref]
                for ref in request_row.source_witness_refs
                if known_witnesses[ref].witness_strength == "direct"
                and known_witnesses[ref].witness_currentness
                in {"current_turn_witness", "current_repo_context"}
            ]
            if not direct_witnesses:
                raise ValueError("eligible declaration requires indexed direct/current witnesses")

    for guardrail_row in semantic_declaration_non_authority_guardrail.guardrail_rows:
        if any(ref not in known_sources for ref in guardrail_row.source_refs):
            raise ValueError("semantic declaration guardrail source refs must be indexed")
        if any(ref not in known_requests for ref in guardrail_row.declaration_request_refs):
            raise ValueError("guardrail request refs must be released V85-A requests")
        sessions = {
            known_requests[ref].semantic_declaration_session_ref
            for ref in guardrail_row.declaration_request_refs
        }
        if sessions != {guardrail_row.semantic_declaration_session_ref}:
            raise ValueError("guardrail declaration session must match request session")


def derive_v85a_semantic_declaration_review_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoWorkPacketActivationReadinessSummary,
    RepoPostWorkPacketActivationReviewHandoff,
    RepoWorkPacketActivationFamilyCloseoutAlignment,
    RepoSemanticDeclarationSourceIndex,
    RepoTurnSemanticDeclarationRequest,
    RepoSemanticDeclarationNonAuthorityGuardrail,
]:
    (
        v84_readiness_summary,
        v84_handoff,
        v84_closeout,
    ) = _v84c_released_bundle(repo_root=repo_root)
    source_index = derive_v85a_repo_semantic_declaration_source_index(repo_root=repo_root)
    request = derive_v85a_repo_turn_semantic_declaration_request(
        repo_root=repo_root,
        semantic_declaration_source_index=source_index,
    )
    guardrail = derive_v85a_repo_semantic_declaration_non_authority_guardrail(
        repo_root=repo_root,
        semantic_declaration_source_index=source_index,
        turn_semantic_declaration_request=request,
    )
    validate_v85a_semantic_declaration_review_bundle(
        v84_work_packet_activation_readiness_summary=v84_readiness_summary,
        v84_post_work_packet_activation_review_handoff=v84_handoff,
        v84_work_packet_activation_family_closeout_alignment=v84_closeout,
        semantic_declaration_source_index=source_index,
        turn_semantic_declaration_request=request,
        semantic_declaration_non_authority_guardrail=guardrail,
    )
    return (
        v84_readiness_summary,
        v84_handoff,
        v84_closeout,
        source_index,
        request,
        guardrail,
    )


class RepoSemanticPointerRow(_CartographyBase):
    pointer_ref: str
    semantic_declaration_session_ref: str
    raw_pointer: str
    parsed_operator: str
    parsed_class: str
    parsed_version: str
    pointer_parse_posture: PointerParsePosture
    normalization_posture: PointerNormalizationPosture
    source_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_pointer_row(self) -> "RepoSemanticPointerRow":
        for attr in (
            "pointer_ref",
            "semantic_declaration_session_ref",
            "raw_pointer",
            "parsed_operator",
            "parsed_class",
            "parsed_version",
        ):
            _non_empty(getattr(self, attr), field_name=attr)
        _validate_repo_refs(self.source_refs, field_name="source_refs")
        if (
            self.pointer_parse_posture == "parsed_with_alias"
            and self.normalization_posture != "alias_normalized_by_registry"
        ):
            raise ValueError("alias parses require alias normalization posture")
        if self.pointer_parse_posture in {
            "malformed_pointer",
            "unknown_version",
        } and self.normalization_posture not in {
            "normalization_rejected",
            "normalization_not_authorized",
        }:
            raise ValueError("malformed or unknown-version pointers must fail closed")
        if (
            self.pointer_parse_posture == "unknown_version"
            and self.parsed_version.lower() == "latest"
        ):
            raise ValueError("unknown pointer versions cannot normalize to latest")
        _reject_v85_authority_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("pointer", "review"),
            ),
            field_name="limitation_note",
        )
        return self


class RepoSemanticRegistryAliasRow(_CartographyBase):
    alias_ref: str
    alias_value: str
    canonical_id: str
    normalization_posture: PointerNormalizationPosture
    source_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_alias_row(self) -> "RepoSemanticRegistryAliasRow":
        for attr in ("alias_ref", "alias_value", "canonical_id"):
            _non_empty(getattr(self, attr), field_name=attr)
        _validate_repo_refs(self.source_refs, field_name="source_refs")
        if self.normalization_posture != "alias_normalized_by_registry":
            raise ValueError("registry aliases must declare alias normalization")
        _reject_v85_authority_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("alias", "review"),
            ),
            field_name="limitation_note",
        )
        return self


class RepoCanonicalMetaLookupRow(_CartographyBase):
    lookup_ref: str
    semantic_declaration_session_ref: str
    candidate_ref: str
    declaration_request_refs: list[str] = Field(min_length=1)
    source_refs: list[str] = Field(min_length=1)
    semantic_pointer: str
    semantic_pointer_rows: list[RepoSemanticPointerRow] = Field(min_length=1)
    operator_registry_refs: list[str] = Field(default_factory=list)
    class_registry_refs: list[str] = Field(default_factory=list)
    obligation_family_refs: list[str] = Field(default_factory=list)
    lookup_input_kind: LookupInputKind
    lookup_posture: LookupPosture
    canonical_lookup_status: V85BCanonicalLookupStatus
    pointer_competency_kind: PointerCompetencyKind
    competency_claim_horizon: CompetencyClaimHorizon
    order_preservation_posture: OrderPreservationPosture
    duplicate_preservation_posture: DuplicatePreservationPosture
    unknown_pointer_posture: UnknownPointerPosture
    conflict_posture: ConflictPosture
    obligation_expansion_posture: LookupObligationExpansionPosture
    non_authority_guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_lookup_row(self) -> "RepoCanonicalMetaLookupRow":
        for attr in (
            "lookup_ref",
            "semantic_declaration_session_ref",
            "candidate_ref",
            "semantic_pointer",
        ):
            _non_empty(getattr(self, attr), field_name=attr)
        for attr in (
            "declaration_request_refs",
            "source_refs",
            "operator_registry_refs",
            "class_registry_refs",
            "obligation_family_refs",
            "non_authority_guardrail_refs",
        ):
            values = getattr(self, attr)
            if attr == "source_refs":
                _validate_repo_refs(values, field_name=attr)
            else:
                _validate_sorted_refs(values, field_name=attr)
        _sorted_unique_by_ref(
            self.semantic_pointer_rows,
            attr="pointer_ref",
            field_name="semantic_pointer_rows",
        )
        for pointer_row in self.semantic_pointer_rows:
            if (
                pointer_row.semantic_declaration_session_ref
                != self.semantic_declaration_session_ref
            ):
                raise ValueError("lookup pointer rows must share declaration session")
        _reject_v85_authority_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("lookup", "review", "no obligation"),
            ),
            field_name="limitation_note",
        )
        if self.lookup_posture == "exact_match_for_review_only":
            if self.canonical_lookup_status != "exact_match_for_review_only":
                raise ValueError("exact lookup rows must carry exact lookup status")
            if self.lookup_input_kind != "opaque_pointer":
                if not self.operator_registry_refs or not self.class_registry_refs:
                    raise ValueError("semantic exact lookup requires operator and class refs")
            if any(
                pointer.pointer_parse_posture not in {"parsed_exact", "parsed_with_alias"}
                for pointer in self.semantic_pointer_rows
            ):
                raise ValueError("exact lookup requires exact or alias pointer parses")
        if self.lookup_input_kind == "opaque_pointer":
            if self.competency_claim_horizon != "pointer_obedience_only":
                raise ValueError("opaque lookup competence is pointer obedience only")
            if self.obligation_family_refs:
                raise ValueError("opaque lookup rows cannot name obligation families")
        if self.lookup_posture in {"unknown_pointer_abstained", "registry_gap"}:
            if self.obligation_family_refs:
                raise ValueError("unknown or registry-gap lookup cannot name obligations")
            if self.unknown_pointer_posture not in {
                "unknown_pointer_abstained",
                "unknown_pointer_registry_gap",
            }:
                raise ValueError("unknown lookup rows must carry unknown-pointer posture")
        if self.lookup_posture == "registry_gap" and self.canonical_lookup_status != "registry_gap":
            raise ValueError("registry-gap lookup rows must carry registry-gap status")
        if self.lookup_posture == "conflict_requires_review":
            if self.conflict_posture != "conflict_requires_review":
                raise ValueError("conflict lookup rows must carry conflict posture")
        if self.obligation_expansion_posture not in {
            "lookup_result_only",
            "named_for_later_expansion_only",
            "expansion_requires_v86_or_later",
            "expansion_blocked_by_ambiguity",
            "expansion_blocked_by_registry_gap",
            "expansion_not_authorized_by_v85",
        }:
            raise ValueError("lookup rows cannot expand obligations")
        if self.obligation_family_refs and self.obligation_expansion_posture not in {
            "lookup_result_only",
            "named_for_later_expansion_only",
            "expansion_requires_v86_or_later",
        }:
            raise ValueError("obligation families must be named for later expansion only")
        return self


class RepoCanonicalMetaLookupIndex(_CartographyBase):
    schema: Literal[REPO_CANONICAL_META_LOOKUP_INDEX_SCHEMA]
    canonical_meta_lookup_index_id: str
    semantic_declaration_source_index_id: str
    turn_semantic_declaration_request_id: str
    semantic_declaration_non_authority_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    lookup_rows: list[RepoCanonicalMetaLookupRow] = Field(min_length=1)
    lookup_summary: str

    @model_validator(mode="after")
    def _validate_lookup_surface(self) -> "RepoCanonicalMetaLookupIndex":
        for attr in (
            "canonical_meta_lookup_index_id",
            "semantic_declaration_source_index_id",
            "turn_semantic_declaration_request_id",
            "semantic_declaration_non_authority_guardrail_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
        ):
            _non_empty(getattr(self, attr), field_name=attr)
        _sorted_unique_by_ref(self.lookup_rows, attr="lookup_ref", field_name="lookup_rows")
        _reject_v85_authority_claim(
            _require_terms(
                self.lookup_summary,
                field_name="lookup_summary",
                terms=("lookup", "review", "no obligation"),
            ),
            field_name="lookup_summary",
        )
        _assert_surface_id(
            surface_name="repo_canonical_meta_lookup_index",
            schema=REPO_CANONICAL_META_LOOKUP_INDEX_SCHEMA,
            payload=self.model_dump(mode="json"),
            id_key="canonical_meta_lookup_index_id",
            actual=self.canonical_meta_lookup_index_id,
        )
        return self


class RepoSemanticOperatorClassRegistryRow(_CartographyBase):
    registry_ref: str
    semantic_declaration_session_ref: str
    source_refs: list[str] = Field(min_length=1)
    registry_entry_kind: RegistryEntryKind
    registry_domain: RegistryDomain
    canonical_id: str
    alias_rows: list[RepoSemanticRegistryAliasRow] = Field(default_factory=list)
    entry_status: RegistryEntryStatus
    entry_currentness: RegistryEntryCurrentness
    entry_scope_posture: RegistryEntryScopePosture
    operator_semantics_posture: OperatorSemanticsPosture
    class_semantics_posture: ClassSemanticsPosture
    non_invention_guardrail: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_registry_row(self) -> "RepoSemanticOperatorClassRegistryRow":
        for attr in ("registry_ref", "semantic_declaration_session_ref", "canonical_id"):
            _non_empty(getattr(self, attr), field_name=attr)
        _validate_repo_refs(self.source_refs, field_name="source_refs")
        _sorted_unique_by_ref(self.alias_rows, attr="alias_ref", field_name="alias_rows")
        for alias in self.alias_rows:
            if alias.canonical_id != self.canonical_id:
                raise ValueError("alias rows must normalize to the registry canonical id")
        if self.entry_status == "current_registry_entry":
            if self.entry_currentness != "current_registry_entry":
                raise ValueError("current registry entries require currentness")
            if self.entry_scope_posture != "lookup_review_only":
                raise ValueError("current registry entries are lookup-review only")
        if self.registry_domain == "operator":
            if self.registry_entry_kind != "operator_entry":
                raise ValueError("operator registry rows must use operator entry kind")
            if self.class_semantics_posture == "semantic_class_for_lookup_only":
                raise ValueError("operator registry rows cannot claim class semantics")
        if self.registry_domain != "operator":
            if self.registry_entry_kind == "operator_entry":
                raise ValueError("non-operator registry rows cannot use operator entry kind")
            if self.operator_semantics_posture == "action_verb_for_declaration_only":
                raise ValueError("class registry rows cannot claim operator semantics")
        if (
            self.canonical_id == "GATE"
            and self.operator_semantics_posture != "guard_or_route_for_later_authority_review"
        ):
            raise ValueError("GATE must remain guard or route for later authority review")
        _reject_v85_authority_claim(
            _require_terms(
                self.non_invention_guardrail,
                field_name="non_invention_guardrail",
                terms=("registry", "review"),
            ),
            field_name="non_invention_guardrail",
        )
        _reject_v85_authority_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("registry", "review"),
            ),
            field_name="limitation_note",
        )
        return self


class RepoSemanticOperatorClassRegistry(_CartographyBase):
    schema: Literal[REPO_SEMANTIC_OPERATOR_CLASS_REGISTRY_SCHEMA]
    semantic_operator_class_registry_id: str
    semantic_declaration_source_index_id: str
    turn_semantic_declaration_request_id: str
    semantic_declaration_non_authority_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    registry_rows: list[RepoSemanticOperatorClassRegistryRow] = Field(min_length=1)
    registry_summary: str

    @model_validator(mode="after")
    def _validate_registry_surface(self) -> "RepoSemanticOperatorClassRegistry":
        for attr in (
            "semantic_operator_class_registry_id",
            "semantic_declaration_source_index_id",
            "turn_semantic_declaration_request_id",
            "semantic_declaration_non_authority_guardrail_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
        ):
            _non_empty(getattr(self, attr), field_name=attr)
        _sorted_unique_by_ref(
            self.registry_rows,
            attr="registry_ref",
            field_name="registry_rows",
        )
        _reject_v85_authority_claim(
            _require_terms(
                self.registry_summary,
                field_name="registry_summary",
                terms=("registry", "review", "no obligation"),
            ),
            field_name="registry_summary",
        )
        _assert_surface_id(
            surface_name="repo_semantic_operator_class_registry",
            schema=REPO_SEMANTIC_OPERATOR_CLASS_REGISTRY_SCHEMA,
            payload=self.model_dump(mode="json"),
            id_key="semantic_operator_class_registry_id",
            actual=self.semantic_operator_class_registry_id,
        )
        return self


class RepoObligationFamilyRegistryRow(_CartographyBase):
    obligation_family_ref: str
    semantic_declaration_session_ref: str
    source_refs: list[str] = Field(min_length=1)
    obligation_family_id: str
    obligation_family_label: str
    applies_to_operator_refs: list[str] = Field(default_factory=list)
    applies_to_class_refs: list[str] = Field(default_factory=list)
    obligation_family_relation_kind: ObligationFamilyRelationKind
    obligation_family_activation_posture: ObligationFamilyActivationPosture
    required_future_surfaces: list[str] = Field(min_length=1)
    future_expansion_posture: FutureExpansionPosture
    evidence_contract_required_posture: EvidenceContractRequiredPosture
    waiver_posture: WaiverPosture
    non_execution_guardrail: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_obligation_family_row(self) -> "RepoObligationFamilyRegistryRow":
        for attr in (
            "obligation_family_ref",
            "semantic_declaration_session_ref",
            "obligation_family_id",
            "obligation_family_label",
        ):
            _non_empty(getattr(self, attr), field_name=attr)
        _validate_repo_refs(self.source_refs, field_name="source_refs")
        _validate_sorted_refs(self.applies_to_operator_refs, field_name="applies_to_operator_refs")
        _validate_sorted_refs(self.applies_to_class_refs, field_name="applies_to_class_refs")
        _validate_sorted_refs(self.required_future_surfaces, field_name="required_future_surfaces")
        if not self.applies_to_operator_refs and not self.applies_to_class_refs:
            if self.obligation_family_relation_kind not in {
                "requires_later_disambiguation",
                "conflict_or_exclusion",
            }:
                raise ValueError("obligation families require operator/class applicability refs")
        if self.obligation_family_activation_posture not in {
            "lookup_result_only",
            "named_for_later_expansion_only",
            "expansion_requires_v86_or_later",
        }:
            raise ValueError("obligation family rows cannot expand obligations in V85-B")
        if self.future_expansion_posture not in {
            "named_for_later_expansion_only",
            "expansion_requires_future_family",
            "expansion_not_authorized_by_v85",
        }:
            raise ValueError("obligation family expansion must remain future-bound")
        if self.evidence_contract_required_posture != "evidence_contract_not_created_by_v85b":
            raise ValueError("V85-B cannot create evidence contracts")
        _reject_v85_authority_claim(
            _require_terms(
                self.non_execution_guardrail,
                field_name="non_execution_guardrail",
                terms=("no implementation", "no obligation"),
            ),
            field_name="non_execution_guardrail",
        )
        _reject_v85_authority_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("family", "review"),
            ),
            field_name="limitation_note",
        )
        return self


class RepoObligationFamilyRegistry(_CartographyBase):
    schema: Literal[REPO_OBLIGATION_FAMILY_REGISTRY_SCHEMA]
    obligation_family_registry_id: str
    semantic_declaration_source_index_id: str
    turn_semantic_declaration_request_id: str
    semantic_declaration_non_authority_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    obligation_family_rows: list[RepoObligationFamilyRegistryRow] = Field(min_length=1)
    obligation_family_registry_summary: str

    @model_validator(mode="after")
    def _validate_obligation_surface(self) -> "RepoObligationFamilyRegistry":
        for attr in (
            "obligation_family_registry_id",
            "semantic_declaration_source_index_id",
            "turn_semantic_declaration_request_id",
            "semantic_declaration_non_authority_guardrail_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
        ):
            _non_empty(getattr(self, attr), field_name=attr)
        _sorted_unique_by_ref(
            self.obligation_family_rows,
            attr="obligation_family_ref",
            field_name="obligation_family_rows",
        )
        _reject_v85_authority_claim(
            _require_terms(
                self.obligation_family_registry_summary,
                field_name="obligation_family_registry_summary",
                terms=("obligation", "review", "no implementation"),
            ),
            field_name="obligation_family_registry_summary",
        )
        _assert_surface_id(
            surface_name="repo_obligation_family_registry",
            schema=REPO_OBLIGATION_FAMILY_REGISTRY_SCHEMA,
            payload=self.model_dump(mode="json"),
            id_key="obligation_family_registry_id",
            actual=self.obligation_family_registry_id,
        )
        return self


class RepoSemanticPointerLookupFixtureRow(_CartographyBase):
    lookup_fixture_ref: str
    semantic_declaration_session_ref: str
    source_refs: list[str] = Field(min_length=1)
    fixture_kind: LookupFixtureKind
    pointer_competency_kind: PointerCompetencyKind
    competency_claim_horizon: CompetencyClaimHorizon
    input_pointer_rows: list[RepoSemanticPointerRow] = Field(min_length=1)
    expected_lookup_rows: list[str] = Field(default_factory=list)
    expected_order_posture: ExpectedOrderPosture
    expected_duplicate_posture: ExpectedDuplicatePosture
    expected_unknown_posture: ExpectedUnknownPosture
    expected_conflict_posture: ExpectedConflictPosture
    actual_result_refs: list[str] = Field(default_factory=list)
    fixture_posture: FixturePosture
    non_authority_guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_fixture_row(self) -> "RepoSemanticPointerLookupFixtureRow":
        _non_empty(self.lookup_fixture_ref, field_name="lookup_fixture_ref")
        _non_empty(
            self.semantic_declaration_session_ref,
            field_name="semantic_declaration_session_ref",
        )
        _validate_repo_refs(self.source_refs, field_name="source_refs")
        pointer_refs = [row.pointer_ref for row in self.input_pointer_rows]
        if len(pointer_refs) != len(set(pointer_refs)):
            raise ValueError("input_pointer_rows must not repeat pointer refs")
        for attr in (
            "expected_lookup_rows",
            "actual_result_refs",
            "non_authority_guardrail_refs",
        ):
            _validate_sorted_refs(getattr(self, attr), field_name=attr)
        for pointer in self.input_pointer_rows:
            if pointer.semantic_declaration_session_ref != self.semantic_declaration_session_ref:
                raise ValueError("fixture pointer rows must share declaration session")
        if self.fixture_kind.startswith("opaque_pointer"):
            if self.competency_claim_horizon != "pointer_obedience_only":
                raise ValueError("opaque fixtures can claim pointer obedience only")
            if any("natural" in value.lower() for value in self.expected_lookup_rows):
                raise ValueError("opaque fixtures cannot claim natural semantic binding")
        if self.fixture_kind.endswith("unknown_abstain"):
            if self.expected_unknown_posture != "unknown_pointer_abstained":
                raise ValueError("unknown-abstain fixtures must expect abstention")
        if (
            self.fixture_kind.endswith("exact_lookup")
            or self.fixture_kind == "explicit_semantic_pointer_lookup"
        ) and not self.actual_result_refs:
            raise ValueError("exact lookup fixtures require actual lookup refs")
        _reject_v85_authority_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("fixture", "review"),
            ),
            field_name="limitation_note",
        )
        return self


class RepoSemanticPointerLookupFixture(_CartographyBase):
    schema: Literal[REPO_SEMANTIC_POINTER_LOOKUP_FIXTURE_SCHEMA]
    semantic_pointer_lookup_fixture_id: str
    canonical_meta_lookup_index_id: str
    semantic_operator_class_registry_id: str
    obligation_family_registry_id: str
    semantic_declaration_source_index_id: str
    turn_semantic_declaration_request_id: str
    semantic_declaration_non_authority_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    lookup_fixture_rows: list[RepoSemanticPointerLookupFixtureRow] = Field(min_length=1)
    lookup_fixture_summary: str

    @model_validator(mode="after")
    def _validate_fixture_surface(self) -> "RepoSemanticPointerLookupFixture":
        for attr in (
            "semantic_pointer_lookup_fixture_id",
            "canonical_meta_lookup_index_id",
            "semantic_operator_class_registry_id",
            "obligation_family_registry_id",
            "semantic_declaration_source_index_id",
            "turn_semantic_declaration_request_id",
            "semantic_declaration_non_authority_guardrail_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
        ):
            _non_empty(getattr(self, attr), field_name=attr)
        _sorted_unique_by_ref(
            self.lookup_fixture_rows,
            attr="lookup_fixture_ref",
            field_name="lookup_fixture_rows",
        )
        _reject_v85_authority_claim(
            _require_terms(
                self.lookup_fixture_summary,
                field_name="lookup_fixture_summary",
                terms=("fixture", "review", "no implementation"),
            ),
            field_name="lookup_fixture_summary",
        )
        _assert_surface_id(
            surface_name="repo_semantic_pointer_lookup_fixture",
            schema=REPO_SEMANTIC_POINTER_LOOKUP_FIXTURE_SCHEMA,
            payload=self.model_dump(mode="json"),
            id_key="semantic_pointer_lookup_fixture_id",
            actual=self.semantic_pointer_lookup_fixture_id,
        )
        return self


def _v85b_base_source_refs() -> list[str]:
    return sorted(
        [
            _V85A_SOURCE_INDEX_FIXTURE,
            _V85A_REQUEST_FIXTURE,
            _V85A_GUARDRAIL_FIXTURE,
            _V85B_LOCK_DOC,
            _V85B_MAPPING_DOC,
        ]
    )


def _semantic_pointer_row(
    *,
    pointer_ref: str,
    session: str,
    raw_pointer: str,
    parsed_operator: str,
    parsed_class: str,
    parsed_version: str,
    pointer_parse_posture: PointerParsePosture = "parsed_exact",
    normalization_posture: PointerNormalizationPosture = "normalization_not_required",
) -> dict[str, object]:
    return {
        "pointer_ref": pointer_ref,
        "semantic_declaration_session_ref": session,
        "raw_pointer": raw_pointer,
        "parsed_operator": parsed_operator,
        "parsed_class": parsed_class,
        "parsed_version": parsed_version,
        "pointer_parse_posture": pointer_parse_posture,
        "normalization_posture": normalization_posture,
        "source_refs": _v85b_base_source_refs(),
        "limitation_note": "Pointer row is recorded for lookup review only.",
    }


def _v85b_registry_rows(session: str) -> list[dict[str, object]]:
    source_refs = _v85b_base_source_refs()
    operators = [
        "AGGREGATE",
        "CACHE",
        "CLOSEOUT",
        "CONNECT",
        "CREATE",
        "GATE",
        "MIGRATE",
        "MODIFY",
        "NORMALIZE",
        "PERSIST",
        "PROJECT",
        "RECONCILE",
        "REMOVE",
        "REVIEW",
        "ROUTE",
        "SUBSCRIBE",
        "TRANSITION",
        "VALIDATE",
    ]
    classes = [
        "audit.report@v1",
        "cache.layer@v1",
        "capability.gate@v1",
        "closeout.artifact@v1",
        "event.subscription@v1",
        "evidence.bundle@v1",
        "migration.plan@v1",
        "persistence.store@v1",
        "readiness.summary@v1",
        "resource.handle@v1",
        "router.dispatcher@v1",
        "schema.binding@v1",
        "semantic.classifier@v1",
        "semantic.normalizer@v1",
        "semantic.summarizer@v1",
        "semantic.validator@v1",
        "state.transition@v1",
        "ui.menu@v1",
        "ui.modal@v1",
        "ui.popover@v1",
        "ui.projection@v1",
        "ui.surface@v1",
        "worker.taskpack@v1",
    ]
    rows: list[dict[str, object]] = []
    for operator in operators:
        rows.append(
            {
                "registry_ref": f"registry:v85b:operator:{operator}",
                "semantic_declaration_session_ref": session,
                "source_refs": source_refs,
                "registry_entry_kind": "operator_entry",
                "registry_domain": "operator",
                "canonical_id": operator,
                "alias_rows": [],
                "entry_status": "current_registry_entry",
                "entry_currentness": "current_registry_entry",
                "entry_scope_posture": "lookup_review_only",
                "operator_semantics_posture": (
                    "guard_or_route_for_later_authority_review"
                    if operator == "GATE"
                    else "action_verb_for_declaration_only"
                ),
                "class_semantics_posture": "not_runtime_class_behavior",
                "non_invention_guardrail": (
                    "Registry row is for review only and does not invent runtime behavior."
                ),
                "limitation_note": (
                    f"{operator} is a semantic registry entry for declaration review."
                ),
            }
        )
    for class_id in classes:
        alias_rows: list[dict[str, object]] = []
        if class_id == "ui.menu@v1":
            alias_rows.append(
                {
                    "alias_ref": "alias:v85b:ui.menu@v1:menu@v1",
                    "alias_value": "menu@v1",
                    "canonical_id": "ui.menu@v1",
                    "normalization_posture": "alias_normalized_by_registry",
                    "source_refs": source_refs,
                    "limitation_note": "Alias row is available for lookup review only.",
                }
            )
        rows.append(
            {
                "registry_ref": f"registry:v85b:object_class:{class_id}",
                "semantic_declaration_session_ref": session,
                "source_refs": source_refs,
                "registry_entry_kind": "class_entry",
                "registry_domain": "object_class",
                "canonical_id": class_id,
                "alias_rows": alias_rows,
                "entry_status": "current_registry_entry",
                "entry_currentness": "current_registry_entry",
                "entry_scope_posture": "lookup_review_only",
                "operator_semantics_posture": "not_runtime_behavior",
                "class_semantics_posture": "semantic_class_for_lookup_only",
                "non_invention_guardrail": (
                    "Registry row is for review only and does not invent implementation."
                ),
                "limitation_note": (
                    f"{class_id} is a semantic class registry entry for lookup review."
                ),
            }
        )
    return sorted(rows, key=lambda row: str(row["registry_ref"]))


def _v85b_obligation_family_rows(session: str) -> list[dict[str, object]]:
    family_ids = [
        "absence_null_empty_distinction@v1",
        "birth_continuation_death_algebra@v1",
        "branch_specific_witness@v1",
        "capability_guard@v1",
        "cross_field_consistency@v1",
        "enum_exhaustiveness@v1",
        "evidence_sufficiency@v1",
        "failure_path_fail_closed@v1",
        "idempotence_reentry@v1",
        "non_vacuous_validation@v1",
        "partial_retry_reentry@v1",
        "projection_source_integrity@v1",
        "rollback_cleanup_teardown@v1",
        "source_witness_preservation@v1",
        "stateful_lifecycle@v1",
        "staleness_invalidation@v1",
        "unknown_case_handling@v1",
        "waiver_explicitness@v1",
    ]
    source_refs = _v85b_base_source_refs()
    rows: list[dict[str, object]] = []
    for family_id in family_ids:
        rows.append(
            {
                "obligation_family_ref": f"obligation-family:v85b:{family_id}",
                "semantic_declaration_session_ref": session,
                "source_refs": source_refs,
                "obligation_family_id": family_id,
                "obligation_family_label": family_id.replace("@v1", "").replace("_", " "),
                "applies_to_operator_refs": ["registry:v85b:operator:CREATE"],
                "applies_to_class_refs": ["registry:v85b:object_class:ui.menu@v1"],
                "obligation_family_relation_kind": "applies_by_object_class",
                "obligation_family_activation_posture": "named_for_later_expansion_only",
                "required_future_surfaces": ["V86:obligation-expansion-review"],
                "future_expansion_posture": "expansion_requires_future_family",
                "evidence_contract_required_posture": "evidence_contract_not_created_by_v85b",
                "waiver_posture": "waiver_requires_later_review",
                "non_execution_guardrail": (
                    "No implementation and no obligation expansion occurs in V85-B."
                ),
                "limitation_note": (
                    f"{family_id} is named as an obligation family for review only."
                ),
            }
        )
    return sorted(rows, key=lambda row: str(row["obligation_family_ref"]))


def derive_v85b_repo_semantic_operator_class_registry(
    *,
    repo_root: Path | None = None,
    semantic_declaration_source_index: RepoSemanticDeclarationSourceIndex | None = None,
    turn_semantic_declaration_request: RepoTurnSemanticDeclarationRequest | None = None,
    semantic_declaration_non_authority_guardrail: (
        RepoSemanticDeclarationNonAuthorityGuardrail | None
    ) = None,
) -> RepoSemanticOperatorClassRegistry:
    _ = repo_root
    if semantic_declaration_source_index is None:
        semantic_declaration_source_index = derive_v85a_repo_semantic_declaration_source_index()
    if turn_semantic_declaration_request is None:
        turn_semantic_declaration_request = derive_v85a_repo_turn_semantic_declaration_request(
            semantic_declaration_source_index=semantic_declaration_source_index
        )
    if semantic_declaration_non_authority_guardrail is None:
        semantic_declaration_non_authority_guardrail = (
            derive_v85a_repo_semantic_declaration_non_authority_guardrail(
                semantic_declaration_source_index=semantic_declaration_source_index,
                turn_semantic_declaration_request=turn_semantic_declaration_request,
            )
        )
    session = turn_semantic_declaration_request.declaration_request_rows[
        0
    ].semantic_declaration_session_ref
    payload = {
        "schema": REPO_SEMANTIC_OPERATOR_CLASS_REGISTRY_SCHEMA,
        "semantic_operator_class_registry_id": "",
        "semantic_declaration_source_index_id": (
            semantic_declaration_source_index.semantic_declaration_source_index_id
        ),
        "turn_semantic_declaration_request_id": (
            turn_semantic_declaration_request.turn_semantic_declaration_request_id
        ),
        "semantic_declaration_non_authority_guardrail_id": (
            semantic_declaration_non_authority_guardrail.semantic_declaration_non_authority_guardrail_id
        ),
        "review_id": "vNext+240",
        "snapshot_id": "vNext+240-semantic-lookup-start",
        "source_set_id": "source-set:v85b:canonical-lookup-registry",
        "registry_rows": _v85b_registry_rows(session),
        "registry_summary": (
            "V85-B registry binds operators and classes for lookup review with "
            "no obligation expansion."
        ),
    }
    payload["semantic_operator_class_registry_id"] = _surface_id(
        "repo_semantic_operator_class_registry",
        REPO_SEMANTIC_OPERATOR_CLASS_REGISTRY_SCHEMA,
        payload,
        "semantic_operator_class_registry_id",
    )
    return RepoSemanticOperatorClassRegistry.model_validate(payload)


def derive_v85b_repo_obligation_family_registry(
    *,
    repo_root: Path | None = None,
    semantic_declaration_source_index: RepoSemanticDeclarationSourceIndex | None = None,
    turn_semantic_declaration_request: RepoTurnSemanticDeclarationRequest | None = None,
    semantic_declaration_non_authority_guardrail: (
        RepoSemanticDeclarationNonAuthorityGuardrail | None
    ) = None,
) -> RepoObligationFamilyRegistry:
    _ = repo_root
    if semantic_declaration_source_index is None:
        semantic_declaration_source_index = derive_v85a_repo_semantic_declaration_source_index()
    if turn_semantic_declaration_request is None:
        turn_semantic_declaration_request = derive_v85a_repo_turn_semantic_declaration_request(
            semantic_declaration_source_index=semantic_declaration_source_index
        )
    if semantic_declaration_non_authority_guardrail is None:
        semantic_declaration_non_authority_guardrail = (
            derive_v85a_repo_semantic_declaration_non_authority_guardrail(
                semantic_declaration_source_index=semantic_declaration_source_index,
                turn_semantic_declaration_request=turn_semantic_declaration_request,
            )
        )
    session = turn_semantic_declaration_request.declaration_request_rows[
        0
    ].semantic_declaration_session_ref
    payload = {
        "schema": REPO_OBLIGATION_FAMILY_REGISTRY_SCHEMA,
        "obligation_family_registry_id": "",
        "semantic_declaration_source_index_id": (
            semantic_declaration_source_index.semantic_declaration_source_index_id
        ),
        "turn_semantic_declaration_request_id": (
            turn_semantic_declaration_request.turn_semantic_declaration_request_id
        ),
        "semantic_declaration_non_authority_guardrail_id": (
            semantic_declaration_non_authority_guardrail.semantic_declaration_non_authority_guardrail_id
        ),
        "review_id": "vNext+240",
        "snapshot_id": "vNext+240-semantic-lookup-start",
        "source_set_id": "source-set:v85b:canonical-lookup-registry",
        "obligation_family_rows": _v85b_obligation_family_rows(session),
        "obligation_family_registry_summary": (
            "V85-B obligation family registry names families for review with "
            "no implementation and no obligation expansion."
        ),
    }
    payload["obligation_family_registry_id"] = _surface_id(
        "repo_obligation_family_registry",
        REPO_OBLIGATION_FAMILY_REGISTRY_SCHEMA,
        payload,
        "obligation_family_registry_id",
    )
    return RepoObligationFamilyRegistry.model_validate(payload)


def _v85b_lookup_rows(
    *,
    session: str,
    candidate_ref: str,
) -> list[dict[str, object]]:
    source_refs = _v85b_base_source_refs()
    explicit_obligation_refs = [
        "obligation-family:v85b:birth_continuation_death_algebra@v1",
        "obligation-family:v85b:failure_path_fail_closed@v1",
        "obligation-family:v85b:rollback_cleanup_teardown@v1",
        "obligation-family:v85b:stateful_lifecycle@v1",
    ]
    return sorted(
        [
            {
                "lookup_ref": "lookup:v85b:create-ui-menu",
                "semantic_declaration_session_ref": session,
                "candidate_ref": candidate_ref,
                "declaration_request_refs": [
                    "declaration-request:v85a:intent-to-declaration-office"
                ],
                "source_refs": source_refs,
                "semantic_pointer": "CREATE ui.menu@v1",
                "semantic_pointer_rows": [
                    _semantic_pointer_row(
                        pointer_ref="pointer:v85b:create-ui-menu",
                        session=session,
                        raw_pointer="CREATE ui.menu@v1",
                        parsed_operator="CREATE",
                        parsed_class="ui.menu@v1",
                        parsed_version="v1",
                    )
                ],
                "operator_registry_refs": ["registry:v85b:operator:CREATE"],
                "class_registry_refs": ["registry:v85b:object_class:ui.menu@v1"],
                "obligation_family_refs": explicit_obligation_refs,
                "lookup_input_kind": "explicit_semantic_pointer",
                "lookup_posture": "exact_match_for_review_only",
                "canonical_lookup_status": "exact_match_for_review_only",
                "pointer_competency_kind": "explicit_pointer_lookup",
                "competency_claim_horizon": "exact_lookup_only",
                "order_preservation_posture": "order_preserved_for_review",
                "duplicate_preservation_posture": "duplicates_not_present",
                "unknown_pointer_posture": "unknown_pointer_not_present",
                "conflict_posture": "no_conflict",
                "obligation_expansion_posture": "named_for_later_expansion_only",
                "non_authority_guardrail_refs": ["guardrail:v85a:intent-to-declaration-office"],
                "limitation_note": (
                    "Explicit semantic lookup is exact for review with no obligation expansion."
                ),
            },
            {
                "lookup_ref": "lookup:v85b:opaque-m42-sequence",
                "semantic_declaration_session_ref": session,
                "candidate_ref": candidate_ref,
                "declaration_request_refs": [
                    "declaration-request:v85a:intent-to-declaration-office"
                ],
                "source_refs": source_refs,
                "semantic_pointer": "M-42",
                "semantic_pointer_rows": [
                    _semantic_pointer_row(
                        pointer_ref="pointer:v85b:opaque:M-42",
                        session=session,
                        raw_pointer="M-42",
                        parsed_operator="OPAQUE",
                        parsed_class="M-42",
                        parsed_version="opaque",
                    )
                ],
                "operator_registry_refs": [],
                "class_registry_refs": [],
                "obligation_family_refs": [],
                "lookup_input_kind": "opaque_pointer",
                "lookup_posture": "exact_match_for_review_only",
                "canonical_lookup_status": "exact_match_for_review_only",
                "pointer_competency_kind": "opaque_pointer_obedience",
                "competency_claim_horizon": "pointer_obedience_only",
                "order_preservation_posture": "order_preserved_for_review",
                "duplicate_preservation_posture": "duplicates_preserved_for_review",
                "unknown_pointer_posture": "unknown_pointer_not_present",
                "conflict_posture": "no_conflict",
                "obligation_expansion_posture": "lookup_result_only",
                "non_authority_guardrail_refs": ["guardrail:v85a:intent-to-declaration-office"],
                "limitation_note": (
                    "Opaque lookup records pointer obedience for review "
                    "with no obligation expansion."
                ),
            },
            {
                "lookup_ref": "lookup:v85b:unknown-class-registry-gap",
                "semantic_declaration_session_ref": session,
                "candidate_ref": candidate_ref,
                "declaration_request_refs": ["declaration-request:v85a:unknown-class-registry-gap"],
                "source_refs": source_refs,
                "semantic_pointer": "CREATE unknown.widget@v9",
                "semantic_pointer_rows": [
                    _semantic_pointer_row(
                        pointer_ref="pointer:v85b:unknown-widget",
                        session=session,
                        raw_pointer="CREATE unknown.widget@v9",
                        parsed_operator="CREATE",
                        parsed_class="unknown.widget@v9",
                        parsed_version="v9",
                        pointer_parse_posture="unknown_class",
                        normalization_posture="normalization_rejected",
                    )
                ],
                "operator_registry_refs": ["registry:v85b:operator:CREATE"],
                "class_registry_refs": [],
                "obligation_family_refs": [],
                "lookup_input_kind": "registry_gap_candidate",
                "lookup_posture": "registry_gap",
                "canonical_lookup_status": "registry_gap",
                "pointer_competency_kind": "registry_gap_detection",
                "competency_claim_horizon": "natural_binding_not_claimed",
                "order_preservation_posture": "order_preserved_for_review",
                "duplicate_preservation_posture": "duplicates_not_present",
                "unknown_pointer_posture": "unknown_pointer_registry_gap",
                "conflict_posture": "conflict_blocked_by_registry_gap",
                "obligation_expansion_posture": "expansion_blocked_by_registry_gap",
                "non_authority_guardrail_refs": ["guardrail:v85a:unknown-class-registry-gap"],
                "limitation_note": (
                    "Unknown class lookup routes to registry-gap review "
                    "with no obligation expansion."
                ),
            },
        ],
        key=lambda row: str(row["lookup_ref"]),
    )


def derive_v85b_repo_canonical_meta_lookup_index(
    *,
    repo_root: Path | None = None,
    semantic_declaration_source_index: RepoSemanticDeclarationSourceIndex | None = None,
    turn_semantic_declaration_request: RepoTurnSemanticDeclarationRequest | None = None,
    semantic_declaration_non_authority_guardrail: (
        RepoSemanticDeclarationNonAuthorityGuardrail | None
    ) = None,
) -> RepoCanonicalMetaLookupIndex:
    _ = repo_root
    if semantic_declaration_source_index is None:
        semantic_declaration_source_index = derive_v85a_repo_semantic_declaration_source_index()
    if turn_semantic_declaration_request is None:
        turn_semantic_declaration_request = derive_v85a_repo_turn_semantic_declaration_request(
            semantic_declaration_source_index=semantic_declaration_source_index
        )
    if semantic_declaration_non_authority_guardrail is None:
        semantic_declaration_non_authority_guardrail = (
            derive_v85a_repo_semantic_declaration_non_authority_guardrail(
                semantic_declaration_source_index=semantic_declaration_source_index,
                turn_semantic_declaration_request=turn_semantic_declaration_request,
            )
        )
    session = turn_semantic_declaration_request.declaration_request_rows[
        0
    ].semantic_declaration_session_ref
    candidate_ref = turn_semantic_declaration_request.declaration_request_rows[0].candidate_ref
    payload = {
        "schema": REPO_CANONICAL_META_LOOKUP_INDEX_SCHEMA,
        "canonical_meta_lookup_index_id": "",
        "semantic_declaration_source_index_id": (
            semantic_declaration_source_index.semantic_declaration_source_index_id
        ),
        "turn_semantic_declaration_request_id": (
            turn_semantic_declaration_request.turn_semantic_declaration_request_id
        ),
        "semantic_declaration_non_authority_guardrail_id": (
            semantic_declaration_non_authority_guardrail.semantic_declaration_non_authority_guardrail_id
        ),
        "review_id": "vNext+240",
        "snapshot_id": "vNext+240-semantic-lookup-start",
        "source_set_id": "source-set:v85b:canonical-lookup-registry",
        "lookup_rows": _v85b_lookup_rows(session=session, candidate_ref=candidate_ref),
        "lookup_summary": (
            "V85-B canonical lookup rows are for review with no obligation expansion."
        ),
    }
    payload["canonical_meta_lookup_index_id"] = _surface_id(
        "repo_canonical_meta_lookup_index",
        REPO_CANONICAL_META_LOOKUP_INDEX_SCHEMA,
        payload,
        "canonical_meta_lookup_index_id",
    )
    return RepoCanonicalMetaLookupIndex.model_validate(payload)


def derive_v85b_repo_semantic_pointer_lookup_fixture(
    *,
    repo_root: Path | None = None,
    semantic_declaration_source_index: RepoSemanticDeclarationSourceIndex | None = None,
    turn_semantic_declaration_request: RepoTurnSemanticDeclarationRequest | None = None,
    semantic_declaration_non_authority_guardrail: (
        RepoSemanticDeclarationNonAuthorityGuardrail | None
    ) = None,
    canonical_meta_lookup_index: RepoCanonicalMetaLookupIndex | None = None,
    semantic_operator_class_registry: RepoSemanticOperatorClassRegistry | None = None,
    obligation_family_registry: RepoObligationFamilyRegistry | None = None,
) -> RepoSemanticPointerLookupFixture:
    _ = repo_root
    if semantic_declaration_source_index is None:
        semantic_declaration_source_index = derive_v85a_repo_semantic_declaration_source_index()
    if turn_semantic_declaration_request is None:
        turn_semantic_declaration_request = derive_v85a_repo_turn_semantic_declaration_request(
            semantic_declaration_source_index=semantic_declaration_source_index
        )
    if semantic_declaration_non_authority_guardrail is None:
        semantic_declaration_non_authority_guardrail = (
            derive_v85a_repo_semantic_declaration_non_authority_guardrail(
                semantic_declaration_source_index=semantic_declaration_source_index,
                turn_semantic_declaration_request=turn_semantic_declaration_request,
            )
        )
    if canonical_meta_lookup_index is None:
        canonical_meta_lookup_index = derive_v85b_repo_canonical_meta_lookup_index(
            semantic_declaration_source_index=semantic_declaration_source_index,
            turn_semantic_declaration_request=turn_semantic_declaration_request,
            semantic_declaration_non_authority_guardrail=semantic_declaration_non_authority_guardrail,
        )
    if semantic_operator_class_registry is None:
        semantic_operator_class_registry = derive_v85b_repo_semantic_operator_class_registry(
            semantic_declaration_source_index=semantic_declaration_source_index,
            turn_semantic_declaration_request=turn_semantic_declaration_request,
            semantic_declaration_non_authority_guardrail=semantic_declaration_non_authority_guardrail,
        )
    if obligation_family_registry is None:
        obligation_family_registry = derive_v85b_repo_obligation_family_registry(
            semantic_declaration_source_index=semantic_declaration_source_index,
            turn_semantic_declaration_request=turn_semantic_declaration_request,
            semantic_declaration_non_authority_guardrail=semantic_declaration_non_authority_guardrail,
        )
    session = turn_semantic_declaration_request.declaration_request_rows[
        0
    ].semantic_declaration_session_ref
    source_refs = _v85b_base_source_refs()
    payload = {
        "schema": REPO_SEMANTIC_POINTER_LOOKUP_FIXTURE_SCHEMA,
        "semantic_pointer_lookup_fixture_id": "",
        "canonical_meta_lookup_index_id": (
            canonical_meta_lookup_index.canonical_meta_lookup_index_id
        ),
        "semantic_operator_class_registry_id": (
            semantic_operator_class_registry.semantic_operator_class_registry_id
        ),
        "obligation_family_registry_id": obligation_family_registry.obligation_family_registry_id,
        "semantic_declaration_source_index_id": (
            semantic_declaration_source_index.semantic_declaration_source_index_id
        ),
        "turn_semantic_declaration_request_id": (
            turn_semantic_declaration_request.turn_semantic_declaration_request_id
        ),
        "semantic_declaration_non_authority_guardrail_id": (
            semantic_declaration_non_authority_guardrail.semantic_declaration_non_authority_guardrail_id
        ),
        "review_id": "vNext+240",
        "snapshot_id": "vNext+240-semantic-lookup-start",
        "source_set_id": "source-set:v85b:canonical-lookup-registry",
        "lookup_fixture_rows": [
            {
                "lookup_fixture_ref": "lookup-fixture:v85b:explicit-create-ui-menu",
                "semantic_declaration_session_ref": session,
                "source_refs": source_refs,
                "fixture_kind": "explicit_semantic_pointer_lookup",
                "pointer_competency_kind": "explicit_pointer_lookup",
                "competency_claim_horizon": "exact_lookup_only",
                "input_pointer_rows": [
                    _semantic_pointer_row(
                        pointer_ref="pointer:v85b:fixture:create-ui-menu",
                        session=session,
                        raw_pointer="CREATE ui.menu@v1",
                        parsed_operator="CREATE",
                        parsed_class="ui.menu@v1",
                        parsed_version="v1",
                    )
                ],
                "expected_lookup_rows": [
                    "obligation-family:v85b:birth_continuation_death_algebra@v1",
                    "obligation-family:v85b:failure_path_fail_closed@v1",
                    "obligation-family:v85b:rollback_cleanup_teardown@v1",
                    "obligation-family:v85b:stateful_lifecycle@v1",
                ],
                "expected_order_posture": "order_preserved",
                "expected_duplicate_posture": "duplicates_absent",
                "expected_unknown_posture": "unknown_absent",
                "expected_conflict_posture": "conflict_absent",
                "actual_result_refs": ["lookup:v85b:create-ui-menu"],
                "fixture_posture": "fixture_passes_for_review_only",
                "non_authority_guardrail_refs": ["guardrail:v85a:intent-to-declaration-office"],
                "limitation_note": ("Explicit semantic fixture is for lookup review only."),
            },
            {
                "lookup_fixture_ref": "lookup-fixture:v85b:opaque-m42-sequence",
                "semantic_declaration_session_ref": session,
                "source_refs": source_refs,
                "fixture_kind": "opaque_pointer_exact_lookup",
                "pointer_competency_kind": "opaque_pointer_obedience",
                "competency_claim_horizon": "pointer_obedience_only",
                "input_pointer_rows": [
                    _semantic_pointer_row(
                        pointer_ref=f"pointer:v85b:fixture:opaque:{raw}",
                        session=session,
                        raw_pointer=raw,
                        parsed_operator="OPAQUE",
                        parsed_class=raw,
                        parsed_version="opaque",
                    )
                    for raw in ["M-42", "A1", "A9", "C4", "Z2"]
                ],
                "expected_lookup_rows": ["A1", "A9", "C4", "Z2"],
                "expected_order_posture": "order_preserved",
                "expected_duplicate_posture": "duplicates_preserved",
                "expected_unknown_posture": "unknown_absent",
                "expected_conflict_posture": "conflict_absent",
                "actual_result_refs": ["lookup:v85b:opaque-m42-sequence"],
                "fixture_posture": "fixture_passes_for_review_only",
                "non_authority_guardrail_refs": ["guardrail:v85a:intent-to-declaration-office"],
                "limitation_note": "Opaque pointer fixture proves obedience for review only.",
            },
            {
                "lookup_fixture_ref": "lookup-fixture:v85b:unknown-class-abstain",
                "semantic_declaration_session_ref": session,
                "source_refs": source_refs,
                "fixture_kind": "explicit_semantic_pointer_registry_gap",
                "pointer_competency_kind": "registry_gap_detection",
                "competency_claim_horizon": "natural_binding_not_claimed",
                "input_pointer_rows": [
                    _semantic_pointer_row(
                        pointer_ref="pointer:v85b:fixture:unknown-widget",
                        session=session,
                        raw_pointer="CREATE unknown.widget@v9",
                        parsed_operator="CREATE",
                        parsed_class="unknown.widget@v9",
                        parsed_version="v9",
                        pointer_parse_posture="unknown_class",
                        normalization_posture="normalization_rejected",
                    )
                ],
                "expected_lookup_rows": [],
                "expected_order_posture": "order_preserved",
                "expected_duplicate_posture": "duplicates_absent",
                "expected_unknown_posture": "unknown_registry_gap",
                "expected_conflict_posture": "conflict_absent",
                "actual_result_refs": ["lookup:v85b:unknown-class-registry-gap"],
                "fixture_posture": "fixture_records_registry_gap",
                "non_authority_guardrail_refs": ["guardrail:v85a:unknown-class-registry-gap"],
                "limitation_note": "Unknown class fixture routes to registry-gap review.",
            },
        ],
        "lookup_fixture_summary": (
            "V85-B pointer fixtures prove lookup behavior for review with no implementation."
        ),
    }
    payload["semantic_pointer_lookup_fixture_id"] = _surface_id(
        "repo_semantic_pointer_lookup_fixture",
        REPO_SEMANTIC_POINTER_LOOKUP_FIXTURE_SCHEMA,
        payload,
        "semantic_pointer_lookup_fixture_id",
    )
    return RepoSemanticPointerLookupFixture.model_validate(payload)


def validate_v85b_semantic_lookup_registry_bundle(
    *,
    semantic_declaration_source_index: RepoSemanticDeclarationSourceIndex,
    turn_semantic_declaration_request: RepoTurnSemanticDeclarationRequest,
    semantic_declaration_non_authority_guardrail: RepoSemanticDeclarationNonAuthorityGuardrail,
    canonical_meta_lookup_index: RepoCanonicalMetaLookupIndex,
    semantic_operator_class_registry: RepoSemanticOperatorClassRegistry,
    obligation_family_registry: RepoObligationFamilyRegistry,
    semantic_pointer_lookup_fixture: RepoSemanticPointerLookupFixture,
) -> None:
    if (
        canonical_meta_lookup_index.semantic_declaration_source_index_id
        != semantic_declaration_source_index.semantic_declaration_source_index_id
        or semantic_operator_class_registry.semantic_declaration_source_index_id
        != semantic_declaration_source_index.semantic_declaration_source_index_id
        or obligation_family_registry.semantic_declaration_source_index_id
        != semantic_declaration_source_index.semantic_declaration_source_index_id
        or semantic_pointer_lookup_fixture.semantic_declaration_source_index_id
        != semantic_declaration_source_index.semantic_declaration_source_index_id
    ):
        raise ValueError("V85-B surfaces must reference released V85-A source index")
    if (
        canonical_meta_lookup_index.turn_semantic_declaration_request_id
        != turn_semantic_declaration_request.turn_semantic_declaration_request_id
        or semantic_operator_class_registry.turn_semantic_declaration_request_id
        != turn_semantic_declaration_request.turn_semantic_declaration_request_id
        or obligation_family_registry.turn_semantic_declaration_request_id
        != turn_semantic_declaration_request.turn_semantic_declaration_request_id
        or semantic_pointer_lookup_fixture.turn_semantic_declaration_request_id
        != turn_semantic_declaration_request.turn_semantic_declaration_request_id
    ):
        raise ValueError("V85-B surfaces must reference released V85-A request")
    guardrail_id = (
        semantic_declaration_non_authority_guardrail.semantic_declaration_non_authority_guardrail_id
    )
    if (
        canonical_meta_lookup_index.semantic_declaration_non_authority_guardrail_id
        != guardrail_id
        or semantic_operator_class_registry.semantic_declaration_non_authority_guardrail_id
        != guardrail_id
        or obligation_family_registry.semantic_declaration_non_authority_guardrail_id
        != guardrail_id
        or semantic_pointer_lookup_fixture.semantic_declaration_non_authority_guardrail_id
        != guardrail_id
    ):
        raise ValueError("V85-B surfaces must reference released V85-A guardrail")
    shared = {
        canonical_meta_lookup_index.review_id,
        semantic_operator_class_registry.review_id,
        obligation_family_registry.review_id,
        semantic_pointer_lookup_fixture.review_id,
    }
    if shared != {"vNext+240"}:
        raise ValueError("V85-B surfaces must share vNext+240 review id")

    known_requests = {
        row.declaration_request_ref: row
        for row in turn_semantic_declaration_request.declaration_request_rows
    }
    known_guardrails = {
        row.guardrail_ref: row
        for row in semantic_declaration_non_authority_guardrail.guardrail_rows
    }
    known_registry_refs = {
        row.registry_ref for row in semantic_operator_class_registry.registry_rows
    }
    known_aliases = {
        alias.alias_value
        for row in semantic_operator_class_registry.registry_rows
        for alias in row.alias_rows
    }
    known_obligation_refs = {
        row.obligation_family_ref for row in obligation_family_registry.obligation_family_rows
    }
    known_lookup_refs = {row.lookup_ref for row in canonical_meta_lookup_index.lookup_rows}
    known_sessions = {
        row.semantic_declaration_session_ref
        for row in turn_semantic_declaration_request.declaration_request_rows
    }
    known_candidates = {
        row.candidate_ref for row in turn_semantic_declaration_request.declaration_request_rows
    }

    for registry_row in semantic_operator_class_registry.registry_rows:
        if registry_row.semantic_declaration_session_ref not in known_sessions:
            raise ValueError("registry rows must use released declaration session")
    for obligation_row in obligation_family_registry.obligation_family_rows:
        if obligation_row.semantic_declaration_session_ref not in known_sessions:
            raise ValueError("obligation rows must use released declaration session")
        if any(ref not in known_registry_refs for ref in obligation_row.applies_to_operator_refs):
            raise ValueError("obligation operator applicability refs must resolve")
        if any(ref not in known_registry_refs for ref in obligation_row.applies_to_class_refs):
            raise ValueError("obligation class applicability refs must resolve")
    for lookup_row in canonical_meta_lookup_index.lookup_rows:
        if lookup_row.semantic_declaration_session_ref not in known_sessions:
            raise ValueError("lookup rows must use released declaration session")
        if lookup_row.candidate_ref not in known_candidates:
            raise ValueError("lookup rows must use released candidate")
        if any(ref not in known_requests for ref in lookup_row.declaration_request_refs):
            raise ValueError("lookup request refs must resolve to released V85-A requests")
        if any(ref not in known_guardrails for ref in lookup_row.non_authority_guardrail_refs):
            raise ValueError("lookup guardrail refs must resolve to released V85-A guardrails")
        if any(ref not in known_registry_refs for ref in lookup_row.operator_registry_refs):
            raise ValueError("lookup operator registry refs must resolve")
        if any(ref not in known_registry_refs for ref in lookup_row.class_registry_refs):
            raise ValueError("lookup class registry refs must resolve")
        if any(ref not in known_obligation_refs for ref in lookup_row.obligation_family_refs):
            raise ValueError("lookup obligation family refs must resolve")
        for pointer_row in lookup_row.semantic_pointer_rows:
            if pointer_row.pointer_parse_posture == "parsed_with_alias":
                raw_parts = pointer_row.raw_pointer.split(maxsplit=1)
                raw_class = raw_parts[1] if len(raw_parts) == 2 else pointer_row.raw_pointer
                if raw_class not in known_aliases:
                    raise ValueError("alias pointer lookup requires a registry alias row")
        if (
            lookup_row.lookup_input_kind != "opaque_pointer"
            and lookup_row.lookup_posture == "exact_match_for_review_only"
            and not lookup_row.obligation_family_refs
        ):
            raise ValueError("semantic exact lookup must name future obligation families")
    for fixture_row in semantic_pointer_lookup_fixture.lookup_fixture_rows:
        if fixture_row.semantic_declaration_session_ref not in known_sessions:
            raise ValueError("fixture rows must use released declaration session")
        if any(ref not in known_guardrails for ref in fixture_row.non_authority_guardrail_refs):
            raise ValueError("fixture guardrail refs must resolve to released V85-A guardrails")
        if any(ref not in known_lookup_refs for ref in fixture_row.actual_result_refs):
            raise ValueError("fixture actual result refs must resolve to lookup rows")
        if (
            fixture_row.fixture_kind.startswith("opaque_pointer")
            and fixture_row.competency_claim_horizon != "pointer_obedience_only"
        ):
            raise ValueError("opaque fixtures cannot claim natural semantic binding")


def derive_v85b_semantic_lookup_registry_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoSemanticDeclarationSourceIndex,
    RepoTurnSemanticDeclarationRequest,
    RepoSemanticDeclarationNonAuthorityGuardrail,
    RepoCanonicalMetaLookupIndex,
    RepoSemanticOperatorClassRegistry,
    RepoObligationFamilyRegistry,
    RepoSemanticPointerLookupFixture,
]:
    (
        _v84_readiness_summary,
        _v84_handoff,
        _v84_closeout,
        source_index,
        request,
        guardrail,
    ) = derive_v85a_semantic_declaration_review_bundle(repo_root=repo_root)
    lookup_index = derive_v85b_repo_canonical_meta_lookup_index(
        repo_root=repo_root,
        semantic_declaration_source_index=source_index,
        turn_semantic_declaration_request=request,
        semantic_declaration_non_authority_guardrail=guardrail,
    )
    registry = derive_v85b_repo_semantic_operator_class_registry(
        repo_root=repo_root,
        semantic_declaration_source_index=source_index,
        turn_semantic_declaration_request=request,
        semantic_declaration_non_authority_guardrail=guardrail,
    )
    obligation_registry = derive_v85b_repo_obligation_family_registry(
        repo_root=repo_root,
        semantic_declaration_source_index=source_index,
        turn_semantic_declaration_request=request,
        semantic_declaration_non_authority_guardrail=guardrail,
    )
    fixture = derive_v85b_repo_semantic_pointer_lookup_fixture(
        repo_root=repo_root,
        semantic_declaration_source_index=source_index,
        turn_semantic_declaration_request=request,
        semantic_declaration_non_authority_guardrail=guardrail,
        canonical_meta_lookup_index=lookup_index,
        semantic_operator_class_registry=registry,
        obligation_family_registry=obligation_registry,
    )
    validate_v85b_semantic_lookup_registry_bundle(
        semantic_declaration_source_index=source_index,
        turn_semantic_declaration_request=request,
        semantic_declaration_non_authority_guardrail=guardrail,
        canonical_meta_lookup_index=lookup_index,
        semantic_operator_class_registry=registry,
        obligation_family_registry=obligation_registry,
        semantic_pointer_lookup_fixture=fixture,
    )
    return (
        source_index,
        request,
        guardrail,
        lookup_index,
        registry,
        obligation_registry,
        fixture,
    )
