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
from .candidate_review_classification import _surface_id
from .recursive_candidate_intake import (
    CandidateAuthorityLayer,
    CandidateSourceKind,
    CandidateSourcePresencePosture,
    OdeuLane,
)

REPO_SEMANTIC_INTENT_CONTRACT_SCHEMA = "repo_semantic_intent_contract@1"
REPO_INTENT_SOURCE_INDEX_SCHEMA = "repo_intent_source_index@1"
REPO_INTENT_NON_IMPLEMENTATION_GUARDRAIL_SCHEMA = "repo_intent_non_implementation_guardrail@1"
REPO_INTENT_EDGE_DECOMPOSITION_SCHEMA = "repo_intent_edge_decomposition@1"
REPO_ARTIFACT_OBLIGATION_MAP_SCHEMA = "repo_artifact_obligation_map@1"
REPO_SEMANTIC_DRIFT_AMBIGUITY_REGISTER_SCHEMA = "repo_semantic_drift_ambiguity_register@1"
REPO_IMPLEMENTATION_SPEC_PROJECTION_PACKET_SCHEMA = "repo_implementation_spec_projection_packet@1"
REPO_INTENT_TO_WORK_PACKET_HANDOFF_SCHEMA = "repo_intent_to_work_packet_handoff@1"
REPO_SEMANTIC_IMPLEMENTATION_SPEC_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA = (
    "repo_semantic_implementation_spec_family_closeout_alignment@1"
)

IntentSourceRole = Literal[
    "v82_closeout_source",
    "v82_summary_source",
    "v82_handoff_source",
    "combined_dogfood_source",
    "operator_intent_source",
    "repo_planning_source",
    "repo_architecture_source",
    "repo_support_doctrine_source",
    "morphic_ux_support_source",
    "external_meta_orchestrator_support_source",
    "external_oai_profile_support_source",
    "model_generated_spec_candidate_source",
    "agent_generated_spec_candidate_source",
    "reviewer_amendment_source",
    "operator_revision_source",
    "prompt_context_source",
    "model_or_agent_profile_source",
    "implementation_prior_artifact_source",
    "implementation_context_source",
    "authority_boundary_source",
    "non_goal_source",
    "explicit_absence_marker",
    "support_process_context",
]
IntentSourceCurrentness = Literal[
    "current_concrete_source",
    "explicit_absence_marker",
    "historical_context_only",
    "stale_or_superseded",
    "unknown_needs_review",
]
IntentSourceScopePosture = Literal[
    "bounded_to_semantic_intent_review",
    "context_only",
    "external_import_required",
    "absence_marker",
    "future_family_only",
]
IntentSourceImportPosture = Literal[
    "repo_owned_source",
    "external_support_source",
    "external_import_required_before_lock",
    "support_context_only",
    "absence_marker",
    "unknown_needs_review",
]
GenerationPosture = Literal[
    "not_generated",
    "generated_for_review_only",
    "generated_from_bounded_context",
    "generated_from_unbounded_context",
    "generated_source_missing",
    "generated_source_unknown",
]
ModelAgentAuthorityPosture = Literal[
    "no_model_authority",
    "model_output_as_candidate_only",
    "agent_output_as_candidate_only",
    "reviewer_output_as_review_only",
    "authority_requires_later_lock",
]
IntentRevisionPosture = Literal[
    "initial_intent_version",
    "operator_revision_recorded",
    "reviewer_amendment_recorded",
    "generated_candidate_revision_recorded",
    "revision_requires_later_review",
]
ArtifactFamilyHorizon = Literal[
    "repo_code_implementation_spec",
    "repo_schema_implementation_spec",
    "repo_fixture_test_spec",
    "repo_docs_support_spec",
    "morphic_ux_projection_spec",
    "direct_oai_harness_spec",
    "workflow_orchestrator_spec",
    "general_digital_artifact_projection_future_family",
    "future_family_only",
]
ImplementationSurfaceHorizon = Literal[
    "repo_description_schema_surface",
    "repo_description_fixture_surface",
    "repo_description_test_surface",
    "repo_docs_support_surface",
    "morphic_ux_projection_surface",
    "direct_oai_harness_surface",
    "workflow_orchestrator_surface",
    "future_family_only",
]
SuccessHorizonKind = Literal[
    "schema_shape_success",
    "validator_behavior_success",
    "fixture_accept_reject_success",
    "workflow_transition_success",
    "ux_projection_success",
    "provider_capability_profile_success",
    "documentation_alignment_success",
    "implementation_packet_success",
    "future_family_only",
]
IntentRecordabilityPosture = Literal[
    "recordable_from_concrete_intent_source",
    "recordable_from_operator_turn_with_absence_markers",
    "recordable_from_support_context_only",
    "recordable_from_generated_spec_candidate",
    "not_recordable_missing_intent_source",
]
SemanticSpecEligibilityPosture = Literal[
    "eligible_for_semantic_spec_review",
    "blocked_by_missing_intent_source",
    "blocked_by_missing_non_goals",
    "blocked_by_missing_authority_boundary",
    "blocked_by_missing_success_horizon",
    "blocked_by_external_source_import_gap",
    "blocked_by_generated_spec_provenance_gap",
    "blocked_by_ambiguous_artifact_horizon",
    "future_family_only",
    "rejected_out_of_scope",
]
SemanticClosurePosture = Literal[
    "closure_not_claimed",
    "closure_candidate_for_review",
    "closure_blocked_by_missing_source",
    "closure_blocked_by_missing_scope_boundary",
    "closure_blocked_by_missing_non_goals",
    "closure_blocked_by_missing_authority_boundary",
    "closure_blocked_by_missing_success_horizon",
    "closure_blocked_by_generated_spec_provenance_gap",
    "future_family_only",
    "rejected_out_of_scope",
]
IntentScopePosture = Literal[
    "bounded_semantic_spec_review",
    "blocked_by_missing_scope_boundary",
    "context_only",
    "future_family_only",
    "rejected_out_of_scope",
]
ExpectedEdgeClass = Literal[
    "source_binding_edge",
    "non_goal_preservation_edge",
    "authority_boundary_edge",
    "success_horizon_edge",
    "target_surface_boundedness_edge",
    "validation_evidence_edge",
    "semantic_drift_edge",
    "future_family_boundary_edge",
]
ForbiddenImplementationAction = Literal[
    "edit_code",
    "write_implementation",
    "create_work_packet",
    "execute_work_packet",
    "open_pr",
    "commit_change",
    "merge_change",
]
ForbiddenRuntimeAction = Literal[
    "run_command",
    "invoke_tool_for_effect",
    "dispatch_worker",
    "mutate_meta_orchestrator_runtime",
    "change_morphic_ux_runtime",
    "activate_direct_oai_runtime",
]
ForbiddenSemanticDownstreamAuthority = Literal[
    "implementation_authority",
    "work_packet_authority",
    "runtime_authority",
    "dispatch_authority",
    "product_authorization",
    "release_authority",
    "graph_memory_authority",
    "recursive_policy_amendment",
    "v84_selection",
]
NonImplementationPosture = Literal["non_implementation_guardrail_active"]
NonExecutionPosture = Literal["non_execution_guardrail_active"]
NonDispatchPosture = Literal["non_dispatch_guardrail_active"]
NonReleasePosture = Literal["non_release_guardrail_active"]
SemanticObjectKind = Literal[
    "domain_object",
    "repo_module",
    "schema_surface",
    "fixture_surface",
    "test_surface",
    "doc_surface",
    "ux_surface",
    "workflow_surface",
    "provider_capability_surface",
    "authority_boundary",
    "non_goal",
    "future_family_surface",
]
SemanticTruthPosture = Literal[
    "not_truth_claim",
    "source_bound_claim_for_review",
    "candidate_only",
]
SemanticMutabilityPosture = Literal[
    "review_object_only",
    "target_requires_later_lock",
    "immutable_boundary",
]
SemanticAuthorityPosture = Literal[
    "no_authority_granted",
    "authority_boundary_only",
    "candidate_only_no_authority",
    "requires_later_lock",
]
SemanticRelationKind = Literal[
    "requires",
    "constrains",
    "forbids",
    "preserves",
    "realizes",
    "refines",
    "conflicts_with",
    "disambiguates",
    "supersedes",
    "non_goal_of",
    "authority_requires",
    "validation_requires",
    "acceptance_requires",
    "derives_from",
    "must_remain_distinct_from",
    "hands_off_to",
    "validates",
    "blocks",
    "future_family_only",
]
PreservationRequirement = Literal[
    "preserve_semantic_relation_for_review",
    "preserve_as_non_goal",
    "preserve_as_authority_boundary",
    "preserve_as_validation_need",
    "preserve_as_future_family_only",
]
ValidationKind = Literal[
    "schema_validation",
    "validator_behavior",
    "positive_fixture",
    "reject_fixture",
    "unit_test",
    "integration_test",
    "documentation_review",
    "semantic_review",
    "human_review",
    "tool_run_review",
    "future_family_review",
]
RequiredEvidenceKind = Literal[
    "schema",
    "validator",
    "positive_fixture",
    "reject_fixture",
    "unit_test",
    "integration_test",
    "documentation",
    "semantic_review",
    "human_review",
    "future_family_review",
]
FixturePosture = Literal[
    "required",
    "not_required",
    "requires_later_review",
]
ToolApplicabilityPosture = Literal[
    "not_applicable",
    "review_only",
    "requires_later_tool_permission",
]
AcceptanceNotTruthGuardrail = Literal["acceptance_evidence_is_not_semantic_truth"]
IntentEdgeDecompositionPosture = Literal[
    "edges_decomposed_for_review",
    "blocked_by_missing_intent_contract",
    "blocked_by_missing_source",
    "blocked_by_ambiguous_relation",
    "blocked_by_authority_gap",
    "future_family_only",
    "rejected_out_of_scope",
]
SemanticClosureReviewPosture = Literal[
    "closure_not_claimed",
    "edge_review_candidate_only",
    "blocked_by_missing_edge",
    "blocked_by_missing_validation_need",
    "future_family_only",
]
ArtifactKind = Literal[
    "code_module",
    "schema",
    "mirror_schema",
    "fixture",
    "reject_fixture",
    "test",
    "documentation",
    "support_artifact",
    "ux_projection_artifact",
    "provider_profile_artifact",
    "workflow_contract_artifact",
    "future_family_artifact",
]
RequiredChangePosture = Literal[
    "change_required_for_later_implementation_spec",
    "review_obligation_only_no_change",
    "future_family_only",
    "blocked_by_non_goal",
    "blocked_by_authority_gap",
]
RequiredArtifactPosture = Literal[
    "required_for_review",
    "not_applicable",
    "requires_later_review",
]
CoveragePosture = Literal[
    "obligations_cover_all_required_edges",
    "obligations_cover_with_nonblocking_warnings",
    "blocked_by_unmapped_edge",
    "blocked_by_unknown_target_surface",
    "blocked_by_missing_validation_need",
    "future_family_only",
    "rejected_out_of_scope",
]
ImplementationReadinessPosture = Literal[
    "not_ready_requires_projection_packet",
    "ready_for_projection_review_only",
    "blocked_by_semantic_drift",
    "blocked_by_ambiguity",
    "blocked_by_authority_gap",
    "future_family_only",
]
DriftKind = Literal[
    "missing_source",
    "ambiguous_intent",
    "ambiguous_artifact_horizon",
    "semantic_edge_unmapped",
    "implementation_target_overbroad",
    "implementation_target_underbroad",
    "non_goal_laundering",
    "authority_boundary_laundering",
    "test_coverage_mismatch",
    "fixture_coverage_mismatch",
    "morphic_ux_scope_drift",
    "direct_oai_runtime_scope_drift",
    "workflow_orchestrator_authority_drift",
    "future_family_pressure_unclassified",
]
DriftSeverityPosture = Literal["blocking", "warning", "informational"]
DriftBlockingPosture = Literal[
    "blocking",
    "warning_only",
    "carried_for_later_review",
    "not_applicable",
]
DriftRegisterBlockingPosture = Literal[
    "no_blockers",
    "warnings_only",
    "blocking_drift_visible",
    "future_family_only",
]
RequiredResolutionHorizon = Literal[
    "source_binding_review",
    "semantic_review",
    "artifact_obligation_review",
    "authority_boundary_review",
    "projection_packet_review",
    "future_family_review",
]
DriftRequiredNextSurface = Literal[
    "v83b_review_only",
    "v83c_projection_packet_review",
    "future_family_review",
    "blocked_until_source_added",
]
ProjectionPacketPosture = Literal[
    "projection_packet_ready_for_review",
    "projection_packet_ready_with_nonblocking_warnings",
    "blocked_by_missing_intent_contract",
    "blocked_by_missing_edge_decomposition",
    "blocked_by_missing_obligation_map",
    "blocked_by_semantic_drift",
    "blocked_by_authority_gap",
    "future_family_only",
    "rejected_out_of_scope",
]
SemanticCoveragePosture = Literal[
    "all_required_edges_covered",
    "covered_with_nonblocking_warnings",
    "blocked_by_uncovered_edge",
    "blocked_by_unvalidated_edge",
    "blocked_by_ambiguous_edge",
    "future_family_only",
]
ProjectionReadyBasisPosture = Literal[
    "ready_no_blockers",
    "ready_with_nonblocking_warnings",
    "not_ready_blockers_remain",
    "authority_review_requested_for_blockers",
    "future_family_only",
    "rejected_out_of_scope",
]
ProjectionActorKind = Literal[
    "human_operator",
    "model",
    "agent",
    "reviewer",
    "tool_assisted_review",
    "mixed",
    "unknown",
]
ProjectionGenerationScopePosture = Literal[
    "bounded_to_released_v83_inputs",
    "bounded_to_prompt_context",
    "unbounded_context_blocked",
    "generated_source_missing",
    "not_generated",
]
ProjectionReviewStatus = Literal[
    "candidate_unreviewed",
    "reviewed_for_source_binding",
    "reviewed_for_edge_coverage",
    "reviewed_for_artifact_obligation_coverage",
    "blocked_by_missing_context",
    "blocked_by_semantic_drift",
    "blocked_by_authority_gap",
]
ProjectionNonAuthorityPosture = Literal[
    "candidate_projection_only",
    "review_only_no_authority",
    "authority_requires_later_lock",
]
ImplementationExecutionPosture = Literal[
    "no_execution_performed_by_v83",
    "execution_requires_later_lock",
    "execution_forbidden_by_this_family",
]
ReviewCheckKind = Literal[
    "source_binding_check",
    "non_goal_preservation_check",
    "authority_boundary_check",
    "target_surface_boundedness_check",
    "edge_coverage_check",
    "validation_evidence_check",
    "reject_fixture_check",
    "generated_spec_provenance_check",
    "semantic_drift_check",
    "future_family_boundary_check",
]
ReviewCheckPosture = Literal[
    "passed_for_review_only",
    "blocked",
    "warning",
    "not_applicable",
    "requires_later_review",
]
ReviewCheckBlockingPosture = Literal["blocking", "warning_only", "not_applicable"]
QualityGatePosture = Literal[
    "ready_for_later_implementation_slice_review",
    "ready_with_nonblocking_warnings",
    "blocked_by_missing_source_binding",
    "blocked_by_uncovered_edge",
    "blocked_by_unbounded_target_surface",
    "blocked_by_missing_validation_evidence",
    "blocked_by_generated_spec_provenance_gap",
    "blocked_by_authority_gap",
    "future_family_only",
    "rejected_out_of_scope",
]
WorkPacketAuthorityPosture = Literal[
    "no_work_packet_authority_granted",
    "work_packet_requires_later_lock",
    "work_packet_review_only",
    "work_packet_forbidden_by_this_family",
]
ImplementationLockRequirement = Literal[
    "canonical_starter_lock_required",
    "later_selector_required",
    "maintainer_review_required",
    "future_family_only",
    "not_applicable",
]
WorkPacketHandoffTarget = Literal[
    "future_implementation_slice_review",
    "future_work_packet_review",
    "future_meta_orchestrator_workflow_review",
    "future_morphic_ux_projection_review",
    "future_direct_oai_harness_review",
    "future_general_digital_artifact_projection_review",
    "future_product_review",
    "future_graph_memory_review",
    "future_family_review",
    "deferred_no_selection",
]
WorkPacketHandoffSubjectHorizon = Literal[
    "implementation_spec_package",
    "code_implementation_spec",
    "schema_fixture_test_spec",
    "docs_support_spec",
    "ux_projection_spec",
    "provider_capability_profile_spec",
    "workflow_orchestrator_spec",
    "general_artifact_projection_pressure",
    "product_authority_gap",
    "graph_memory_pressure",
]
WorkPacketHandoffPosture = Literal[
    "ready_for_later_review",
    "ready_with_nonblocking_warnings",
    "blocked_by_projection_packet_gap",
    "blocked_by_authority_gap",
    "blocked_by_semantic_drift",
    "future_family_only",
    "rejected_out_of_scope",
]
MetaOrchestratorRuntimePosture = Literal[
    "no_meta_orchestrator_runtime_performed_by_v83",
    "workflow_transition_review_only",
    "runtime_requires_later_family",
    "not_applicable",
]
SemanticSpecClosedSlice = Literal["V83-A", "V83-B", "V83-C"]
SemanticSpecConsumedFamily = Literal[
    "V68",
    "V69",
    "V70",
    "V71",
    "V72",
    "V73",
    "V74",
    "V75",
    "V76",
    "V77",
    "V78",
    "V79",
    "V80",
    "V81",
    "V82",
    "V83",
]
SemanticSpecShippedRecordShape = Literal[
    "repo_semantic_intent_contract@1",
    "repo_intent_source_index@1",
    "repo_intent_non_implementation_guardrail@1",
    "repo_intent_edge_decomposition@1",
    "repo_artifact_obligation_map@1",
    "repo_semantic_drift_ambiguity_register@1",
    "repo_implementation_spec_projection_packet@1",
    "repo_intent_to_work_packet_handoff@1",
    "repo_semantic_implementation_spec_family_closeout_alignment@1",
]
SemanticSpecUnselectedFutureSurface = Literal[
    "code_implementation",
    "work_packet_execution",
    "meta_orchestrator_runtime",
    "morphic_ux_runtime_change",
    "direct_oai_runtime_behavior",
    "product_authorization",
    "release",
    "graph_memory_authority",
    "recursive_policy_amendment",
    "v84_selection",
]

_V82_ELIGIBILITY_SOURCE_ROLES = {
    "v82_summary_source",
    "v82_handoff_source",
    "v82_closeout_source",
}
_CONCRETE_INTENT_SOURCE_ROLES = {
    "operator_intent_source",
    "operator_revision_source",
    "repo_planning_source",
}
_SUPPORT_ONLY_SOURCE_ROLES = {
    "combined_dogfood_source",
    "repo_support_doctrine_source",
    "morphic_ux_support_source",
    "external_meta_orchestrator_support_source",
    "external_oai_profile_support_source",
    "support_process_context",
}
_GENERATED_SOURCE_ROLES = {
    "model_generated_spec_candidate_source",
    "agent_generated_spec_candidate_source",
}
_ABSENCE_SOURCE_ROLES = {"explicit_absence_marker"}
_FORBIDDEN_IMPLEMENTATION_ACTIONS = {
    "edit_code",
    "write_implementation",
    "create_work_packet",
    "execute_work_packet",
    "open_pr",
    "commit_change",
    "merge_change",
}
_FORBIDDEN_RUNTIME_ACTIONS = {
    "run_command",
    "invoke_tool_for_effect",
    "dispatch_worker",
    "mutate_meta_orchestrator_runtime",
    "change_morphic_ux_runtime",
    "activate_direct_oai_runtime",
}
_FORBIDDEN_DOWNSTREAM_AUTHORITIES = {
    "implementation_authority",
    "work_packet_authority",
    "runtime_authority",
    "dispatch_authority",
    "product_authorization",
    "release_authority",
    "graph_memory_authority",
    "recursive_policy_amendment",
    "v84_selection",
}
_BROAD_ARTIFACT_TARGETS = {
    ".",
    "packages",
    "packages/adeu_repo_description",
    "packages/adeu_repo_description/src",
    "apps",
    "docs",
}


def _source_path(path: str) -> str:
    _repo_ref(path, field_name="source_ref")
    return path


def _require_terms(value: str, *, field_name: str, terms: tuple[str, ...]) -> str:
    lowered = value.lower()
    missing = [term for term in terms if term not in lowered]
    if missing:
        raise ValueError(f"{field_name} must mention {', '.join(missing)}")
    return value


def _reject_v83_action_claim(value: str, *, field_name: str) -> str:
    lowered = value.lower()
    forbidden_patterns = [
        r"\bimplemented\b",
        r"\bimplementation truth\b",
        r"\bcode correctness\b",
        r"\bready to implement now\b",
        r"\bwork[- ]packet (?:executed|authority granted)\b",
        r"\bcommand (?:executed|run)\b",
        r"\btool (?:invoked|executed)\b",
        r"\bworker (?:assigned|dispatched)\b",
        r"\bmeta[- ]orchestrator runtime (?:mutated|transitioned)\b",
        r"\bmorphic ux runtime (?:changed|updated)\b",
        r"\bdirect oai runtime (?:activated|changed)\b",
        r"\bpr (?:created|opened)\b",
        r"\bcommit(?:ted)? (?:changes|code|diff|implementation|work|to main)\b",
        r"\bmerge(?:d)? (?:pr|pull request|branch|changes)\b",
        r"\brelease(?:d)? (?:artifact|authority|build|package|truth|version)\b",
        r"\bproduct (?:authorized|authorization)\b",
        r"\bgraph[- ]memory authority\b",
        r"\brecursive policy (?:amended|amendment)\b",
        r"\bv84 (?:selected|selection)\b",
    ]

    def is_negated(match: re.Match[str]) -> bool:
        prefix = lowered[max(0, match.start() - 24) : match.start()]
        suffix = lowered[match.end() : min(len(lowered), match.end() + 24)]
        return bool(
            re.search(r"(?:\bno\b|\bnot\b|\bwithout\b|\bmust not\b|\bno[- ])\W*$", prefix)
            or re.match(r"^\W*(?:forbidden|not authorized|not permitted)\b", suffix)
        )

    for pattern in forbidden_patterns:
        match = re.search(pattern, lowered)
        if match is None:
            continue
        if not is_negated(match):
            raise ValueError(f"{field_name} may not carry V83 implementation authority")
    return value


def _reject_v83b_projection_or_runtime_claim(value: str, *, field_name: str) -> str:
    _reject_v83_action_claim(value, field_name=field_name)
    lowered = value.lower()
    forbidden_patterns = [
        r"\bprojection packet (?:created|ready|complete|authoritative)\b",
        r"\bwork[- ]packet handoff (?:created|ready|authorized)\b",
        r"\bsemantic truth\b",
        r"\btests? prove(?:s|d)? semantic preservation\b",
        r"\bmorphic ux runtime\b",
        r"\bruntime composer\b",
        r"\bdirect oai runtime\b",
        r"\bprovider capability authority\b",
        r"\bprovider runtime authority\b",
        r"\bv83-c (?:selected|complete|implemented)\b",
        r"\bv84 (?:selected|selection)\b",
    ]
    for pattern in forbidden_patterns:
        match = re.search(pattern, lowered)
        if match is None:
            continue
        prefix = lowered[max(0, match.start() - 24) : match.start()]
        suffix = lowered[match.end() : min(len(lowered), match.end() + 24)]
        negated = bool(
            re.search(r"(?:\bno\b|\bnot\b|\bwithout\b|\bmust not\b|\bno[- ])\W*$", prefix)
            or re.match(r"^\W*(?:forbidden|not authorized|not permitted)\b", suffix)
        )
        if not negated:
            raise ValueError(f"{field_name} may not carry V83-B downstream authority")
    return value


def _reject_v83c_execution_claim(value: str, *, field_name: str) -> str:
    _reject_v83_action_claim(value, field_name=field_name)
    lowered = value.lower()
    forbidden_patterns = [
        r"\bimplementation (?:done|completed|executed|authorized)\b",
        r"\bwork[- ]packet (?:executed|authorized|authority granted|ready to run)\b",
        r"\bworkflow transition (?:completed|authorized)\b",
        r"\bmorphic ux runtime (?:changed|updated|authorized)\b",
        r"\bdirect oai provider authority granted\b",
        r"\bprovider authority granted\b",
        r"\btests? prove(?:s|d)? semantic preservation\b",
        r"\bv84 (?:selected|selection)\b",
    ]
    for pattern in forbidden_patterns:
        match = re.search(pattern, lowered)
        if match is None:
            continue
        prefix = lowered[max(0, match.start() - 24) : match.start()]
        suffix = lowered[match.end() : min(len(lowered), match.end() + 24)]
        negated = bool(
            re.search(r"(?:\bno\b|\bnot\b|\bwithout\b|\bmust not\b|\bno[- ])\W*$", prefix)
            or re.match(r"^\W*(?:forbidden|not authorized|not permitted)\b", suffix)
        )
        if not negated:
            raise ValueError(f"{field_name} may not carry V83-C implementation authority")
    return value


def _validate_repo_refs(values: list[str], *, field_name: str) -> list[str]:
    normalized = _sorted_unique(values, field_name=field_name)
    for value in normalized:
        _repo_ref(value, field_name=field_name)
    return normalized


class RepoIntentSourceRow(_CartographyBase):
    source_ref: str
    source_kind: CandidateSourceKind
    authority_layer: CandidateAuthorityLayer
    source_status: SourceStatus
    source_presence_posture: CandidateSourcePresencePosture
    intent_source_role: IntentSourceRole
    source_horizon: str
    source_currentness: IntentSourceCurrentness
    source_scope_posture: IntentSourceScopePosture
    source_import_posture: IntentSourceImportPosture
    generation_posture: GenerationPosture
    model_agent_authority_posture: ModelAgentAuthorityPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_intent_source_row(self) -> RepoIntentSourceRow:
        _repo_ref(self.source_ref, field_name="source_ref")
        _non_empty(self.source_horizon, field_name="source_horizon")
        _reject_v83_action_claim(self.limitation_note, field_name="limitation_note")
        if (
            self.intent_source_role not in _ABSENCE_SOURCE_ROLES
            and self.source_presence_posture != "present"
            and self.source_import_posture != "external_import_required_before_lock"
        ):
            raise ValueError("non-absence intent source rows must be present or import-gapped")
        if (
            self.intent_source_role in _ABSENCE_SOURCE_ROLES
            and self.source_presence_posture == "present"
        ):
            raise ValueError("absence intent source rows must not be present sources")
        if self.intent_source_role in _SUPPORT_ONLY_SOURCE_ROLES and self.authority_layer == "lock":
            raise ValueError("support context source rows may not be lock authority")
        if (
            self.intent_source_role in _GENERATED_SOURCE_ROLES
            and self.generation_posture == "not_generated"
        ):
            raise ValueError("generated spec source rows require generated posture")
        if self.intent_source_role not in _GENERATED_SOURCE_ROLES and self.generation_posture in {
            "generated_for_review_only",
            "generated_from_bounded_context",
            "generated_from_unbounded_context",
        }:
            raise ValueError("generated posture is limited to generated spec source rows")
        if (
            self.intent_source_role == "model_generated_spec_candidate_source"
            and self.model_agent_authority_posture != "model_output_as_candidate_only"
        ):
            raise ValueError("model-generated spec rows must be candidate-only")
        if (
            self.intent_source_role == "agent_generated_spec_candidate_source"
            and self.model_agent_authority_posture != "agent_output_as_candidate_only"
        ):
            raise ValueError("agent-generated spec rows must be candidate-only")
        if (
            self.source_import_posture == "repo_owned_source"
            and self.source_presence_posture != "present"
        ):
            raise ValueError("repo-owned source posture requires present source")
        return self


class RepoIntentSourceIndex(_CartographyBase):
    schema: Literal["repo_intent_source_index@1"] = REPO_INTENT_SOURCE_INDEX_SCHEMA
    intent_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    source_rows: list[RepoIntentSourceRow] = Field(min_length=1)
    intent_source_summary: str

    @model_validator(mode="after")
    def _validate_intent_source_index(self) -> RepoIntentSourceIndex:
        object.__setattr__(
            self,
            "source_rows",
            _sorted_unique_by_ref(self.source_rows, attr="source_ref", field_name="source_rows"),
        )
        _non_empty(self.review_id, field_name="review_id")
        _non_empty(self.snapshot_id, field_name="snapshot_id")
        _non_empty(self.source_set_id, field_name="source_set_id")
        _require_terms(
            self.intent_source_summary,
            field_name="intent_source_summary",
            terms=("recordability", "eligibility", "candidate-only", "no implementation"),
        )
        expected_id = _surface_id(
            "repo_intent_source_index",
            self.schema,
            self.model_dump(mode="json"),
            "intent_source_index_id",
        )
        if self.intent_source_index_id != expected_id:
            raise ValueError("intent_source_index_id does not match canonical hash")
        return self


class RepoSemanticIntentContractRow(_CartographyBase):
    intent_contract_ref: str
    intent_version_ref: str
    intent_revision_posture: IntentRevisionPosture
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    intent_title: str
    intent_statement: str
    artifact_family_horizon: ArtifactFamilyHorizon
    implementation_surface_horizon: ImplementationSurfaceHorizon
    success_horizon: str
    success_horizon_kind: SuccessHorizonKind
    intent_recordability_posture: IntentRecordabilityPosture
    semantic_spec_eligibility_posture: SemanticSpecEligibilityPosture
    semantic_closure_posture: SemanticClosurePosture
    scope_posture: IntentScopePosture
    non_goal_refs: list[str] = Field(default_factory=list)
    semantic_constraint_refs: list[str] = Field(default_factory=list)
    operational_constraint_refs: list[str] = Field(default_factory=list)
    authority_boundary_refs: list[str] = Field(default_factory=list)
    expected_edge_classes: list[ExpectedEdgeClass] = Field(min_length=1)
    guardrail_refs: list[str] = Field(min_length=1)
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_semantic_intent_contract_row(self) -> RepoSemanticIntentContractRow:
        _non_empty(self.intent_contract_ref, field_name="intent_contract_ref")
        _non_empty(self.intent_version_ref, field_name="intent_version_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "non_goal_refs",
            "semantic_constraint_refs",
            "operational_constraint_refs",
            "authority_boundary_refs",
            "expected_edge_classes",
            "guardrail_refs",
            "odeu_lanes",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        _non_empty(self.intent_title, field_name="intent_title")
        _require_terms(
            self.intent_statement,
            field_name="intent_statement",
            terms=("intent", "spec"),
        )
        _reject_v83_action_claim(self.success_horizon, field_name="success_horizon")
        _reject_v83_action_claim(self.limitation_note, field_name="limitation_note")
        if self.semantic_spec_eligibility_posture == "eligible_for_semantic_spec_review":
            if self.intent_recordability_posture not in {
                "recordable_from_concrete_intent_source",
                "recordable_from_operator_turn_with_absence_markers",
            }:
                raise ValueError(
                    "eligible semantic intent contracts require concrete recordability"
                )
            if not self.non_goal_refs:
                raise ValueError("eligible semantic intent contracts require non-goal refs")
            if not self.authority_boundary_refs:
                raise ValueError(
                    "eligible semantic intent contracts require authority-boundary refs"
                )
            if self.success_horizon_kind == "future_family_only":
                raise ValueError("eligible semantic intent contracts require concrete success kind")
            if self.artifact_family_horizon in {
                "general_digital_artifact_projection_future_family",
                "future_family_only",
            }:
                raise ValueError(
                    "eligible semantic intent contracts require bounded artifact horizon"
                )
            if self.scope_posture != "bounded_semantic_spec_review":
                raise ValueError("eligible semantic intent contracts require bounded scope")
            if self.semantic_closure_posture != "closure_candidate_for_review":
                raise ValueError("eligible rows are closure candidates only")
        if self.success_horizon.strip().lower() in {"passes tests", "tests pass"}:
            raise ValueError("success horizon cannot be only passing tests")
        if self.semantic_spec_eligibility_posture == "future_family_only":
            if self.artifact_family_horizon != "general_digital_artifact_projection_future_family":
                raise ValueError(
                    "future-family-only semantic rows require deferred artifact horizon"
                )
        return self


class RepoSemanticIntentContract(_CartographyBase):
    schema: Literal["repo_semantic_intent_contract@1"] = REPO_SEMANTIC_INTENT_CONTRACT_SCHEMA
    semantic_intent_contract_id: str
    intent_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    intent_contract_rows: list[RepoSemanticIntentContractRow] = Field(min_length=1)
    semantic_intent_summary: str

    @model_validator(mode="after")
    def _validate_semantic_intent_contract(self) -> RepoSemanticIntentContract:
        object.__setattr__(
            self,
            "intent_contract_rows",
            _sorted_unique_by_ref(
                self.intent_contract_rows,
                attr="intent_contract_ref",
                field_name="intent_contract_rows",
            ),
        )
        _require_terms(
            self.semantic_intent_summary,
            field_name="semantic_intent_summary",
            terms=("semantic", "implementation spec", "no implementation"),
        )
        expected_id = _surface_id(
            "repo_semantic_intent_contract",
            self.schema,
            self.model_dump(mode="json"),
            "semantic_intent_contract_id",
        )
        if self.semantic_intent_contract_id != expected_id:
            raise ValueError("semantic_intent_contract_id does not match canonical hash")
        return self


class RepoIntentNonImplementationGuardrailRow(_CartographyBase):
    guardrail_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    intent_contract_refs: list[str] = Field(min_length=1)
    forbidden_implementation_actions: list[ForbiddenImplementationAction] = Field(min_length=1)
    forbidden_runtime_actions: list[ForbiddenRuntimeAction] = Field(min_length=1)
    forbidden_downstream_authority: list[ForbiddenSemanticDownstreamAuthority] = Field(min_length=1)
    required_later_authority_refs: list[str] = Field(default_factory=list)
    non_implementation_posture: NonImplementationPosture
    non_execution_posture: NonExecutionPosture
    non_dispatch_posture: NonDispatchPosture
    non_release_posture: NonReleasePosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_non_implementation_guardrail_row(
        self,
    ) -> RepoIntentNonImplementationGuardrailRow:
        _non_empty(self.guardrail_ref, field_name="guardrail_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "intent_contract_refs",
            "forbidden_implementation_actions",
            "forbidden_runtime_actions",
            "forbidden_downstream_authority",
            "required_later_authority_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        for authority_ref in self.required_later_authority_refs:
            _repo_ref(authority_ref, field_name="required_later_authority_refs")
        missing_implementation = _FORBIDDEN_IMPLEMENTATION_ACTIONS.difference(
            self.forbidden_implementation_actions
        )
        if missing_implementation:
            raise ValueError("intent guardrail omits forbidden implementation actions")
        missing_runtime = _FORBIDDEN_RUNTIME_ACTIONS.difference(self.forbidden_runtime_actions)
        if missing_runtime:
            raise ValueError("intent guardrail omits forbidden runtime actions")
        missing_authority = _FORBIDDEN_DOWNSTREAM_AUTHORITIES.difference(
            self.forbidden_downstream_authority
        )
        if missing_authority:
            raise ValueError("intent guardrail omits forbidden downstream authority")
        _reject_v83_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("no implementation", "no execution", "no release"),
        )
        return self


class RepoIntentNonImplementationGuardrail(_CartographyBase):
    schema: Literal["repo_intent_non_implementation_guardrail@1"] = (
        REPO_INTENT_NON_IMPLEMENTATION_GUARDRAIL_SCHEMA
    )
    intent_non_implementation_guardrail_id: str
    semantic_intent_contract_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    guardrail_rows: list[RepoIntentNonImplementationGuardrailRow] = Field(min_length=1)
    non_implementation_summary: str

    @model_validator(mode="after")
    def _validate_non_implementation_guardrail(self) -> RepoIntentNonImplementationGuardrail:
        object.__setattr__(
            self,
            "guardrail_rows",
            _sorted_unique_by_ref(
                self.guardrail_rows,
                attr="guardrail_ref",
                field_name="guardrail_rows",
            ),
        )
        _require_terms(
            self.non_implementation_summary,
            field_name="non_implementation_summary",
            terms=("no implementation", "no execution", "no release"),
        )
        expected_id = _surface_id(
            "repo_intent_non_implementation_guardrail",
            self.schema,
            self.model_dump(mode="json"),
            "intent_non_implementation_guardrail_id",
        )
        if self.intent_non_implementation_guardrail_id != expected_id:
            raise ValueError("intent_non_implementation_guardrail_id does not match canonical hash")
        return self


def derive_v83a_repo_intent_source_index(*, repo_root: Path | None = None) -> RepoIntentSourceIndex:
    _ = repo_root
    payload = {
        "schema": REPO_INTENT_SOURCE_INDEX_SCHEMA,
        "intent_source_index_id": "",
        "review_id": "review:v83a:semantic-implementation-spec",
        "snapshot_id": "vNext+232-corpus-ingestion-review-closeout",
        "source_set_id": "source-set:v83a:semantic-implementation-spec-intent",
        "source_rows": [
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus232/"
                    "repo_corpus_ingestion_review_summary_v232_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "intent_source_role": "v82_summary_source",
                "source_horizon": "Released V82-C corpus-ingestion review summary substrate.",
                "source_currentness": "current_concrete_source",
                "source_scope_posture": "bounded_to_semantic_intent_review",
                "source_import_posture": "repo_owned_source",
                "generation_posture": "not_generated",
                "model_agent_authority_posture": "no_model_authority",
                "limitation_note": (
                    "V82 summary source for semantic spec review; no implementation."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus232/"
                    "repo_post_corpus_ingestion_review_handoff_v232_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "intent_source_role": "v82_handoff_source",
                "source_horizon": "Released V82-C post-corpus-ingestion-review handoff substrate.",
                "source_currentness": "current_concrete_source",
                "source_scope_posture": "bounded_to_semantic_intent_review",
                "source_import_posture": "repo_owned_source",
                "generation_posture": "not_generated",
                "model_agent_authority_posture": "no_model_authority",
                "limitation_note": (
                    "V82 handoff source for semantic spec review; no implementation."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus232/"
                    "repo_corpus_ingestion_review_family_closeout_alignment_v232_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "intent_source_role": "v82_closeout_source",
                "source_horizon": "Released V82 family closeout alignment substrate.",
                "source_currentness": "current_concrete_source",
                "source_scope_posture": "bounded_to_semantic_intent_review",
                "source_import_posture": "repo_owned_source",
                "generation_posture": "not_generated",
                "model_agent_authority_posture": "no_model_authority",
                "limitation_note": (
                    "V82 closeout source for semantic spec review; no implementation."
                ),
            },
            {
                "source_ref": _source_path(
                    "docs/support/arc_series_mapping/"
                    "V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_"
                    "COMBINED_DOGFOOD_TEST_v0.json"
                ),
                "source_kind": "support_doc",
                "authority_layer": "support",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "intent_source_role": "combined_dogfood_source",
                "source_horizon": "Combined V68-V82 dogfood context.",
                "source_currentness": "current_concrete_source",
                "source_scope_posture": "context_only",
                "source_import_posture": "support_context_only",
                "generation_posture": "not_generated",
                "model_agent_authority_posture": "no_model_authority",
                "limitation_note": "Dogfood context only; no implementation authority.",
            },
            {
                "source_ref": _source_path("docs/DRAFT_NEXT_ARC_OPTIONS_v73.md"),
                "source_kind": "planning_doc",
                "authority_layer": "planning",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "intent_source_role": "operator_intent_source",
                "source_horizon": "Planning source selecting semantic implementation-spec review.",
                "source_currentness": "current_concrete_source",
                "source_scope_posture": "bounded_to_semantic_intent_review",
                "source_import_posture": "repo_owned_source",
                "generation_posture": "not_generated",
                "model_agent_authority_posture": "no_model_authority",
                "limitation_note": "Operator-shaped intent source; no implementation.",
            },
            {
                "source_ref": _source_path(
                    "docs/ARCHITECTURE_ADEU_SEMANTIC_IMPLEMENTATION_SPECIFICATION_REVIEW_FAMILY_v0.md"
                ),
                "source_kind": "architecture_doc",
                "authority_layer": "architecture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "intent_source_role": "repo_architecture_source",
                "source_horizon": "Architecture source for semantic implementation-spec review.",
                "source_currentness": "current_concrete_source",
                "source_scope_posture": "bounded_to_semantic_intent_review",
                "source_import_posture": "repo_owned_source",
                "generation_posture": "not_generated",
                "model_agent_authority_posture": "no_model_authority",
                "limitation_note": "Architecture source for review boundary; no implementation.",
            },
            {
                "source_ref": _source_path("docs/support/morphic_ux. v2.md"),
                "source_kind": "support_doc",
                "authority_layer": "support",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "intent_source_role": "morphic_ux_support_source",
                "source_horizon": "Morphic UX v2 support instantiation.",
                "source_currentness": "current_concrete_source",
                "source_scope_posture": "context_only",
                "source_import_posture": "repo_owned_source",
                "generation_posture": "not_generated",
                "model_agent_authority_posture": "no_model_authority",
                "limitation_note": "Morphic UX support context only; no implementation.",
            },
            {
                "source_ref": "external-support:direct-oai-meta-orchestrator-loop",
                "source_kind": "external_artifact",
                "authority_layer": "support",
                "source_status": "review_pending_input",
                "source_presence_posture": "external_unavailable",
                "intent_source_role": "external_meta_orchestrator_support_source",
                "source_horizon": "External direct-harness meta-orchestrator support source.",
                "source_currentness": "unknown_needs_review",
                "source_scope_posture": "external_import_required",
                "source_import_posture": "external_import_required_before_lock",
                "generation_posture": "not_generated",
                "model_agent_authority_posture": "no_model_authority",
                "limitation_note": "External support import gap; no runtime authority.",
            },
            {
                "source_ref": "external-support:direct-oai-upstream-profile",
                "source_kind": "external_artifact",
                "authority_layer": "support",
                "source_status": "review_pending_input",
                "source_presence_posture": "external_unavailable",
                "intent_source_role": "external_oai_profile_support_source",
                "source_horizon": "External direct OAI upstream profile support source.",
                "source_currentness": "unknown_needs_review",
                "source_scope_posture": "external_import_required",
                "source_import_posture": "external_import_required_before_lock",
                "generation_posture": "not_generated",
                "model_agent_authority_posture": "no_model_authority",
                "limitation_note": "External OAI support import gap; no runtime authority.",
            },
            {
                "source_ref": "intent:v83a:non-goal:no-implementation",
                "source_kind": "operator_turn",
                "authority_layer": "planning",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "intent_source_role": "non_goal_source",
                "source_horizon": "Non-goal: V83-A does not implement code or work packets.",
                "source_currentness": "current_concrete_source",
                "source_scope_posture": "bounded_to_semantic_intent_review",
                "source_import_posture": "repo_owned_source",
                "generation_posture": "not_generated",
                "model_agent_authority_posture": "no_model_authority",
                "limitation_note": "Non-goal source: no implementation and no execution.",
            },
            {
                "source_ref": "intent:v83a:authority-boundary:later-lock-required",
                "source_kind": "operator_turn",
                "authority_layer": "planning",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "intent_source_role": "authority_boundary_source",
                "source_horizon": "Authority boundary: later implementation lock required.",
                "source_currentness": "current_concrete_source",
                "source_scope_posture": "bounded_to_semantic_intent_review",
                "source_import_posture": "repo_owned_source",
                "generation_posture": "not_generated",
                "model_agent_authority_posture": "no_model_authority",
                "limitation_note": (
                    "Authority boundary source: no implementation without later lock."
                ),
            },
            {
                "source_ref": "generated-spec:v83a:current:absent",
                "source_kind": "model_output",
                "authority_layer": "support",
                "source_status": "review_pending_input",
                "source_presence_posture": "external_unavailable",
                "intent_source_role": "explicit_absence_marker",
                "source_horizon": "No generated implementation-spec candidate is present.",
                "source_currentness": "explicit_absence_marker",
                "source_scope_posture": "absence_marker",
                "source_import_posture": "absence_marker",
                "generation_posture": "generated_source_missing",
                "model_agent_authority_posture": "authority_requires_later_lock",
                "limitation_note": "Generated spec absence marker; no implementation truth.",
            },
        ],
        "intent_source_summary": (
            "Intent source rows separate recordability from eligibility, keep model "
            "and agent output candidate-only, and preserve no implementation."
        ),
    }
    payload["source_rows"] = sorted(payload["source_rows"], key=lambda row: row["source_ref"])
    payload["intent_source_index_id"] = _surface_id(
        "repo_intent_source_index",
        REPO_INTENT_SOURCE_INDEX_SCHEMA,
        payload,
        "intent_source_index_id",
    )
    return RepoIntentSourceIndex.model_validate(payload)


def derive_v83a_repo_semantic_intent_contract(
    *,
    repo_root: Path | None = None,
    intent_source_index: RepoIntentSourceIndex | None = None,
) -> RepoSemanticIntentContract:
    _ = repo_root
    source_index = intent_source_index or derive_v83a_repo_intent_source_index()
    v82_refs = [
        row.source_ref
        for row in source_index.source_rows
        if row.intent_source_role in _V82_ELIGIBILITY_SOURCE_ROLES
    ]
    operator_refs = [
        row.source_ref
        for row in source_index.source_rows
        if row.intent_source_role in _CONCRETE_INTENT_SOURCE_ROLES
    ]
    non_goal_refs = [
        row.source_ref
        for row in source_index.source_rows
        if row.intent_source_role == "non_goal_source"
    ]
    authority_refs = [
        row.source_ref
        for row in source_index.source_rows
        if row.intent_source_role == "authority_boundary_source"
    ]
    payload = {
        "schema": REPO_SEMANTIC_INTENT_CONTRACT_SCHEMA,
        "semantic_intent_contract_id": "",
        "intent_source_index_id": source_index.intent_source_index_id,
        "review_id": source_index.review_id,
        "snapshot_id": source_index.snapshot_id,
        "source_set_id": source_index.source_set_id,
        "intent_contract_rows": [
            {
                "intent_contract_ref": "semantic-intent:v83a:intent-to-implementation-spec",
                "intent_version_ref": "intent-version:v83a:intent-to-spec:v1",
                "intent_revision_posture": "initial_intent_version",
                "candidate_ref": "candidate:internal:intent_to_implementation_spec_institution",
                "source_refs": sorted({*v82_refs, *operator_refs, *non_goal_refs, *authority_refs}),
                "intent_title": "Institutionalize intent-to-implementation specification review",
                "intent_statement": (
                    "The intent is to create a source-bound semantic implementation spec "
                    "review layer before implementation specs or work packets are projected."
                ),
                "artifact_family_horizon": "repo_schema_implementation_spec",
                "implementation_surface_horizon": "repo_description_schema_surface",
                "success_horizon": (
                    "Success means schema shape, validator behavior, reference fixture, "
                    "reject fixture, and documentation alignment preserve the semantic "
                    "intent before any implementation."
                ),
                "success_horizon_kind": "implementation_packet_success",
                "intent_recordability_posture": "recordable_from_concrete_intent_source",
                "semantic_spec_eligibility_posture": "eligible_for_semantic_spec_review",
                "semantic_closure_posture": "closure_candidate_for_review",
                "scope_posture": "bounded_semantic_spec_review",
                "non_goal_refs": sorted(non_goal_refs),
                "semantic_constraint_refs": sorted(authority_refs),
                "operational_constraint_refs": sorted(v82_refs),
                "authority_boundary_refs": sorted(authority_refs),
                "expected_edge_classes": [
                    "authority_boundary_edge",
                    "future_family_boundary_edge",
                    "non_goal_preservation_edge",
                    "source_binding_edge",
                    "success_horizon_edge",
                    "target_surface_boundedness_edge",
                    "validation_evidence_edge",
                ],
                "guardrail_refs": ["guardrail:v83a:intent-to-spec:non-implementation"],
                "odeu_lanes": ["deontic", "epistemic", "ontological", "utility"],
                "limitation_note": (
                    "Eligible for semantic implementation spec review only; "
                    "no implementation, no execution, and no release."
                ),
            },
            {
                "intent_contract_ref": "semantic-intent:v83a:general-digital-artifact-future",
                "intent_version_ref": "intent-version:v83a:general-artifact:v1",
                "intent_revision_posture": "initial_intent_version",
                "candidate_ref": "candidate:future:general_digital_artifact_projection",
                "source_refs": sorted({*operator_refs, *non_goal_refs, *authority_refs}),
                "intent_title": "General digital artifact projection remains future-family only",
                "intent_statement": (
                    "The intent is to preserve generalized digital artifact projection as a "
                    "future family while V83-A stays on implementation spec review."
                ),
                "artifact_family_horizon": "general_digital_artifact_projection_future_family",
                "implementation_surface_horizon": "future_family_only",
                "success_horizon": (
                    "Success means the generalized artifact theory remains mapped but not "
                    "selected by V83-A."
                ),
                "success_horizon_kind": "future_family_only",
                "intent_recordability_posture": "recordable_from_concrete_intent_source",
                "semantic_spec_eligibility_posture": "future_family_only",
                "semantic_closure_posture": "future_family_only",
                "scope_posture": "future_family_only",
                "non_goal_refs": sorted(non_goal_refs),
                "semantic_constraint_refs": sorted(authority_refs),
                "operational_constraint_refs": [],
                "authority_boundary_refs": sorted(authority_refs),
                "expected_edge_classes": [
                    "future_family_boundary_edge",
                    "non_goal_preservation_edge",
                ],
                "guardrail_refs": ["guardrail:v83a:general-artifact:future-family"],
                "odeu_lanes": ["ontological", "utility"],
                "limitation_note": (
                    "General artifact projection is future-family only with no implementation."
                ),
            },
            {
                "intent_contract_ref": "semantic-intent:v83a:direct-harness-import-gap",
                "intent_version_ref": "intent-version:v83a:direct-harness:v1",
                "intent_revision_posture": "initial_intent_version",
                "candidate_ref": "candidate:support:direct_oai_harness_spec_pressure",
                "source_refs": sorted(
                    {
                        "external-support:direct-oai-meta-orchestrator-loop",
                        "external-support:direct-oai-upstream-profile",
                        *non_goal_refs,
                        *authority_refs,
                    }
                ),
                "intent_title": "Direct OAI harness support remains import-blocked context",
                "intent_statement": (
                    "The intent is to carry direct OAI harness spec pressure as context "
                    "until external support sources are imported or absence-marked."
                ),
                "artifact_family_horizon": "direct_oai_harness_spec",
                "implementation_surface_horizon": "direct_oai_harness_surface",
                "success_horizon": (
                    "Success means direct harness pressure is blocked by source import "
                    "posture and does not grant runtime authority."
                ),
                "success_horizon_kind": "provider_capability_profile_success",
                "intent_recordability_posture": "recordable_from_support_context_only",
                "semantic_spec_eligibility_posture": "blocked_by_external_source_import_gap",
                "semantic_closure_posture": "closure_blocked_by_missing_source",
                "scope_posture": "context_only",
                "non_goal_refs": sorted(non_goal_refs),
                "semantic_constraint_refs": sorted(authority_refs),
                "operational_constraint_refs": [
                    "external-support:direct-oai-meta-orchestrator-loop",
                    "external-support:direct-oai-upstream-profile",
                ],
                "authority_boundary_refs": sorted(authority_refs),
                "expected_edge_classes": [
                    "authority_boundary_edge",
                    "source_binding_edge",
                ],
                "guardrail_refs": ["guardrail:v83a:direct-harness:import-gap"],
                "odeu_lanes": ["deontic", "epistemic"],
                "limitation_note": (
                    "Direct OAI harness pressure is context only; no runtime authority "
                    "and no implementation."
                ),
            },
        ],
        "semantic_intent_summary": (
            "Semantic implementation spec intent contracts are review only with "
            "no implementation, no execution, and no release."
        ),
    }
    payload["intent_contract_rows"] = sorted(
        payload["intent_contract_rows"],
        key=lambda row: row["intent_contract_ref"],
    )
    payload["semantic_intent_contract_id"] = _surface_id(
        "repo_semantic_intent_contract",
        REPO_SEMANTIC_INTENT_CONTRACT_SCHEMA,
        payload,
        "semantic_intent_contract_id",
    )
    return RepoSemanticIntentContract.model_validate(payload)


def derive_v83a_repo_intent_non_implementation_guardrail(
    *,
    repo_root: Path | None = None,
    semantic_intent_contract: RepoSemanticIntentContract | None = None,
) -> RepoIntentNonImplementationGuardrail:
    _ = repo_root
    contract = semantic_intent_contract or derive_v83a_repo_semantic_intent_contract()
    grouped_rows: dict[str, dict[str, object]] = {}
    for contract_row in contract.intent_contract_rows:
        for guardrail_ref in contract_row.guardrail_refs:
            existing = grouped_rows.setdefault(
                guardrail_ref,
                {
                    "guardrail_ref": guardrail_ref,
                    "candidate_ref": contract_row.candidate_ref,
                    "source_refs": [],
                    "intent_contract_refs": [],
                    "forbidden_implementation_actions": sorted(_FORBIDDEN_IMPLEMENTATION_ACTIONS),
                    "forbidden_runtime_actions": sorted(_FORBIDDEN_RUNTIME_ACTIONS),
                    "forbidden_downstream_authority": sorted(_FORBIDDEN_DOWNSTREAM_AUTHORITIES),
                    "required_later_authority_refs": sorted(contract_row.authority_boundary_refs),
                    "non_implementation_posture": "non_implementation_guardrail_active",
                    "non_execution_posture": "non_execution_guardrail_active",
                    "non_dispatch_posture": "non_dispatch_guardrail_active",
                    "non_release_posture": "non_release_guardrail_active",
                    "limitation_note": (
                        "V83-A guardrail is review only: no implementation, "
                        "no execution, no dispatch, no product authorization, "
                        "and no release."
                    ),
                },
            )
            if existing["candidate_ref"] != contract_row.candidate_ref:
                raise ValueError("intent guardrail cannot merge candidates")
            existing["source_refs"] = sorted({*existing["source_refs"], *contract_row.source_refs})
            existing["intent_contract_refs"] = sorted(
                {*existing["intent_contract_refs"], contract_row.intent_contract_ref}
            )
            existing["required_later_authority_refs"] = sorted(
                {
                    *existing["required_later_authority_refs"],
                    *contract_row.authority_boundary_refs,
                }
            )
    payload = {
        "schema": REPO_INTENT_NON_IMPLEMENTATION_GUARDRAIL_SCHEMA,
        "intent_non_implementation_guardrail_id": "",
        "semantic_intent_contract_id": contract.semantic_intent_contract_id,
        "review_id": contract.review_id,
        "snapshot_id": contract.snapshot_id,
        "source_set_id": contract.source_set_id,
        "guardrail_rows": sorted(grouped_rows.values(), key=lambda row: row["guardrail_ref"]),
        "non_implementation_summary": (
            "Intent non-implementation guardrails preserve no implementation, "
            "no execution, no dispatch, no release, and no downstream authority."
        ),
    }
    payload["intent_non_implementation_guardrail_id"] = _surface_id(
        "repo_intent_non_implementation_guardrail",
        REPO_INTENT_NON_IMPLEMENTATION_GUARDRAIL_SCHEMA,
        payload,
        "intent_non_implementation_guardrail_id",
    )
    return RepoIntentNonImplementationGuardrail.model_validate(payload)


def validate_v83a_semantic_implementation_spec_bundle(
    *,
    intent_source_index: RepoIntentSourceIndex,
    semantic_intent_contract: RepoSemanticIntentContract,
    intent_non_implementation_guardrail: RepoIntentNonImplementationGuardrail,
) -> None:
    if (
        semantic_intent_contract.intent_source_index_id
        != intent_source_index.intent_source_index_id
    ):
        raise ValueError("semantic intent contract must reference the intent source index")
    if (
        semantic_intent_contract.review_id,
        semantic_intent_contract.snapshot_id,
        semantic_intent_contract.source_set_id,
    ) != (
        intent_source_index.review_id,
        intent_source_index.snapshot_id,
        intent_source_index.source_set_id,
    ):
        raise ValueError("semantic intent contract provenance must match source index")
    if (
        intent_non_implementation_guardrail.semantic_intent_contract_id
        != semantic_intent_contract.semantic_intent_contract_id
    ):
        raise ValueError("intent guardrail must reference the semantic intent contract")
    if (
        intent_non_implementation_guardrail.review_id,
        intent_non_implementation_guardrail.snapshot_id,
        intent_non_implementation_guardrail.source_set_id,
    ) != (
        semantic_intent_contract.review_id,
        semantic_intent_contract.snapshot_id,
        semantic_intent_contract.source_set_id,
    ):
        raise ValueError("intent guardrail provenance must match semantic intent contract")

    source_roles = {
        row.source_ref: row.intent_source_role for row in intent_source_index.source_rows
    }
    generation_postures = {
        row.source_ref: row.generation_posture for row in intent_source_index.source_rows
    }
    model_authority_postures = {
        row.source_ref: row.model_agent_authority_posture for row in intent_source_index.source_rows
    }
    known_sources = set(source_roles)
    guardrails = {
        row.guardrail_ref: row for row in intent_non_implementation_guardrail.guardrail_rows
    }
    for contract_row in semantic_intent_contract.intent_contract_rows:
        if any(source_ref not in known_sources for source_ref in contract_row.source_refs):
            raise ValueError("semantic intent contract source refs must be known")
        roles = {source_roles[source_ref] for source_ref in contract_row.source_refs}
        if contract_row.semantic_spec_eligibility_posture == "eligible_for_semantic_spec_review":
            if not roles.intersection(_V82_ELIGIBILITY_SOURCE_ROLES):
                raise ValueError(
                    "eligible semantic intent contracts require released V82-C sources"
                )
            if not roles.intersection(_CONCRETE_INTENT_SOURCE_ROLES):
                raise ValueError(
                    "eligible semantic intent contracts require concrete intent source"
                )
            for source_ref in contract_row.source_refs:
                if source_roles[source_ref] in _GENERATED_SOURCE_ROLES:
                    if generation_postures[source_ref] == "generated_from_unbounded_context":
                        raise ValueError("unbounded generated specs cannot support eligibility")
                    if model_authority_postures[source_ref] not in {
                        "model_output_as_candidate_only",
                        "agent_output_as_candidate_only",
                    }:
                        raise ValueError("generated spec sources must remain candidate-only")
        for guardrail_ref in contract_row.guardrail_refs:
            guardrail = guardrails.get(guardrail_ref)
            if guardrail is None:
                raise ValueError("semantic intent contract guardrail refs must be known")
            if guardrail.candidate_ref != contract_row.candidate_ref:
                raise ValueError("intent guardrail candidate must match contract")
            if contract_row.intent_contract_ref not in guardrail.intent_contract_refs:
                raise ValueError("intent guardrail must reference contract row")
    contract_rows = {
        row.intent_contract_ref: row for row in semantic_intent_contract.intent_contract_rows
    }
    for guardrail_row in intent_non_implementation_guardrail.guardrail_rows:
        if any(source_ref not in known_sources for source_ref in guardrail_row.source_refs):
            raise ValueError("intent guardrail source refs must be known")
        for contract_ref in guardrail_row.intent_contract_refs:
            contract_row = contract_rows.get(contract_ref)
            if contract_row is None:
                raise ValueError("intent guardrail contract refs must be known")
            if contract_row.candidate_ref != guardrail_row.candidate_ref:
                raise ValueError("intent guardrail contract candidate must match")


def derive_v83a_semantic_implementation_spec_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoIntentSourceIndex,
    RepoSemanticIntentContract,
    RepoIntentNonImplementationGuardrail,
]:
    source_index = derive_v83a_repo_intent_source_index(repo_root=repo_root)
    contract = derive_v83a_repo_semantic_intent_contract(
        repo_root=repo_root,
        intent_source_index=source_index,
    )
    guardrail = derive_v83a_repo_intent_non_implementation_guardrail(
        repo_root=repo_root,
        semantic_intent_contract=contract,
    )
    validate_v83a_semantic_implementation_spec_bundle(
        intent_source_index=source_index,
        semantic_intent_contract=contract,
        intent_non_implementation_guardrail=guardrail,
    )
    return source_index, contract, guardrail


class RepoSemanticObjectRow(_CartographyBase):
    semantic_object_ref: str
    object_kind: SemanticObjectKind
    object_label: str
    source_refs: list[str] = Field(min_length=1)
    anticipated_artifact_kind_refs: list[str] = Field(default_factory=list)
    truth_posture: SemanticTruthPosture
    mutability_posture: SemanticMutabilityPosture
    authority_posture: SemanticAuthorityPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_semantic_object(self) -> RepoSemanticObjectRow:
        _repo_ref(self.semantic_object_ref, field_name="semantic_object_ref")
        _non_empty(self.object_label, field_name="object_label")
        object.__setattr__(
            self,
            "source_refs",
            _validate_repo_refs(self.source_refs, field_name="source_refs"),
        )
        object.__setattr__(
            self,
            "anticipated_artifact_kind_refs",
            _sorted_unique(
                self.anticipated_artifact_kind_refs,
                field_name="anticipated_artifact_kind_refs",
            ),
        )
        if self.object_kind in {"non_goal", "authority_boundary"}:
            if self.authority_posture not in {
                "authority_boundary_only",
                "no_authority_granted",
            }:
                raise ValueError("boundary semantic objects may not grant authority")
        _reject_v83b_projection_or_runtime_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoSemanticRelationRow(_CartographyBase):
    semantic_relation_ref: str
    relation_kind: SemanticRelationKind
    from_object_ref: str
    to_object_ref: str
    source_refs: list[str] = Field(min_length=1)
    preservation_requirement: PreservationRequirement
    validation_need_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_semantic_relation(self) -> RepoSemanticRelationRow:
        _repo_ref(self.semantic_relation_ref, field_name="semantic_relation_ref")
        _repo_ref(self.from_object_ref, field_name="from_object_ref")
        _repo_ref(self.to_object_ref, field_name="to_object_ref")
        object.__setattr__(
            self,
            "source_refs",
            _validate_repo_refs(self.source_refs, field_name="source_refs"),
        )
        object.__setattr__(
            self,
            "validation_need_refs",
            _validate_repo_refs(self.validation_need_refs, field_name="validation_need_refs"),
        )
        if self.relation_kind == "non_goal_of":
            if self.preservation_requirement != "preserve_as_non_goal":
                raise ValueError("non-goal relations must preserve the non-goal")
        if self.relation_kind == "authority_requires":
            if self.preservation_requirement != "preserve_as_authority_boundary":
                raise ValueError("authority relations must preserve authority boundary")
        _reject_v83b_projection_or_runtime_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoValidationNeedRow(_CartographyBase):
    validation_need_ref: str
    semantic_edge_refs: list[str] = Field(min_length=1)
    validation_kind: ValidationKind
    required_evidence_kind: RequiredEvidenceKind
    required_positive_fixture_posture: FixturePosture
    required_reject_fixture_posture: FixturePosture
    manual_review_required: bool
    tool_applicability_posture: ToolApplicabilityPosture
    acceptance_not_truth_guardrail: AcceptanceNotTruthGuardrail
    limitation_note: str

    @model_validator(mode="after")
    def _validate_validation_need(self) -> RepoValidationNeedRow:
        _repo_ref(self.validation_need_ref, field_name="validation_need_ref")
        object.__setattr__(
            self,
            "semantic_edge_refs",
            _validate_repo_refs(self.semantic_edge_refs, field_name="semantic_edge_refs"),
        )
        if self.validation_kind == "reject_fixture":
            if self.required_reject_fixture_posture != "required":
                raise ValueError("reject fixture validation needs require reject posture")
        if self.validation_kind in {"schema_validation", "validator_behavior"}:
            if self.required_evidence_kind not in {"schema", "validator"}:
                raise ValueError("schema and validator needs require matching evidence")
        _reject_v83b_projection_or_runtime_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoIntentEdgeConstraintRow(_CartographyBase):
    constraint_ref: str
    source_refs: list[str] = Field(min_length=1)
    semantic_relation_refs: list[str] = Field(min_length=1)
    constraint_posture: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_constraint(self) -> RepoIntentEdgeConstraintRow:
        _repo_ref(self.constraint_ref, field_name="constraint_ref")
        object.__setattr__(
            self,
            "source_refs",
            _validate_repo_refs(self.source_refs, field_name="source_refs"),
        )
        object.__setattr__(
            self,
            "semantic_relation_refs",
            _validate_repo_refs(
                self.semantic_relation_refs,
                field_name="semantic_relation_refs",
            ),
        )
        _non_empty(self.constraint_posture, field_name="constraint_posture")
        _reject_v83b_projection_or_runtime_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoIntentEdgeNonGoalRow(_CartographyBase):
    non_goal_ref: str
    source_refs: list[str] = Field(min_length=1)
    semantic_relation_refs: list[str] = Field(min_length=1)
    non_goal_posture: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_non_goal_edge(self) -> RepoIntentEdgeNonGoalRow:
        _repo_ref(self.non_goal_ref, field_name="non_goal_ref")
        object.__setattr__(
            self,
            "source_refs",
            _validate_repo_refs(self.source_refs, field_name="source_refs"),
        )
        object.__setattr__(
            self,
            "semantic_relation_refs",
            _validate_repo_refs(
                self.semantic_relation_refs,
                field_name="semantic_relation_refs",
            ),
        )
        _require_terms(
            self.non_goal_posture,
            field_name="non_goal_posture",
            terms=("non-goal",),
        )
        _reject_v83b_projection_or_runtime_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoIntentAuthorityEdgeRow(_CartographyBase):
    authority_edge_ref: str
    source_refs: list[str] = Field(min_length=1)
    semantic_relation_refs: list[str] = Field(min_length=1)
    authority_boundary_posture: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_authority_edge(self) -> RepoIntentAuthorityEdgeRow:
        _repo_ref(self.authority_edge_ref, field_name="authority_edge_ref")
        object.__setattr__(
            self,
            "source_refs",
            _validate_repo_refs(self.source_refs, field_name="source_refs"),
        )
        object.__setattr__(
            self,
            "semantic_relation_refs",
            _validate_repo_refs(
                self.semantic_relation_refs,
                field_name="semantic_relation_refs",
            ),
        )
        _require_terms(
            self.authority_boundary_posture,
            field_name="authority_boundary_posture",
            terms=("boundary", "no authority"),
        )
        _reject_v83b_projection_or_runtime_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoIntentEdgeDecompositionRow(_CartographyBase):
    edge_decomposition_ref: str
    intent_contract_refs: list[str] = Field(min_length=1)
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    semantic_object_rows: list[RepoSemanticObjectRow] = Field(min_length=1)
    semantic_relation_rows: list[RepoSemanticRelationRow] = Field(min_length=1)
    constraint_rows: list[RepoIntentEdgeConstraintRow] = Field(default_factory=list)
    non_goal_rows: list[RepoIntentEdgeNonGoalRow] = Field(default_factory=list)
    authority_edge_rows: list[RepoIntentAuthorityEdgeRow] = Field(default_factory=list)
    validation_need_rows: list[RepoValidationNeedRow] = Field(min_length=1)
    edge_decomposition_posture: IntentEdgeDecompositionPosture
    semantic_closure_posture: SemanticClosureReviewPosture
    guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_edge_decomposition_row(self) -> RepoIntentEdgeDecompositionRow:
        _repo_ref(self.edge_decomposition_ref, field_name="edge_decomposition_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in ("intent_contract_refs", "source_refs", "guardrail_refs"):
            object.__setattr__(
                self,
                field_name,
                _validate_repo_refs(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "semantic_object_rows",
            _sorted_unique_by_ref(
                self.semantic_object_rows,
                attr="semantic_object_ref",
                field_name="semantic_object_rows",
            ),
        )
        object.__setattr__(
            self,
            "semantic_relation_rows",
            _sorted_unique_by_ref(
                self.semantic_relation_rows,
                attr="semantic_relation_ref",
                field_name="semantic_relation_rows",
            ),
        )
        object.__setattr__(
            self,
            "constraint_rows",
            _sorted_unique_by_ref(
                self.constraint_rows,
                attr="constraint_ref",
                field_name="constraint_rows",
            ),
        )
        object.__setattr__(
            self,
            "non_goal_rows",
            _sorted_unique_by_ref(
                self.non_goal_rows,
                attr="non_goal_ref",
                field_name="non_goal_rows",
            ),
        )
        object.__setattr__(
            self,
            "authority_edge_rows",
            _sorted_unique_by_ref(
                self.authority_edge_rows,
                attr="authority_edge_ref",
                field_name="authority_edge_rows",
            ),
        )
        object.__setattr__(
            self,
            "validation_need_rows",
            _sorted_unique_by_ref(
                self.validation_need_rows,
                attr="validation_need_ref",
                field_name="validation_need_rows",
            ),
        )
        object_refs = {row.semantic_object_ref for row in self.semantic_object_rows}
        validation_refs = {row.validation_need_ref for row in self.validation_need_rows}
        relation_refs = {row.semantic_relation_ref for row in self.semantic_relation_rows}
        for relation in self.semantic_relation_rows:
            if (
                relation.from_object_ref not in object_refs
                or relation.to_object_ref not in object_refs
            ):
                raise ValueError("semantic relations must reference known semantic objects")
            if any(ref not in validation_refs for ref in relation.validation_need_refs):
                raise ValueError("semantic relations must reference known validation needs")
        for need in self.validation_need_rows:
            if any(ref not in relation_refs for ref in need.semantic_edge_refs):
                raise ValueError("validation needs must reference known semantic relations")
        if self.edge_decomposition_posture == "edges_decomposed_for_review":
            if self.semantic_closure_posture != "edge_review_candidate_only":
                raise ValueError("decomposed edges remain edge-review candidates only")
        _reject_v83b_projection_or_runtime_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoIntentEdgeDecomposition(_CartographyBase):
    schema: Literal["repo_intent_edge_decomposition@1"] = REPO_INTENT_EDGE_DECOMPOSITION_SCHEMA
    intent_edge_decomposition_id: str
    semantic_intent_contract_id: str
    intent_source_index_id: str
    intent_non_implementation_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    edge_decomposition_rows: list[RepoIntentEdgeDecompositionRow] = Field(min_length=1)
    edge_decomposition_summary: str

    @model_validator(mode="after")
    def _validate_edge_decomposition(self) -> RepoIntentEdgeDecomposition:
        object.__setattr__(
            self,
            "edge_decomposition_rows",
            _sorted_unique_by_ref(
                self.edge_decomposition_rows,
                attr="edge_decomposition_ref",
                field_name="edge_decomposition_rows",
            ),
        )
        _require_terms(
            self.edge_decomposition_summary,
            field_name="edge_decomposition_summary",
            terms=("edge", "review", "no implementation"),
        )
        expected_id = _surface_id(
            "repo_intent_edge_decomposition",
            self.schema,
            self.model_dump(mode="json"),
            "intent_edge_decomposition_id",
        )
        if self.intent_edge_decomposition_id != expected_id:
            raise ValueError("intent_edge_decomposition_id does not match canonical hash")
        return self


class RepoAcceptanceEvidenceRequirementRow(_CartographyBase):
    evidence_requirement_ref: str
    semantic_edge_refs: list[str] = Field(min_length=1)
    validation_need_refs: list[str] = Field(min_length=1)
    evidence_kind: RequiredEvidenceKind
    required_artifact_refs: list[str] = Field(min_length=1)
    non_truth_guardrail: AcceptanceNotTruthGuardrail
    limitation_note: str

    @model_validator(mode="after")
    def _validate_evidence_requirement(self) -> RepoAcceptanceEvidenceRequirementRow:
        _repo_ref(self.evidence_requirement_ref, field_name="evidence_requirement_ref")
        for field_name in (
            "semantic_edge_refs",
            "validation_need_refs",
            "required_artifact_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _validate_repo_refs(getattr(self, field_name), field_name=field_name),
            )
        _reject_v83b_projection_or_runtime_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoArtifactObligationRow(_CartographyBase):
    artifact_obligation_ref: str
    semantic_edge_refs: list[str] = Field(min_length=1)
    artifact_kind: ArtifactKind
    target_surface_refs: list[str] = Field(min_length=1)
    required_change_posture: RequiredChangePosture
    required_fixture_posture: RequiredArtifactPosture
    required_test_posture: RequiredArtifactPosture
    required_doc_posture: RequiredArtifactPosture
    acceptance_evidence_requirements: list[RepoAcceptanceEvidenceRequirementRow] = Field(
        min_length=1
    )
    non_implementation_posture: NonImplementationPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_artifact_obligation(self) -> RepoArtifactObligationRow:
        _repo_ref(self.artifact_obligation_ref, field_name="artifact_obligation_ref")
        for field_name in ("semantic_edge_refs", "target_surface_refs"):
            object.__setattr__(
                self,
                field_name,
                _validate_repo_refs(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "acceptance_evidence_requirements",
            _sorted_unique_by_ref(
                self.acceptance_evidence_requirements,
                attr="evidence_requirement_ref",
                field_name="acceptance_evidence_requirements",
            ),
        )
        if any(target in _BROAD_ARTIFACT_TARGETS for target in self.target_surface_refs):
            if self.required_change_posture == "change_required_for_later_implementation_spec":
                raise ValueError("artifact obligations require bounded target surfaces")
        if self.non_implementation_posture != "non_implementation_guardrail_active":
            raise ValueError("artifact obligations remain non-implementation")
        _reject_v83b_projection_or_runtime_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoArtifactObligationMapRow(_CartographyBase):
    obligation_map_ref: str
    intent_contract_refs: list[str] = Field(min_length=1)
    edge_decomposition_refs: list[str] = Field(min_length=1)
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    artifact_obligation_rows: list[RepoArtifactObligationRow] = Field(min_length=1)
    coverage_posture: CoveragePosture
    implementation_readiness_posture: ImplementationReadinessPosture
    guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_obligation_map_row(self) -> RepoArtifactObligationMapRow:
        _repo_ref(self.obligation_map_ref, field_name="obligation_map_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "intent_contract_refs",
            "edge_decomposition_refs",
            "source_refs",
            "guardrail_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _validate_repo_refs(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "artifact_obligation_rows",
            _sorted_unique_by_ref(
                self.artifact_obligation_rows,
                attr="artifact_obligation_ref",
                field_name="artifact_obligation_rows",
            ),
        )
        if self.implementation_readiness_posture == "ready_for_projection_review_only":
            if self.coverage_posture not in {
                "obligations_cover_all_required_edges",
                "obligations_cover_with_nonblocking_warnings",
            }:
                raise ValueError("projection-review readiness requires covered obligations")
        _reject_v83b_projection_or_runtime_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoArtifactObligationMap(_CartographyBase):
    schema: Literal["repo_artifact_obligation_map@1"] = REPO_ARTIFACT_OBLIGATION_MAP_SCHEMA
    artifact_obligation_map_id: str
    intent_edge_decomposition_id: str
    semantic_intent_contract_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    obligation_map_rows: list[RepoArtifactObligationMapRow] = Field(min_length=1)
    obligation_map_summary: str

    @model_validator(mode="after")
    def _validate_obligation_map(self) -> RepoArtifactObligationMap:
        object.__setattr__(
            self,
            "obligation_map_rows",
            _sorted_unique_by_ref(
                self.obligation_map_rows,
                attr="obligation_map_ref",
                field_name="obligation_map_rows",
            ),
        )
        _require_terms(
            self.obligation_map_summary,
            field_name="obligation_map_summary",
            terms=("artifact", "obligation", "no implementation"),
        )
        expected_id = _surface_id(
            "repo_artifact_obligation_map",
            self.schema,
            self.model_dump(mode="json"),
            "artifact_obligation_map_id",
        )
        if self.artifact_obligation_map_id != expected_id:
            raise ValueError("artifact_obligation_map_id does not match canonical hash")
        return self


class RepoSemanticDriftAmbiguityRow(_CartographyBase):
    drift_ref: str
    drift_kind: DriftKind
    semantic_edge_refs: list[str] = Field(default_factory=list)
    artifact_obligation_refs: list[str] = Field(default_factory=list)
    source_refs: list[str] = Field(min_length=1)
    severity_posture: DriftSeverityPosture
    blocking_posture: DriftBlockingPosture
    required_resolution_horizon: RequiredResolutionHorizon
    limitation_note: str

    @model_validator(mode="after")
    def _validate_drift_row(self) -> RepoSemanticDriftAmbiguityRow:
        _repo_ref(self.drift_ref, field_name="drift_ref")
        for field_name in ("semantic_edge_refs", "artifact_obligation_refs", "source_refs"):
            object.__setattr__(
                self,
                field_name,
                _validate_repo_refs(getattr(self, field_name), field_name=field_name),
            )
        if self.severity_posture == "blocking" and self.blocking_posture != "blocking":
            raise ValueError("blocking drift rows must remain blocking")
        if self.drift_kind in {"morphic_ux_scope_drift", "direct_oai_runtime_scope_drift"}:
            if self.required_resolution_horizon not in {
                "future_family_review",
                "semantic_review",
            }:
                raise ValueError("support-scope drift requires semantic or future review")
        _reject_v83b_projection_or_runtime_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoSemanticDriftAmbiguityRegisterRow(_CartographyBase):
    drift_register_ref: str
    intent_contract_refs: list[str] = Field(min_length=1)
    edge_decomposition_refs: list[str] = Field(min_length=1)
    obligation_map_refs: list[str] = Field(min_length=1)
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    drift_or_ambiguity_rows: list[RepoSemanticDriftAmbiguityRow] = Field(min_length=1)
    blocking_posture: DriftRegisterBlockingPosture
    required_next_surface: DriftRequiredNextSurface
    guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_drift_register_row(self) -> RepoSemanticDriftAmbiguityRegisterRow:
        _repo_ref(self.drift_register_ref, field_name="drift_register_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "intent_contract_refs",
            "edge_decomposition_refs",
            "obligation_map_refs",
            "source_refs",
            "guardrail_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _validate_repo_refs(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "drift_or_ambiguity_rows",
            _sorted_unique_by_ref(
                self.drift_or_ambiguity_rows,
                attr="drift_ref",
                field_name="drift_or_ambiguity_rows",
            ),
        )
        has_blocker = any(
            row.blocking_posture == "blocking" for row in self.drift_or_ambiguity_rows
        )
        if has_blocker and self.blocking_posture != "blocking_drift_visible":
            raise ValueError("blocking drift cannot be hidden by ready posture")
        if self.required_next_surface == "v83c_projection_packet_review" and has_blocker:
            raise ValueError("blocking drift prevents ordinary V83-C projection readiness")
        _reject_v83b_projection_or_runtime_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoSemanticDriftAmbiguityRegister(_CartographyBase):
    schema: Literal["repo_semantic_drift_ambiguity_register@1"] = (
        REPO_SEMANTIC_DRIFT_AMBIGUITY_REGISTER_SCHEMA
    )
    semantic_drift_ambiguity_register_id: str
    artifact_obligation_map_id: str
    intent_edge_decomposition_id: str
    semantic_intent_contract_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    drift_register_rows: list[RepoSemanticDriftAmbiguityRegisterRow] = Field(min_length=1)
    drift_register_summary: str

    @model_validator(mode="after")
    def _validate_drift_register(self) -> RepoSemanticDriftAmbiguityRegister:
        object.__setattr__(
            self,
            "drift_register_rows",
            _sorted_unique_by_ref(
                self.drift_register_rows,
                attr="drift_register_ref",
                field_name="drift_register_rows",
            ),
        )
        _require_terms(
            self.drift_register_summary,
            field_name="drift_register_summary",
            terms=("drift", "ambiguity", "no implementation"),
        )
        expected_id = _surface_id(
            "repo_semantic_drift_ambiguity_register",
            self.schema,
            self.model_dump(mode="json"),
            "semantic_drift_ambiguity_register_id",
        )
        if self.semantic_drift_ambiguity_register_id != expected_id:
            raise ValueError("semantic_drift_ambiguity_register_id does not match canonical hash")
        return self


def _v83a_released_refs(
    *,
    source_index: RepoIntentSourceIndex,
    semantic_intent_contract: RepoSemanticIntentContract,
    intent_non_implementation_guardrail: RepoIntentNonImplementationGuardrail,
) -> tuple[RepoSemanticIntentContractRow, list[str], list[str]]:
    eligible_rows = [
        row
        for row in semantic_intent_contract.intent_contract_rows
        if row.semantic_spec_eligibility_posture == "eligible_for_semantic_spec_review"
    ]
    if len(eligible_rows) != 1:
        raise ValueError("V83-B derivation expects one eligible V83-A intent row")
    source_refs = sorted({row.source_ref for row in source_index.source_rows})
    guardrail_refs = sorted(
        {row.guardrail_ref for row in intent_non_implementation_guardrail.guardrail_rows}
    )
    return eligible_rows[0], source_refs, guardrail_refs


def derive_v83b_repo_intent_edge_decomposition(
    *,
    repo_root: Path | None = None,
    intent_source_index: RepoIntentSourceIndex | None = None,
    semantic_intent_contract: RepoSemanticIntentContract | None = None,
    intent_non_implementation_guardrail: RepoIntentNonImplementationGuardrail | None = None,
) -> RepoIntentEdgeDecomposition:
    _ = repo_root
    if (
        intent_source_index is None
        or semantic_intent_contract is None
        or intent_non_implementation_guardrail is None
    ):
        (
            intent_source_index,
            semantic_intent_contract,
            intent_non_implementation_guardrail,
        ) = derive_v83a_semantic_implementation_spec_bundle()
    eligible, _, guardrail_refs = _v83a_released_refs(
        source_index=intent_source_index,
        semantic_intent_contract=semantic_intent_contract,
        intent_non_implementation_guardrail=intent_non_implementation_guardrail,
    )
    source_refs = sorted(eligible.source_refs)
    semantic_object_rows = [
        {
            "semantic_object_ref": "semantic-object:v83b:authority:later-lock",
            "object_kind": "authority_boundary",
            "object_label": "Later implementation lock authority boundary",
            "source_refs": sorted(eligible.authority_boundary_refs),
            "anticipated_artifact_kind_refs": [],
            "truth_posture": "source_bound_claim_for_review",
            "mutability_posture": "immutable_boundary",
            "authority_posture": "authority_boundary_only",
            "limitation_note": "Authority boundary object for review; no implementation.",
        },
        {
            "semantic_object_ref": "semantic-object:v83b:domain:intent-to-spec",
            "object_kind": "domain_object",
            "object_label": "Intent to implementation-spec transformation",
            "source_refs": source_refs,
            "anticipated_artifact_kind_refs": [
                "artifact-kind:v83b:fixture",
                "artifact-kind:v83b:schema",
                "artifact-kind:v83b:test",
            ],
            "truth_posture": "source_bound_claim_for_review",
            "mutability_posture": "review_object_only",
            "authority_posture": "no_authority_granted",
            "limitation_note": "Semantic object for edge review; no implementation.",
        },
        {
            "semantic_object_ref": "semantic-object:v83b:morphic-ux:support",
            "object_kind": "ux_surface",
            "object_label": "Morphic UX support instantiation",
            "source_refs": ["docs/support/morphic_ux. v2.md"],
            "anticipated_artifact_kind_refs": ["artifact-kind:v83b:ux-projection"],
            "truth_posture": "candidate_only",
            "mutability_posture": "target_requires_later_lock",
            "authority_posture": "candidate_only_no_authority",
            "limitation_note": "Morphic UX support is scoped context only; no implementation.",
        },
        {
            "semantic_object_ref": "semantic-object:v83b:non-goal:no-implementation",
            "object_kind": "non_goal",
            "object_label": "No implementation in V83-B",
            "source_refs": sorted(eligible.non_goal_refs),
            "anticipated_artifact_kind_refs": [],
            "truth_posture": "source_bound_claim_for_review",
            "mutability_posture": "immutable_boundary",
            "authority_posture": "no_authority_granted",
            "limitation_note": "Non-goal object preserved for review; no implementation.",
        },
        {
            "semantic_object_ref": "semantic-object:v83b:provider:direct-oai",
            "object_kind": "provider_capability_surface",
            "object_label": "Direct OAI support profile pressure",
            "source_refs": [
                "external-support:direct-oai-meta-orchestrator-loop",
                "external-support:direct-oai-upstream-profile",
            ],
            "anticipated_artifact_kind_refs": ["artifact-kind:v83b:provider-profile"],
            "truth_posture": "candidate_only",
            "mutability_posture": "target_requires_later_lock",
            "authority_posture": "candidate_only_no_authority",
            "limitation_note": "Direct OAI profile is support context only; no implementation.",
        },
        {
            "semantic_object_ref": "semantic-object:v83b:schema:edge-decomposition",
            "object_kind": "schema_surface",
            "object_label": "Intent edge decomposition schema",
            "source_refs": source_refs,
            "anticipated_artifact_kind_refs": ["artifact-kind:v83b:schema"],
            "truth_posture": "source_bound_claim_for_review",
            "mutability_posture": "review_object_only",
            "authority_posture": "no_authority_granted",
            "limitation_note": "Schema surface obligation candidate; no implementation.",
        },
    ]
    semantic_relation_rows = [
        {
            "semantic_relation_ref": "semantic-relation:v83b:acceptance:evidence-bound",
            "relation_kind": "acceptance_requires",
            "from_object_ref": "semantic-object:v83b:schema:edge-decomposition",
            "to_object_ref": "semantic-object:v83b:domain:intent-to-spec",
            "source_refs": source_refs,
            "preservation_requirement": "preserve_as_validation_need",
            "validation_need_refs": [
                "validation-need:v83b:positive-fixture",
                "validation-need:v83b:reject-fixture",
            ],
            "limitation_note": "Acceptance evidence is edge-bound; no semantic truth.",
        },
        {
            "semantic_relation_ref": "semantic-relation:v83b:authority:later-lock",
            "relation_kind": "authority_requires",
            "from_object_ref": "semantic-object:v83b:domain:intent-to-spec",
            "to_object_ref": "semantic-object:v83b:authority:later-lock",
            "source_refs": sorted(eligible.authority_boundary_refs),
            "preservation_requirement": "preserve_as_authority_boundary",
            "validation_need_refs": ["validation-need:v83b:semantic-review"],
            "limitation_note": "Later lock boundary is preserved; no implementation.",
        },
        {
            "semantic_relation_ref": "semantic-relation:v83b:morphic:scoped",
            "relation_kind": "constrains",
            "from_object_ref": "semantic-object:v83b:morphic-ux:support",
            "to_object_ref": "semantic-object:v83b:domain:intent-to-spec",
            "source_refs": ["docs/support/morphic_ux. v2.md"],
            "preservation_requirement": "preserve_semantic_relation_for_review",
            "validation_need_refs": ["validation-need:v83b:semantic-review"],
            "limitation_note": "Morphic UX remains scoped support context; no implementation.",
        },
        {
            "semantic_relation_ref": "semantic-relation:v83b:non-goal:no-implementation",
            "relation_kind": "non_goal_of",
            "from_object_ref": "semantic-object:v83b:non-goal:no-implementation",
            "to_object_ref": "semantic-object:v83b:domain:intent-to-spec",
            "source_refs": sorted(eligible.non_goal_refs),
            "preservation_requirement": "preserve_as_non_goal",
            "validation_need_refs": ["validation-need:v83b:reject-fixture"],
            "limitation_note": "Non-goal is preserved and cannot become required work.",
        },
        {
            "semantic_relation_ref": "semantic-relation:v83b:provider:not-authority",
            "relation_kind": "must_remain_distinct_from",
            "from_object_ref": "semantic-object:v83b:provider:direct-oai",
            "to_object_ref": "semantic-object:v83b:authority:later-lock",
            "source_refs": [
                "external-support:direct-oai-meta-orchestrator-loop",
                "external-support:direct-oai-upstream-profile",
            ],
            "preservation_requirement": "preserve_as_authority_boundary",
            "validation_need_refs": ["validation-need:v83b:reject-fixture"],
            "limitation_note": "Direct OAI support cannot grant provider authority.",
        },
        {
            "semantic_relation_ref": "semantic-relation:v83b:realizes:intent",
            "relation_kind": "realizes",
            "from_object_ref": "semantic-object:v83b:schema:edge-decomposition",
            "to_object_ref": "semantic-object:v83b:domain:intent-to-spec",
            "source_refs": source_refs,
            "preservation_requirement": "preserve_semantic_relation_for_review",
            "validation_need_refs": [
                "validation-need:v83b:schema-validation",
                "validation-need:v83b:validator-behavior",
            ],
            "limitation_note": "Edge decomposition realizes review shape; no implementation.",
        },
        {
            "semantic_relation_ref": "semantic-relation:v83b:validation:edge-bound",
            "relation_kind": "validation_requires",
            "from_object_ref": "semantic-object:v83b:schema:edge-decomposition",
            "to_object_ref": "semantic-object:v83b:domain:intent-to-spec",
            "source_refs": source_refs,
            "preservation_requirement": "preserve_as_validation_need",
            "validation_need_refs": [
                "validation-need:v83b:positive-fixture",
                "validation-need:v83b:reject-fixture",
                "validation-need:v83b:validator-behavior",
            ],
            "limitation_note": "Validation needs bind to semantic edges; no implementation.",
        },
    ]
    validation_need_rows = [
        {
            "validation_need_ref": "validation-need:v83b:positive-fixture",
            "semantic_edge_refs": [
                "semantic-relation:v83b:acceptance:evidence-bound",
                "semantic-relation:v83b:validation:edge-bound",
            ],
            "validation_kind": "positive_fixture",
            "required_evidence_kind": "positive_fixture",
            "required_positive_fixture_posture": "required",
            "required_reject_fixture_posture": "not_required",
            "manual_review_required": False,
            "tool_applicability_posture": "review_only",
            "acceptance_not_truth_guardrail": "acceptance_evidence_is_not_semantic_truth",
            "limitation_note": "Positive fixture evidence is not semantic truth.",
        },
        {
            "validation_need_ref": "validation-need:v83b:reject-fixture",
            "semantic_edge_refs": [
                "semantic-relation:v83b:acceptance:evidence-bound",
                "semantic-relation:v83b:non-goal:no-implementation",
                "semantic-relation:v83b:provider:not-authority",
                "semantic-relation:v83b:validation:edge-bound",
            ],
            "validation_kind": "reject_fixture",
            "required_evidence_kind": "reject_fixture",
            "required_positive_fixture_posture": "not_required",
            "required_reject_fixture_posture": "required",
            "manual_review_required": False,
            "tool_applicability_posture": "review_only",
            "acceptance_not_truth_guardrail": "acceptance_evidence_is_not_semantic_truth",
            "limitation_note": "Reject fixture evidence is not semantic truth.",
        },
        {
            "validation_need_ref": "validation-need:v83b:schema-validation",
            "semantic_edge_refs": ["semantic-relation:v83b:realizes:intent"],
            "validation_kind": "schema_validation",
            "required_evidence_kind": "schema",
            "required_positive_fixture_posture": "required",
            "required_reject_fixture_posture": "not_required",
            "manual_review_required": False,
            "tool_applicability_posture": "review_only",
            "acceptance_not_truth_guardrail": "acceptance_evidence_is_not_semantic_truth",
            "limitation_note": "Schema validation evidence is not semantic truth.",
        },
        {
            "validation_need_ref": "validation-need:v83b:semantic-review",
            "semantic_edge_refs": [
                "semantic-relation:v83b:authority:later-lock",
                "semantic-relation:v83b:morphic:scoped",
            ],
            "validation_kind": "semantic_review",
            "required_evidence_kind": "semantic_review",
            "required_positive_fixture_posture": "not_required",
            "required_reject_fixture_posture": "required",
            "manual_review_required": True,
            "tool_applicability_posture": "not_applicable",
            "acceptance_not_truth_guardrail": "acceptance_evidence_is_not_semantic_truth",
            "limitation_note": "Semantic review evidence is not implementation truth.",
        },
        {
            "validation_need_ref": "validation-need:v83b:validator-behavior",
            "semantic_edge_refs": [
                "semantic-relation:v83b:realizes:intent",
                "semantic-relation:v83b:validation:edge-bound",
            ],
            "validation_kind": "validator_behavior",
            "required_evidence_kind": "validator",
            "required_positive_fixture_posture": "required",
            "required_reject_fixture_posture": "required",
            "manual_review_required": False,
            "tool_applicability_posture": "review_only",
            "acceptance_not_truth_guardrail": "acceptance_evidence_is_not_semantic_truth",
            "limitation_note": "Validator evidence is not semantic truth.",
        },
    ]
    payload = {
        "schema": REPO_INTENT_EDGE_DECOMPOSITION_SCHEMA,
        "intent_edge_decomposition_id": "",
        "semantic_intent_contract_id": semantic_intent_contract.semantic_intent_contract_id,
        "intent_source_index_id": intent_source_index.intent_source_index_id,
        "intent_non_implementation_guardrail_id": (
            intent_non_implementation_guardrail.intent_non_implementation_guardrail_id
        ),
        "review_id": semantic_intent_contract.review_id,
        "snapshot_id": "vNext+233-semantic-intent-contract-closeout",
        "source_set_id": semantic_intent_contract.source_set_id,
        "edge_decomposition_rows": [
            {
                "edge_decomposition_ref": "edge-decomposition:v83b:intent-to-spec",
                "intent_contract_refs": [eligible.intent_contract_ref],
                "candidate_ref": eligible.candidate_ref,
                "source_refs": source_refs,
                "semantic_object_rows": sorted(
                    semantic_object_rows,
                    key=lambda row: row["semantic_object_ref"],
                ),
                "semantic_relation_rows": sorted(
                    semantic_relation_rows,
                    key=lambda row: row["semantic_relation_ref"],
                ),
                "constraint_rows": [
                    {
                        "constraint_ref": "constraint:v83b:test-evidence-not-truth",
                        "source_refs": source_refs,
                        "semantic_relation_refs": [
                            "semantic-relation:v83b:acceptance:evidence-bound"
                        ],
                        "constraint_posture": "tests and fixtures are evidence requirements only",
                        "limitation_note": (
                            "Constraint preserves review-only evidence; no implementation."
                        ),
                    }
                ],
                "non_goal_rows": [
                    {
                        "non_goal_ref": "non-goal:v83b:no-implementation",
                        "source_refs": sorted(eligible.non_goal_refs),
                        "semantic_relation_refs": [
                            "semantic-relation:v83b:non-goal:no-implementation"
                        ],
                        "non_goal_posture": "non-goal preserved as non-goal",
                        "limitation_note": "Non-goal is visible and remains no implementation.",
                    }
                ],
                "authority_edge_rows": [
                    {
                        "authority_edge_ref": "authority-edge:v83b:later-lock-required",
                        "source_refs": sorted(eligible.authority_boundary_refs),
                        "semantic_relation_refs": ["semantic-relation:v83b:authority:later-lock"],
                        "authority_boundary_posture": "boundary only with no authority granted",
                        "limitation_note": "Authority edge constrains review; no implementation.",
                    }
                ],
                "validation_need_rows": sorted(
                    validation_need_rows,
                    key=lambda row: row["validation_need_ref"],
                ),
                "edge_decomposition_posture": "edges_decomposed_for_review",
                "semantic_closure_posture": "edge_review_candidate_only",
                "guardrail_refs": guardrail_refs,
                "limitation_note": (
                    "V83-B decomposes semantic edges for review only; no implementation."
                ),
            }
        ],
        "edge_decomposition_summary": (
            "V83-B edge decomposition binds semantic edges to released intent rows "
            "for review with no implementation."
        ),
    }
    payload["intent_edge_decomposition_id"] = _surface_id(
        "repo_intent_edge_decomposition",
        REPO_INTENT_EDGE_DECOMPOSITION_SCHEMA,
        payload,
        "intent_edge_decomposition_id",
    )
    return RepoIntentEdgeDecomposition.model_validate(payload)


def derive_v83b_repo_artifact_obligation_map(
    *,
    repo_root: Path | None = None,
    semantic_intent_contract: RepoSemanticIntentContract | None = None,
    intent_edge_decomposition: RepoIntentEdgeDecomposition | None = None,
) -> RepoArtifactObligationMap:
    _ = repo_root
    if semantic_intent_contract is None or intent_edge_decomposition is None:
        source_index, contract, guardrail = derive_v83a_semantic_implementation_spec_bundle()
        semantic_intent_contract = contract
        intent_edge_decomposition = derive_v83b_repo_intent_edge_decomposition(
            intent_source_index=source_index,
            semantic_intent_contract=contract,
            intent_non_implementation_guardrail=guardrail,
        )
    edge_row = intent_edge_decomposition.edge_decomposition_rows[0]
    source_refs = sorted(edge_row.source_refs)
    evidence_common = {
        "semantic_edge_refs": ["semantic-relation:v83b:validation:edge-bound"],
        "validation_need_refs": ["validation-need:v83b:validator-behavior"],
        "non_truth_guardrail": "acceptance_evidence_is_not_semantic_truth",
    }
    obligations = [
        {
            "artifact_obligation_ref": "artifact-obligation:v83b:fixtures",
            "semantic_edge_refs": [
                "semantic-relation:v83b:acceptance:evidence-bound",
                "semantic-relation:v83b:validation:edge-bound",
            ],
            "artifact_kind": "fixture",
            "target_surface_refs": ["apps/api/fixtures/repo_description/vnext_plus234"],
            "required_change_posture": "change_required_for_later_implementation_spec",
            "required_fixture_posture": "required_for_review",
            "required_test_posture": "required_for_review",
            "required_doc_posture": "not_applicable",
            "acceptance_evidence_requirements": [
                {
                    "evidence_requirement_ref": "evidence-requirement:v83b:fixtures",
                    **evidence_common,
                    "evidence_kind": "positive_fixture",
                    "required_artifact_refs": [
                        "apps/api/fixtures/repo_description/vnext_plus234/"
                        "repo_intent_edge_decomposition_v234_reference.json"
                    ],
                    "limitation_note": "Fixture evidence is edge-bound and not semantic truth.",
                }
            ],
            "non_implementation_posture": "non_implementation_guardrail_active",
            "limitation_note": "Fixture obligation is review-only with no implementation.",
        },
        {
            "artifact_obligation_ref": "artifact-obligation:v83b:schema:artifact-obligation-map",
            "semantic_edge_refs": ["semantic-relation:v83b:realizes:intent"],
            "artifact_kind": "schema",
            "target_surface_refs": [
                "packages/adeu_repo_description/schema/repo_artifact_obligation_map.v1.json"
            ],
            "required_change_posture": "change_required_for_later_implementation_spec",
            "required_fixture_posture": "required_for_review",
            "required_test_posture": "required_for_review",
            "required_doc_posture": "required_for_review",
            "acceptance_evidence_requirements": [
                {
                    "evidence_requirement_ref": (
                        "evidence-requirement:v83b:schema:artifact-obligation-map"
                    ),
                    **evidence_common,
                    "evidence_kind": "schema",
                    "required_artifact_refs": [
                        "packages/adeu_repo_description/schema/repo_artifact_obligation_map.v1.json"
                    ],
                    "limitation_note": "Schema evidence is review-only and not semantic truth.",
                }
            ],
            "non_implementation_posture": "non_implementation_guardrail_active",
            "limitation_note": "Schema obligation is review-only with no implementation.",
        },
        {
            "artifact_obligation_ref": "artifact-obligation:v83b:schema:drift-register",
            "semantic_edge_refs": ["semantic-relation:v83b:validation:edge-bound"],
            "artifact_kind": "schema",
            "target_surface_refs": [
                "packages/adeu_repo_description/schema/"
                "repo_semantic_drift_ambiguity_register.v1.json"
            ],
            "required_change_posture": "change_required_for_later_implementation_spec",
            "required_fixture_posture": "required_for_review",
            "required_test_posture": "required_for_review",
            "required_doc_posture": "required_for_review",
            "acceptance_evidence_requirements": [
                {
                    "evidence_requirement_ref": "evidence-requirement:v83b:schema:drift-register",
                    **evidence_common,
                    "evidence_kind": "schema",
                    "required_artifact_refs": [
                        "packages/adeu_repo_description/schema/"
                        "repo_semantic_drift_ambiguity_register.v1.json"
                    ],
                    "limitation_note": "Drift schema evidence is not semantic truth.",
                }
            ],
            "non_implementation_posture": "non_implementation_guardrail_active",
            "limitation_note": "Drift schema obligation is review-only; no implementation.",
        },
        {
            "artifact_obligation_ref": "artifact-obligation:v83b:schema:edge-decomposition",
            "semantic_edge_refs": ["semantic-relation:v83b:realizes:intent"],
            "artifact_kind": "schema",
            "target_surface_refs": [
                "packages/adeu_repo_description/schema/repo_intent_edge_decomposition.v1.json"
            ],
            "required_change_posture": "change_required_for_later_implementation_spec",
            "required_fixture_posture": "required_for_review",
            "required_test_posture": "required_for_review",
            "required_doc_posture": "required_for_review",
            "acceptance_evidence_requirements": [
                {
                    "evidence_requirement_ref": (
                        "evidence-requirement:v83b:schema:edge-decomposition"
                    ),
                    **evidence_common,
                    "evidence_kind": "schema",
                    "required_artifact_refs": [
                        "packages/adeu_repo_description/schema/repo_intent_edge_decomposition.v1.json"
                    ],
                    "limitation_note": "Edge schema evidence is not semantic truth.",
                }
            ],
            "non_implementation_posture": "non_implementation_guardrail_active",
            "limitation_note": "Edge schema obligation is review-only; no implementation.",
        },
        {
            "artifact_obligation_ref": "artifact-obligation:v83b:tests",
            "semantic_edge_refs": [
                "semantic-relation:v83b:acceptance:evidence-bound",
                "semantic-relation:v83b:provider:not-authority",
            ],
            "artifact_kind": "test",
            "target_surface_refs": [
                "packages/adeu_repo_description/tests/test_semantic_implementation_spec_v83b.py"
            ],
            "required_change_posture": "change_required_for_later_implementation_spec",
            "required_fixture_posture": "required_for_review",
            "required_test_posture": "required_for_review",
            "required_doc_posture": "not_applicable",
            "acceptance_evidence_requirements": [
                {
                    "evidence_requirement_ref": "evidence-requirement:v83b:tests",
                    "semantic_edge_refs": [
                        "semantic-relation:v83b:acceptance:evidence-bound",
                        "semantic-relation:v83b:provider:not-authority",
                    ],
                    "validation_need_refs": [
                        "validation-need:v83b:reject-fixture",
                        "validation-need:v83b:validator-behavior",
                    ],
                    "evidence_kind": "unit_test",
                    "required_artifact_refs": [
                        "packages/adeu_repo_description/tests/"
                        "test_semantic_implementation_spec_v83b.py"
                    ],
                    "non_truth_guardrail": "acceptance_evidence_is_not_semantic_truth",
                    "limitation_note": "Test evidence is edge-bound and not semantic truth.",
                }
            ],
            "non_implementation_posture": "non_implementation_guardrail_active",
            "limitation_note": "Test obligation is review-only with no implementation.",
        },
    ]
    payload = {
        "schema": REPO_ARTIFACT_OBLIGATION_MAP_SCHEMA,
        "artifact_obligation_map_id": "",
        "intent_edge_decomposition_id": intent_edge_decomposition.intent_edge_decomposition_id,
        "semantic_intent_contract_id": semantic_intent_contract.semantic_intent_contract_id,
        "review_id": intent_edge_decomposition.review_id,
        "snapshot_id": intent_edge_decomposition.snapshot_id,
        "source_set_id": intent_edge_decomposition.source_set_id,
        "obligation_map_rows": [
            {
                "obligation_map_ref": "obligation-map:v83b:intent-to-spec",
                "intent_contract_refs": edge_row.intent_contract_refs,
                "edge_decomposition_refs": [edge_row.edge_decomposition_ref],
                "candidate_ref": edge_row.candidate_ref,
                "source_refs": source_refs,
                "artifact_obligation_rows": sorted(
                    obligations,
                    key=lambda row: row["artifact_obligation_ref"],
                ),
                "coverage_posture": "obligations_cover_with_nonblocking_warnings",
                "implementation_readiness_posture": "ready_for_projection_review_only",
                "guardrail_refs": edge_row.guardrail_refs,
                "limitation_note": (
                    "Artifact obligations cover semantic edges for projection review only; "
                    "no implementation."
                ),
            }
        ],
        "obligation_map_summary": (
            "V83-B artifact obligation map binds artifact obligations to semantic "
            "edges with no implementation."
        ),
    }
    payload["artifact_obligation_map_id"] = _surface_id(
        "repo_artifact_obligation_map",
        REPO_ARTIFACT_OBLIGATION_MAP_SCHEMA,
        payload,
        "artifact_obligation_map_id",
    )
    return RepoArtifactObligationMap.model_validate(payload)


def derive_v83b_repo_semantic_drift_ambiguity_register(
    *,
    repo_root: Path | None = None,
    semantic_intent_contract: RepoSemanticIntentContract | None = None,
    intent_edge_decomposition: RepoIntentEdgeDecomposition | None = None,
    artifact_obligation_map: RepoArtifactObligationMap | None = None,
) -> RepoSemanticDriftAmbiguityRegister:
    _ = repo_root
    if (
        semantic_intent_contract is None
        or intent_edge_decomposition is None
        or artifact_obligation_map is None
    ):
        source_index, contract, guardrail = derive_v83a_semantic_implementation_spec_bundle()
        semantic_intent_contract = contract
        intent_edge_decomposition = derive_v83b_repo_intent_edge_decomposition(
            intent_source_index=source_index,
            semantic_intent_contract=contract,
            intent_non_implementation_guardrail=guardrail,
        )
        artifact_obligation_map = derive_v83b_repo_artifact_obligation_map(
            semantic_intent_contract=contract,
            intent_edge_decomposition=intent_edge_decomposition,
        )
    edge_row = intent_edge_decomposition.edge_decomposition_rows[0]
    obligation_row = artifact_obligation_map.obligation_map_rows[0]
    payload = {
        "schema": REPO_SEMANTIC_DRIFT_AMBIGUITY_REGISTER_SCHEMA,
        "semantic_drift_ambiguity_register_id": "",
        "artifact_obligation_map_id": artifact_obligation_map.artifact_obligation_map_id,
        "intent_edge_decomposition_id": intent_edge_decomposition.intent_edge_decomposition_id,
        "semantic_intent_contract_id": semantic_intent_contract.semantic_intent_contract_id,
        "review_id": intent_edge_decomposition.review_id,
        "snapshot_id": intent_edge_decomposition.snapshot_id,
        "source_set_id": intent_edge_decomposition.source_set_id,
        "drift_register_rows": [
            {
                "drift_register_ref": "drift-register:v83b:intent-to-spec",
                "intent_contract_refs": edge_row.intent_contract_refs,
                "edge_decomposition_refs": [edge_row.edge_decomposition_ref],
                "obligation_map_refs": [obligation_row.obligation_map_ref],
                "candidate_ref": edge_row.candidate_ref,
                "source_refs": edge_row.source_refs,
                "drift_or_ambiguity_rows": [
                    {
                        "drift_ref": "drift:v83b:direct-oai-runtime-scope",
                        "drift_kind": "direct_oai_runtime_scope_drift",
                        "semantic_edge_refs": ["semantic-relation:v83b:provider:not-authority"],
                        "artifact_obligation_refs": ["artifact-obligation:v83b:tests"],
                        "source_refs": [
                            "external-support:direct-oai-meta-orchestrator-loop",
                            "external-support:direct-oai-upstream-profile",
                        ],
                        "severity_posture": "warning",
                        "blocking_posture": "warning_only",
                        "required_resolution_horizon": "semantic_review",
                        "limitation_note": (
                            "Direct OAI support remains warning-only scope drift; "
                            "no implementation."
                        ),
                    },
                    {
                        "drift_ref": "drift:v83b:general-artifact-future-family",
                        "drift_kind": "future_family_pressure_unclassified",
                        "semantic_edge_refs": ["semantic-relation:v83b:authority:later-lock"],
                        "artifact_obligation_refs": [],
                        "source_refs": [
                            "docs/DRAFT_NEXT_ARC_OPTIONS_v73.md",
                            "intent:v83a:authority-boundary:later-lock-required",
                        ],
                        "severity_posture": "informational",
                        "blocking_posture": "carried_for_later_review",
                        "required_resolution_horizon": "future_family_review",
                        "limitation_note": (
                            "General digital artifact projection is carried as future "
                            "family pressure with no implementation."
                        ),
                    },
                    {
                        "drift_ref": "drift:v83b:morphic-ux-scope",
                        "drift_kind": "morphic_ux_scope_drift",
                        "semantic_edge_refs": ["semantic-relation:v83b:morphic:scoped"],
                        "artifact_obligation_refs": [],
                        "source_refs": ["docs/support/morphic_ux. v2.md"],
                        "severity_posture": "warning",
                        "blocking_posture": "warning_only",
                        "required_resolution_horizon": "semantic_review",
                        "limitation_note": (
                            "Morphic UX support remains scoped UX projection pressure; "
                            "no implementation."
                        ),
                    },
                ],
                "blocking_posture": "warnings_only",
                "required_next_surface": "v83c_projection_packet_review",
                "guardrail_refs": edge_row.guardrail_refs,
                "limitation_note": (
                    "Drift and ambiguity remain visible for projection review; no implementation."
                ),
            }
        ],
        "drift_register_summary": (
            "V83-B semantic drift and ambiguity register preserves support-scope "
            "drift and future-family ambiguity with no implementation."
        ),
    }
    payload["semantic_drift_ambiguity_register_id"] = _surface_id(
        "repo_semantic_drift_ambiguity_register",
        REPO_SEMANTIC_DRIFT_AMBIGUITY_REGISTER_SCHEMA,
        payload,
        "semantic_drift_ambiguity_register_id",
    )
    return RepoSemanticDriftAmbiguityRegister.model_validate(payload)


def validate_v83b_semantic_edge_obligation_bundle(
    *,
    intent_source_index: RepoIntentSourceIndex,
    semantic_intent_contract: RepoSemanticIntentContract,
    intent_non_implementation_guardrail: RepoIntentNonImplementationGuardrail,
    intent_edge_decomposition: RepoIntentEdgeDecomposition,
    artifact_obligation_map: RepoArtifactObligationMap,
    semantic_drift_ambiguity_register: RepoSemanticDriftAmbiguityRegister,
) -> None:
    validate_v83a_semantic_implementation_spec_bundle(
        intent_source_index=intent_source_index,
        semantic_intent_contract=semantic_intent_contract,
        intent_non_implementation_guardrail=intent_non_implementation_guardrail,
    )
    if (
        intent_edge_decomposition.semantic_intent_contract_id
        != semantic_intent_contract.semantic_intent_contract_id
    ):
        raise ValueError("edge decomposition must reference released V83-A intent contract")
    if (
        intent_edge_decomposition.intent_source_index_id
        != intent_source_index.intent_source_index_id
    ):
        raise ValueError("edge decomposition must reference released V83-A source index")
    if (
        intent_edge_decomposition.intent_non_implementation_guardrail_id
        != intent_non_implementation_guardrail.intent_non_implementation_guardrail_id
    ):
        raise ValueError("edge decomposition must reference released V83-A guardrail")
    if (
        artifact_obligation_map.intent_edge_decomposition_id
        != intent_edge_decomposition.intent_edge_decomposition_id
    ):
        raise ValueError("artifact obligation map must reference edge decomposition")
    if (
        artifact_obligation_map.semantic_intent_contract_id
        != semantic_intent_contract.semantic_intent_contract_id
    ):
        raise ValueError("artifact obligation map must reference released V83-A intent contract")
    if (
        semantic_drift_ambiguity_register.artifact_obligation_map_id
        != artifact_obligation_map.artifact_obligation_map_id
    ):
        raise ValueError("drift register must reference artifact obligation map")
    if (
        semantic_drift_ambiguity_register.intent_edge_decomposition_id
        != intent_edge_decomposition.intent_edge_decomposition_id
    ):
        raise ValueError("drift register must reference edge decomposition")
    if (
        semantic_drift_ambiguity_register.semantic_intent_contract_id
        != semantic_intent_contract.semantic_intent_contract_id
    ):
        raise ValueError("drift register must reference released V83-A intent contract")

    known_sources = {row.source_ref for row in intent_source_index.source_rows}
    source_by_ref = {row.source_ref: row for row in intent_source_index.source_rows}
    known_contracts = {
        row.intent_contract_ref: row for row in semantic_intent_contract.intent_contract_rows
    }
    known_guardrails = {
        row.guardrail_ref for row in intent_non_implementation_guardrail.guardrail_rows
    }
    known_edges: dict[str, RepoSemanticRelationRow] = {}
    known_validations: set[str] = set()
    known_decompositions = {
        row.edge_decomposition_ref: row for row in intent_edge_decomposition.edge_decomposition_rows
    }

    for edge_row in intent_edge_decomposition.edge_decomposition_rows:
        if any(ref not in known_contracts for ref in edge_row.intent_contract_refs):
            raise ValueError("edge decomposition intent refs must be known")
        if any(ref not in known_sources for ref in edge_row.source_refs):
            raise ValueError("edge decomposition source refs must be known")
        if any(ref not in known_guardrails for ref in edge_row.guardrail_refs):
            raise ValueError("edge decomposition guardrail refs must be known")
        roles = {source_by_ref[ref].intent_source_role for ref in edge_row.source_refs}
        if roles.intersection(_GENERATED_SOURCE_ROLES):
            generated_rows = [
                source_by_ref[ref]
                for ref in edge_row.source_refs
                if source_by_ref[ref].intent_source_role in _GENERATED_SOURCE_ROLES
            ]
            if any(
                row.generation_posture == "generated_from_unbounded_context"
                for row in generated_rows
            ):
                raise ValueError("generated spec edges require bounded V83-A provenance")
        known_validations.update(row.validation_need_ref for row in edge_row.validation_need_rows)
        known_edges.update(
            {row.semantic_relation_ref: row for row in edge_row.semantic_relation_rows}
        )

    obligation_maps = {
        row.obligation_map_ref: row for row in artifact_obligation_map.obligation_map_rows
    }
    known_obligations: dict[str, RepoArtifactObligationRow] = {}
    for obligation_map_row in artifact_obligation_map.obligation_map_rows:
        if any(ref not in known_contracts for ref in obligation_map_row.intent_contract_refs):
            raise ValueError("obligation map intent refs must be known")
        if any(
            ref not in known_decompositions for ref in obligation_map_row.edge_decomposition_refs
        ):
            raise ValueError("obligation map edge decomposition refs must be known")
        if any(ref not in known_sources for ref in obligation_map_row.source_refs):
            raise ValueError("obligation map source refs must be known")
        if any(ref not in known_guardrails for ref in obligation_map_row.guardrail_refs):
            raise ValueError("obligation map guardrail refs must be known")
        for obligation_row in obligation_map_row.artifact_obligation_rows:
            known_obligations[obligation_row.artifact_obligation_ref] = obligation_row
            if any(ref not in known_edges for ref in obligation_row.semantic_edge_refs):
                raise ValueError("artifact obligations must reference known semantic edges")
            for edge_ref in obligation_row.semantic_edge_refs:
                relation = known_edges[edge_ref]
                if (
                    relation.relation_kind == "non_goal_of"
                    and obligation_row.required_change_posture
                    == "change_required_for_later_implementation_spec"
                ):
                    raise ValueError("non-goals cannot become implementation obligations")
                if (
                    relation.relation_kind == "authority_requires"
                    and obligation_row.required_change_posture
                    == "change_required_for_later_implementation_spec"
                    and obligation_row.artifact_kind == "code_module"
                ):
                    raise ValueError("authority boundaries cannot become code permissions")
            for evidence_row in obligation_row.acceptance_evidence_requirements:
                if any(ref not in known_edges for ref in evidence_row.semantic_edge_refs):
                    raise ValueError("acceptance evidence must reference known semantic edges")
                if any(ref not in known_validations for ref in evidence_row.validation_need_refs):
                    raise ValueError("acceptance evidence must reference known validation needs")

    for drift_register_row in semantic_drift_ambiguity_register.drift_register_rows:
        if any(ref not in known_contracts for ref in drift_register_row.intent_contract_refs):
            raise ValueError("drift register intent refs must be known")
        if any(
            ref not in known_decompositions for ref in drift_register_row.edge_decomposition_refs
        ):
            raise ValueError("drift register decomposition refs must be known")
        if any(ref not in obligation_maps for ref in drift_register_row.obligation_map_refs):
            raise ValueError("drift register obligation refs must be known")
        if any(ref not in known_guardrails for ref in drift_register_row.guardrail_refs):
            raise ValueError("drift register guardrail refs must be known")
        for drift_row in drift_register_row.drift_or_ambiguity_rows:
            if any(ref not in known_edges for ref in drift_row.semantic_edge_refs):
                raise ValueError("drift rows must reference known semantic edges")
            if any(ref not in known_obligations for ref in drift_row.artifact_obligation_refs):
                raise ValueError("drift rows must reference known artifact obligations")
            if any(ref not in known_sources for ref in drift_row.source_refs):
                raise ValueError("drift rows must reference known source rows")


def derive_v83b_semantic_edge_obligation_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoIntentSourceIndex,
    RepoSemanticIntentContract,
    RepoIntentNonImplementationGuardrail,
    RepoIntentEdgeDecomposition,
    RepoArtifactObligationMap,
    RepoSemanticDriftAmbiguityRegister,
]:
    source_index, contract, guardrail = derive_v83a_semantic_implementation_spec_bundle(
        repo_root=repo_root
    )
    edge_decomposition = derive_v83b_repo_intent_edge_decomposition(
        repo_root=repo_root,
        intent_source_index=source_index,
        semantic_intent_contract=contract,
        intent_non_implementation_guardrail=guardrail,
    )
    obligation_map = derive_v83b_repo_artifact_obligation_map(
        repo_root=repo_root,
        semantic_intent_contract=contract,
        intent_edge_decomposition=edge_decomposition,
    )
    drift_register = derive_v83b_repo_semantic_drift_ambiguity_register(
        repo_root=repo_root,
        semantic_intent_contract=contract,
        intent_edge_decomposition=edge_decomposition,
        artifact_obligation_map=obligation_map,
    )
    validate_v83b_semantic_edge_obligation_bundle(
        intent_source_index=source_index,
        semantic_intent_contract=contract,
        intent_non_implementation_guardrail=guardrail,
        intent_edge_decomposition=edge_decomposition,
        artifact_obligation_map=obligation_map,
        semantic_drift_ambiguity_register=drift_register,
    )
    return (
        source_index,
        contract,
        guardrail,
        edge_decomposition,
        obligation_map,
        drift_register,
    )


class RepoImplementationSpecRow(_CartographyBase):
    implementation_spec_ref: str
    artifact_obligation_refs: list[str] = Field(min_length=1)
    target_artifact_kind: ArtifactKind
    target_surface_refs: list[str] = Field(min_length=1)
    required_change_summary: str
    required_validation_refs: list[str] = Field(min_length=1)
    explicit_non_goals: list[str] = Field(min_length=1)
    semantic_preservation_refs: list[str] = Field(min_length=1)
    acceptance_evidence_requirements: list[str] = Field(min_length=1)
    implementation_execution_posture: ImplementationExecutionPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_implementation_spec_row(self) -> RepoImplementationSpecRow:
        _repo_ref(self.implementation_spec_ref, field_name="implementation_spec_ref")
        for field_name in (
            "artifact_obligation_refs",
            "target_surface_refs",
            "required_validation_refs",
            "explicit_non_goals",
            "semantic_preservation_refs",
            "acceptance_evidence_requirements",
        ):
            object.__setattr__(
                self,
                field_name,
                _validate_repo_refs(getattr(self, field_name), field_name=field_name),
            )
        if any(target in _BROAD_ARTIFACT_TARGETS for target in self.target_surface_refs):
            raise ValueError("implementation specs require bounded target surfaces")
        _non_empty(self.required_change_summary, field_name="required_change_summary")
        if self.implementation_execution_posture == "no_execution_performed_by_v83":
            _reject_v83c_execution_claim(
                self.required_change_summary,
                field_name="required_change_summary",
            )
        _reject_v83c_execution_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoProjectionProvenanceRow(_CartographyBase):
    projection_provenance_ref: str
    projection_actor_kind: ProjectionActorKind
    model_or_agent_profile_refs: list[str] = Field(default_factory=list)
    prompt_context_refs: list[str] = Field(default_factory=list)
    input_intent_contract_refs: list[str] = Field(min_length=1)
    input_edge_decomposition_refs: list[str] = Field(min_length=1)
    input_obligation_map_refs: list[str] = Field(min_length=1)
    generated_spec_refs: list[str] = Field(default_factory=list)
    reviewer_amendment_refs: list[str] = Field(default_factory=list)
    generation_scope_posture: ProjectionGenerationScopePosture
    review_status: ProjectionReviewStatus
    non_authority_posture: ProjectionNonAuthorityPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_projection_provenance_row(self) -> RepoProjectionProvenanceRow:
        _repo_ref(self.projection_provenance_ref, field_name="projection_provenance_ref")
        for field_name in (
            "model_or_agent_profile_refs",
            "prompt_context_refs",
            "input_intent_contract_refs",
            "input_edge_decomposition_refs",
            "input_obligation_map_refs",
            "generated_spec_refs",
            "reviewer_amendment_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _validate_repo_refs(getattr(self, field_name), field_name=field_name),
            )
        if self.projection_actor_kind in {"model", "agent"}:
            if not self.model_or_agent_profile_refs or not self.prompt_context_refs:
                raise ValueError(
                    "model/agent projection provenance requires profile and prompt refs"
                )
            if not self.generated_spec_refs:
                raise ValueError("model/agent projection provenance requires generated spec refs")
            if self.non_authority_posture != "candidate_projection_only":
                raise ValueError("model/agent projection provenance must remain candidate-only")
            if self.generation_scope_posture not in {
                "bounded_to_released_v83_inputs",
                "bounded_to_prompt_context",
            }:
                raise ValueError("model/agent projection provenance requires bounded context")
        if self.review_status in {
            "blocked_by_missing_context",
            "blocked_by_semantic_drift",
            "blocked_by_authority_gap",
        }:
            if self.non_authority_posture == "review_only_no_authority":
                raise ValueError("blocked projection provenance cannot be review-ready")
        _reject_v83c_execution_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoSpecReviewChecklistRow(_CartographyBase):
    review_check_ref: str
    implementation_spec_refs: list[str] = Field(min_length=1)
    semantic_edge_refs: list[str] = Field(default_factory=list)
    artifact_obligation_refs: list[str] = Field(default_factory=list)
    check_kind: ReviewCheckKind
    check_posture: ReviewCheckPosture
    source_refs: list[str] = Field(min_length=1)
    blocking_posture: ReviewCheckBlockingPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_review_check_row(self) -> RepoSpecReviewChecklistRow:
        _repo_ref(self.review_check_ref, field_name="review_check_ref")
        for field_name in (
            "implementation_spec_refs",
            "semantic_edge_refs",
            "artifact_obligation_refs",
            "source_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _validate_repo_refs(getattr(self, field_name), field_name=field_name),
            )
        if self.check_posture == "blocked" and self.blocking_posture != "blocking":
            raise ValueError("blocked review checks must remain blocking")
        if self.check_posture == "passed_for_review_only" and self.blocking_posture == "blocking":
            raise ValueError("passed review checks cannot carry blocking posture")
        if self.check_kind in {
            "edge_coverage_check",
            "validation_evidence_check",
            "reject_fixture_check",
        } and not self.semantic_edge_refs:
            raise ValueError("semantic review checks require semantic edge refs")
        _reject_v83c_execution_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoImplementationSpecQualityGateRow(_CartographyBase):
    quality_gate_ref: str
    projection_packet_refs: list[str] = Field(min_length=1)
    required_check_refs: list[str] = Field(min_length=1)
    gate_posture: QualityGatePosture
    ready_basis_posture: ProjectionReadyBasisPosture
    carried_blocker_refs: list[str] = Field(default_factory=list)
    carried_warning_refs: list[str] = Field(default_factory=list)
    non_implementation_guardrail: NonImplementationPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_quality_gate_row(self) -> RepoImplementationSpecQualityGateRow:
        _repo_ref(self.quality_gate_ref, field_name="quality_gate_ref")
        for field_name in (
            "projection_packet_refs",
            "required_check_refs",
            "carried_blocker_refs",
            "carried_warning_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _validate_repo_refs(getattr(self, field_name), field_name=field_name),
            )
        if self.gate_posture in {
            "ready_for_later_implementation_slice_review",
            "ready_with_nonblocking_warnings",
        }:
            if self.ready_basis_posture not in {
                "ready_no_blockers",
                "ready_with_nonblocking_warnings",
            }:
                raise ValueError("ready quality gates require blocker-aware ready basis")
            if self.carried_blocker_refs:
                raise ValueError("ready quality gates cannot carry blockers")
        if self.gate_posture == "ready_for_later_implementation_slice_review":
            if self.non_implementation_guardrail != "non_implementation_guardrail_active":
                raise ValueError("quality gates remain non-implementation")
        _reject_v83c_execution_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoImplementationSpecProjectionPacketRow(_CartographyBase):
    projection_packet_ref: str
    intent_contract_refs: list[str] = Field(min_length=1)
    edge_decomposition_refs: list[str] = Field(min_length=1)
    obligation_map_refs: list[str] = Field(min_length=1)
    drift_register_refs: list[str] = Field(min_length=1)
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    implementation_spec_rows: list[RepoImplementationSpecRow] = Field(min_length=1)
    projection_provenance_rows: list[RepoProjectionProvenanceRow] = Field(min_length=1)
    spec_review_checklist_rows: list[RepoSpecReviewChecklistRow] = Field(min_length=1)
    implementation_spec_quality_gate_rows: list[RepoImplementationSpecQualityGateRow] = Field(
        min_length=1
    )
    projection_posture: ProjectionPacketPosture
    semantic_coverage_posture: SemanticCoveragePosture
    ready_basis_posture: ProjectionReadyBasisPosture
    carried_blocker_refs: list[str] = Field(default_factory=list)
    carried_warning_refs: list[str] = Field(default_factory=list)
    non_implementation_posture: NonImplementationPosture
    guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_projection_packet_row(self) -> RepoImplementationSpecProjectionPacketRow:
        _repo_ref(self.projection_packet_ref, field_name="projection_packet_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "intent_contract_refs",
            "edge_decomposition_refs",
            "obligation_map_refs",
            "drift_register_refs",
            "source_refs",
            "carried_blocker_refs",
            "carried_warning_refs",
            "guardrail_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _validate_repo_refs(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "implementation_spec_rows",
            _sorted_unique_by_ref(
                self.implementation_spec_rows,
                attr="implementation_spec_ref",
                field_name="implementation_spec_rows",
            ),
        )
        object.__setattr__(
            self,
            "projection_provenance_rows",
            _sorted_unique_by_ref(
                self.projection_provenance_rows,
                attr="projection_provenance_ref",
                field_name="projection_provenance_rows",
            ),
        )
        object.__setattr__(
            self,
            "spec_review_checklist_rows",
            _sorted_unique_by_ref(
                self.spec_review_checklist_rows,
                attr="review_check_ref",
                field_name="spec_review_checklist_rows",
            ),
        )
        object.__setattr__(
            self,
            "implementation_spec_quality_gate_rows",
            _sorted_unique_by_ref(
                self.implementation_spec_quality_gate_rows,
                attr="quality_gate_ref",
                field_name="implementation_spec_quality_gate_rows",
            ),
        )
        spec_refs = {row.implementation_spec_ref for row in self.implementation_spec_rows}
        check_refs = {row.review_check_ref for row in self.spec_review_checklist_rows}
        for check_row in self.spec_review_checklist_rows:
            if any(ref not in spec_refs for ref in check_row.implementation_spec_refs):
                raise ValueError(
                    "projection review checks must reference known implementation specs"
                )
        for gate_row in self.implementation_spec_quality_gate_rows:
            if any(ref not in check_refs for ref in gate_row.required_check_refs):
                raise ValueError("quality gates must reference known review checks")
            if any(ref != self.projection_packet_ref for ref in gate_row.projection_packet_refs):
                raise ValueError("quality gates must reference the containing projection packet")
        if self.projection_posture in {
            "projection_packet_ready_for_review",
            "projection_packet_ready_with_nonblocking_warnings",
        }:
            if self.ready_basis_posture not in {
                "ready_no_blockers",
                "ready_with_nonblocking_warnings",
            }:
                raise ValueError("ready projection packets require ready basis")
            if self.carried_blocker_refs:
                raise ValueError("ready projection packets cannot carry blockers")
            required_checks = {
                "source_binding_check",
                "non_goal_preservation_check",
                "authority_boundary_check",
                "target_surface_boundedness_check",
                "edge_coverage_check",
                "validation_evidence_check",
                "reject_fixture_check",
                "generated_spec_provenance_check",
                "semantic_drift_check",
                "future_family_boundary_check",
            }
            observed_checks = {row.check_kind for row in self.spec_review_checklist_rows}
            if not required_checks.issubset(observed_checks):
                raise ValueError("ready projection packets require complete review checklist")
            if not any(
                row.gate_posture == "ready_for_later_implementation_slice_review"
                for row in self.implementation_spec_quality_gate_rows
            ):
                raise ValueError("ready projection packets require a ready quality gate")
        if self.semantic_coverage_posture == "all_required_edges_covered":
            if not any(
                row.check_kind == "edge_coverage_check"
                for row in self.spec_review_checklist_rows
            ):
                raise ValueError("semantic coverage requires edge coverage check")
        if self.non_implementation_posture != "non_implementation_guardrail_active":
            raise ValueError("projection packets remain non-implementation")
        _reject_v83c_execution_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoImplementationSpecProjectionPacket(_CartographyBase):
    schema: Literal["repo_implementation_spec_projection_packet@1"] = (
        REPO_IMPLEMENTATION_SPEC_PROJECTION_PACKET_SCHEMA
    )
    implementation_spec_projection_packet_id: str
    semantic_intent_contract_id: str
    intent_edge_decomposition_id: str
    artifact_obligation_map_id: str
    semantic_drift_ambiguity_register_id: str
    intent_non_implementation_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    projection_packet_rows: list[RepoImplementationSpecProjectionPacketRow] = Field(min_length=1)
    projection_packet_summary: str

    @model_validator(mode="after")
    def _validate_projection_packet(self) -> RepoImplementationSpecProjectionPacket:
        object.__setattr__(
            self,
            "projection_packet_rows",
            _sorted_unique_by_ref(
                self.projection_packet_rows,
                attr="projection_packet_ref",
                field_name="projection_packet_rows",
            ),
        )
        _require_terms(
            self.projection_packet_summary,
            field_name="projection_packet_summary",
            terms=("projection packet", "review", "no implementation"),
        )
        expected_id = _surface_id(
            "repo_implementation_spec_projection_packet",
            self.schema,
            self.model_dump(mode="json"),
            "implementation_spec_projection_packet_id",
        )
        if self.implementation_spec_projection_packet_id != expected_id:
            raise ValueError(
                "implementation_spec_projection_packet_id does not match canonical hash"
            )
        return self


class RepoIntentToWorkPacketHandoffRow(_CartographyBase):
    handoff_ref: str
    candidate_ref: str
    projection_packet_refs: list[str] = Field(min_length=1)
    intent_contract_refs: list[str] = Field(min_length=1)
    artifact_obligation_refs: list[str] = Field(default_factory=list)
    carried_drift_refs: list[str] = Field(default_factory=list)
    handoff_target: WorkPacketHandoffTarget
    handoff_subject_horizon: WorkPacketHandoffSubjectHorizon
    handoff_posture: WorkPacketHandoffPosture
    required_later_authority_refs: list[str] = Field(min_length=1)
    work_packet_authority_posture: WorkPacketAuthorityPosture
    implementation_lock_requirement: ImplementationLockRequirement
    work_packet_execution_posture: ImplementationExecutionPosture
    implementation_execution_posture: ImplementationExecutionPosture
    meta_orchestrator_runtime_posture: MetaOrchestratorRuntimePosture
    guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_work_packet_handoff_row(self) -> RepoIntentToWorkPacketHandoffRow:
        _repo_ref(self.handoff_ref, field_name="handoff_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "projection_packet_refs",
            "intent_contract_refs",
            "artifact_obligation_refs",
            "carried_drift_refs",
            "required_later_authority_refs",
            "guardrail_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _validate_repo_refs(getattr(self, field_name), field_name=field_name),
            )
        if self.handoff_posture in {
            "ready_for_later_review",
            "ready_with_nonblocking_warnings",
        }:
            if self.work_packet_authority_posture != "work_packet_requires_later_lock":
                raise ValueError("ready work-packet handoffs require later lock authority")
            if self.implementation_lock_requirement != "canonical_starter_lock_required":
                raise ValueError("ready work-packet handoffs require canonical later lock")
        if self.handoff_target == "future_meta_orchestrator_workflow_review":
            if self.meta_orchestrator_runtime_posture != "workflow_transition_review_only":
                raise ValueError("meta-orchestrator handoffs remain workflow review only")
        if self.work_packet_execution_posture != "no_execution_performed_by_v83":
            raise ValueError("V83-C handoffs must not execute work packets")
        if self.implementation_execution_posture != "no_execution_performed_by_v83":
            raise ValueError("V83-C handoffs must not execute implementation")
        _reject_v83c_execution_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoIntentToWorkPacketHandoff(_CartographyBase):
    schema: Literal["repo_intent_to_work_packet_handoff@1"] = (
        REPO_INTENT_TO_WORK_PACKET_HANDOFF_SCHEMA
    )
    intent_to_work_packet_handoff_id: str
    implementation_spec_projection_packet_id: str
    semantic_intent_contract_id: str
    artifact_obligation_map_id: str
    semantic_drift_ambiguity_register_id: str
    intent_non_implementation_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    handoff_rows: list[RepoIntentToWorkPacketHandoffRow] = Field(min_length=1)
    handoff_summary: str

    @model_validator(mode="after")
    def _validate_work_packet_handoff(self) -> RepoIntentToWorkPacketHandoff:
        object.__setattr__(
            self,
            "handoff_rows",
            _sorted_unique_by_ref(self.handoff_rows, attr="handoff_ref", field_name="handoff_rows"),
        )
        _require_terms(
            self.handoff_summary,
            field_name="handoff_summary",
            terms=("later review", "later lock", "no implementation"),
        )
        expected_id = _surface_id(
            "repo_intent_to_work_packet_handoff",
            self.schema,
            self.model_dump(mode="json"),
            "intent_to_work_packet_handoff_id",
        )
        if self.intent_to_work_packet_handoff_id != expected_id:
            raise ValueError("intent_to_work_packet_handoff_id does not match canonical hash")
        return self


class RepoSemanticImplementationSpecFamilyCloseoutAlignment(_CartographyBase):
    schema: Literal["repo_semantic_implementation_spec_family_closeout_alignment@1"] = (
        REPO_SEMANTIC_IMPLEMENTATION_SPEC_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
    )
    semantic_implementation_spec_family_closeout_alignment_id: str
    implementation_spec_projection_packet_id: str
    intent_to_work_packet_handoff_id: str
    family: Literal["V83"]
    closed_by_arc: Literal["vNext+235"]
    closed_slice_ladder: list[SemanticSpecClosedSlice] = Field(min_length=3)
    shipped_record_shapes: list[SemanticSpecShippedRecordShape] = Field(min_length=1)
    consumed_source_families: list[SemanticSpecConsumedFamily] = Field(min_length=1)
    family_closed_on_main: Literal["closed_after_v83c_merge"]
    future_family_authority: Literal["next_selector_required"]
    unselected_future_surfaces: list[SemanticSpecUnselectedFutureSurface] = Field(min_length=1)
    semantic_implementation_spec_boundary: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_semantic_spec_family_closeout(
        self,
    ) -> RepoSemanticImplementationSpecFamilyCloseoutAlignment:
        for field_name in (
            "closed_slice_ladder",
            "shipped_record_shapes",
            "consumed_source_families",
            "unselected_future_surfaces",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        if self.closed_slice_ladder != ["V83-A", "V83-B", "V83-C"]:
            raise ValueError("semantic implementation-spec closeout must close V83-A/B/C")
        if "v84_selection" not in self.unselected_future_surfaces:
            raise ValueError("semantic implementation-spec closeout must not select V84")
        _require_terms(
            self.semantic_implementation_spec_boundary,
            field_name="semantic_implementation_spec_boundary",
            terms=("projection packet", "no implementation", "no v84 selection"),
        )
        _reject_v83c_execution_claim(
            self.semantic_implementation_spec_boundary,
            field_name="semantic_implementation_spec_boundary",
        )
        _reject_v83c_execution_claim(self.limitation_note, field_name="limitation_note")
        expected_id = _surface_id(
            "repo_semantic_implementation_spec_family_closeout_alignment",
            self.schema,
            self.model_dump(mode="json"),
            "semantic_implementation_spec_family_closeout_alignment_id",
        )
        if self.semantic_implementation_spec_family_closeout_alignment_id != expected_id:
            raise ValueError(
                "semantic_implementation_spec_family_closeout_alignment_id "
                "does not match canonical hash"
            )
        return self


def _v83b_released_refs(
    *,
    intent_edge_decomposition: RepoIntentEdgeDecomposition,
    artifact_obligation_map: RepoArtifactObligationMap,
    semantic_drift_ambiguity_register: RepoSemanticDriftAmbiguityRegister,
) -> tuple[
    RepoIntentEdgeDecompositionRow,
    RepoArtifactObligationMapRow,
    RepoSemanticDriftAmbiguityRegisterRow,
]:
    if len(intent_edge_decomposition.edge_decomposition_rows) != 1:
        raise ValueError("V83-C derivation expects one V83-B edge decomposition row")
    if len(artifact_obligation_map.obligation_map_rows) != 1:
        raise ValueError("V83-C derivation expects one V83-B obligation map row")
    if len(semantic_drift_ambiguity_register.drift_register_rows) != 1:
        raise ValueError("V83-C derivation expects one V83-B drift register row")
    return (
        intent_edge_decomposition.edge_decomposition_rows[0],
        artifact_obligation_map.obligation_map_rows[0],
        semantic_drift_ambiguity_register.drift_register_rows[0],
    )


def derive_v83c_repo_implementation_spec_projection_packet(
    *,
    repo_root: Path | None = None,
    semantic_intent_contract: RepoSemanticIntentContract | None = None,
    intent_non_implementation_guardrail: RepoIntentNonImplementationGuardrail | None = None,
    intent_edge_decomposition: RepoIntentEdgeDecomposition | None = None,
    artifact_obligation_map: RepoArtifactObligationMap | None = None,
    semantic_drift_ambiguity_register: RepoSemanticDriftAmbiguityRegister | None = None,
) -> RepoImplementationSpecProjectionPacket:
    _ = repo_root
    if any(
        item is None
        for item in (
            semantic_intent_contract,
            intent_non_implementation_guardrail,
            intent_edge_decomposition,
            artifact_obligation_map,
            semantic_drift_ambiguity_register,
        )
    ):
        (
            _source_index,
            semantic_intent_contract,
            intent_non_implementation_guardrail,
            intent_edge_decomposition,
            artifact_obligation_map,
            semantic_drift_ambiguity_register,
        ) = derive_v83b_semantic_edge_obligation_bundle(repo_root=repo_root)
    assert semantic_intent_contract is not None
    assert intent_non_implementation_guardrail is not None
    assert intent_edge_decomposition is not None
    assert artifact_obligation_map is not None
    assert semantic_drift_ambiguity_register is not None
    edge_row, obligation_map_row, drift_register_row = _v83b_released_refs(
        intent_edge_decomposition=intent_edge_decomposition,
        artifact_obligation_map=artifact_obligation_map,
        semantic_drift_ambiguity_register=semantic_drift_ambiguity_register,
    )
    eligible = semantic_intent_contract.intent_contract_rows[0]
    source_refs = sorted(set(edge_row.source_refs).union(obligation_map_row.source_refs))
    guardrail_refs = sorted(
        {row.guardrail_ref for row in intent_non_implementation_guardrail.guardrail_rows}
    )
    obligations = sorted(
        obligation_map_row.artifact_obligation_rows,
        key=lambda row: row.artifact_obligation_ref,
    )
    semantic_refs = sorted(
        {
            relation.semantic_relation_ref
            for relation in edge_row.semantic_relation_rows
        }
    )
    obligation_refs = [
        obligation.artifact_obligation_ref
        for obligation in obligations
    ]
    spec_rows: list[dict[str, object]] = []
    for obligation in obligations:
        spec_rows.append(
            {
                "implementation_spec_ref": (
                    "implementation-spec:v83c:"
                    + obligation.artifact_obligation_ref.split(":")[-1]
                ),
                "artifact_obligation_refs": [obligation.artifact_obligation_ref],
                "target_artifact_kind": obligation.artifact_kind,
                "target_surface_refs": obligation.target_surface_refs,
                "required_change_summary": (
                    "Later implementation spec must preserve source binding, "
                    "semantic edge coverage, reject fixtures, and non-goals for review only."
                ),
                "required_validation_refs": sorted(
                    {
                        evidence_ref
                        for evidence in obligation.acceptance_evidence_requirements
                        for evidence_ref in evidence.validation_need_refs
                    }
                ),
                "explicit_non_goals": sorted(eligible.non_goal_refs),
                "semantic_preservation_refs": obligation.semantic_edge_refs,
                "acceptance_evidence_requirements": sorted(
                    {
                        evidence.evidence_requirement_ref
                        for evidence in obligation.acceptance_evidence_requirements
                    }
                ),
                "implementation_execution_posture": "no_execution_performed_by_v83",
                "limitation_note": (
                    "Implementation spec row is a later-review requirement only; "
                    "no implementation and no execution."
                ),
            }
        )
    spec_refs = sorted(row["implementation_spec_ref"] for row in spec_rows)
    checklist_rows = [
        {
            "review_check_ref": "review-check:v83c:authority-boundary",
            "implementation_spec_refs": spec_refs,
            "semantic_edge_refs": ["semantic-relation:v83b:authority:later-lock"],
            "artifact_obligation_refs": obligation_refs,
            "check_kind": "authority_boundary_check",
            "check_posture": "passed_for_review_only",
            "source_refs": sorted(eligible.authority_boundary_refs),
            "blocking_posture": "not_applicable",
            "limitation_note": (
                "Authority boundary check passes for review only; no implementation."
            ),
        },
        {
            "review_check_ref": "review-check:v83c:edge-coverage",
            "implementation_spec_refs": spec_refs,
            "semantic_edge_refs": semantic_refs,
            "artifact_obligation_refs": obligation_refs,
            "check_kind": "edge_coverage_check",
            "check_posture": "passed_for_review_only",
            "source_refs": source_refs,
            "blocking_posture": "not_applicable",
            "limitation_note": (
                "Edge coverage check is evidence for review only; no implementation."
            ),
        },
        {
            "review_check_ref": "review-check:v83c:future-family-boundary",
            "implementation_spec_refs": spec_refs,
            "semantic_edge_refs": ["semantic-relation:v83b:authority:later-lock"],
            "artifact_obligation_refs": [],
            "check_kind": "future_family_boundary_check",
            "check_posture": "warning",
            "source_refs": ["docs/DRAFT_NEXT_ARC_OPTIONS_v73.md"],
            "blocking_posture": "warning_only",
            "limitation_note": "Future family pressure remains warning-only with no V84 selection.",
        },
        {
            "review_check_ref": "review-check:v83c:generated-provenance",
            "implementation_spec_refs": spec_refs,
            "semantic_edge_refs": [],
            "artifact_obligation_refs": [],
            "check_kind": "generated_spec_provenance_check",
            "check_posture": "passed_for_review_only",
            "source_refs": ["intent:v83a:generated-spec:absence-marker"],
            "blocking_posture": "not_applicable",
            "limitation_note": "No model/agent generated spec is authoritative; no implementation.",
        },
        {
            "review_check_ref": "review-check:v83c:non-goal-preservation",
            "implementation_spec_refs": spec_refs,
            "semantic_edge_refs": ["semantic-relation:v83b:non-goal:no-implementation"],
            "artifact_obligation_refs": [],
            "check_kind": "non_goal_preservation_check",
            "check_posture": "passed_for_review_only",
            "source_refs": sorted(eligible.non_goal_refs),
            "blocking_posture": "not_applicable",
            "limitation_note": "Non-goals remain preserved for review; no implementation.",
        },
        {
            "review_check_ref": "review-check:v83c:reject-fixture",
            "implementation_spec_refs": spec_refs,
            "semantic_edge_refs": semantic_refs,
            "artifact_obligation_refs": obligation_refs,
            "check_kind": "reject_fixture_check",
            "check_posture": "passed_for_review_only",
            "source_refs": source_refs,
            "blocking_posture": "not_applicable",
            "limitation_note": "Reject fixtures are required evidence, not semantic truth.",
        },
        {
            "review_check_ref": "review-check:v83c:semantic-drift",
            "implementation_spec_refs": spec_refs,
            "semantic_edge_refs": semantic_refs,
            "artifact_obligation_refs": obligation_refs,
            "check_kind": "semantic_drift_check",
            "check_posture": "warning",
            "source_refs": drift_register_row.source_refs,
            "blocking_posture": "warning_only",
            "limitation_note": "Drift warnings remain visible and nonblocking; no implementation.",
        },
        {
            "review_check_ref": "review-check:v83c:source-binding",
            "implementation_spec_refs": spec_refs,
            "semantic_edge_refs": semantic_refs,
            "artifact_obligation_refs": obligation_refs,
            "check_kind": "source_binding_check",
            "check_posture": "passed_for_review_only",
            "source_refs": source_refs,
            "blocking_posture": "not_applicable",
            "limitation_note": "Source binding check passes for review only; no implementation.",
        },
        {
            "review_check_ref": "review-check:v83c:target-surface-boundedness",
            "implementation_spec_refs": spec_refs,
            "semantic_edge_refs": semantic_refs,
            "artifact_obligation_refs": obligation_refs,
            "check_kind": "target_surface_boundedness_check",
            "check_posture": "passed_for_review_only",
            "source_refs": source_refs,
            "blocking_posture": "not_applicable",
            "limitation_note": "Target surfaces are bounded for later review; no implementation.",
        },
        {
            "review_check_ref": "review-check:v83c:validation-evidence",
            "implementation_spec_refs": spec_refs,
            "semantic_edge_refs": semantic_refs,
            "artifact_obligation_refs": obligation_refs,
            "check_kind": "validation_evidence_check",
            "check_posture": "passed_for_review_only",
            "source_refs": source_refs,
            "blocking_posture": "not_applicable",
            "limitation_note": "Validation evidence is edge-bound and not semantic truth.",
        },
    ]
    carried_warnings = sorted(
        drift.drift_ref
        for drift in drift_register_row.drift_or_ambiguity_rows
        if drift.blocking_posture in {"warning_only", "carried_for_later_review"}
    )
    packet_ref = "projection-packet:v83c:intent-to-spec"
    payload = {
        "schema": REPO_IMPLEMENTATION_SPEC_PROJECTION_PACKET_SCHEMA,
        "implementation_spec_projection_packet_id": "",
        "semantic_intent_contract_id": semantic_intent_contract.semantic_intent_contract_id,
        "intent_edge_decomposition_id": intent_edge_decomposition.intent_edge_decomposition_id,
        "artifact_obligation_map_id": artifact_obligation_map.artifact_obligation_map_id,
        "semantic_drift_ambiguity_register_id": (
            semantic_drift_ambiguity_register.semantic_drift_ambiguity_register_id
        ),
        "intent_non_implementation_guardrail_id": (
            intent_non_implementation_guardrail.intent_non_implementation_guardrail_id
        ),
        "review_id": intent_edge_decomposition.review_id,
        "snapshot_id": "vNext+234-semantic-edge-obligation-closeout",
        "source_set_id": intent_edge_decomposition.source_set_id,
        "projection_packet_rows": [
            {
                "projection_packet_ref": packet_ref,
                "intent_contract_refs": edge_row.intent_contract_refs,
                "edge_decomposition_refs": [edge_row.edge_decomposition_ref],
                "obligation_map_refs": [obligation_map_row.obligation_map_ref],
                "drift_register_refs": [drift_register_row.drift_register_ref],
                "candidate_ref": edge_row.candidate_ref,
                "source_refs": source_refs,
                "implementation_spec_rows": sorted(
                    spec_rows,
                    key=lambda row: row["implementation_spec_ref"],
                ),
                "projection_provenance_rows": [
                    {
                        "projection_provenance_ref": "projection-provenance:v83c:reviewer",
                        "projection_actor_kind": "reviewer",
                        "model_or_agent_profile_refs": [],
                        "prompt_context_refs": [],
                        "input_intent_contract_refs": edge_row.intent_contract_refs,
                        "input_edge_decomposition_refs": [edge_row.edge_decomposition_ref],
                        "input_obligation_map_refs": [obligation_map_row.obligation_map_ref],
                        "generated_spec_refs": [],
                        "reviewer_amendment_refs": ["docs/LOCKED_CONTINUATION_vNEXT_PLUS235.md"],
                        "generation_scope_posture": "not_generated",
                        "review_status": "reviewed_for_artifact_obligation_coverage",
                        "non_authority_posture": "review_only_no_authority",
                        "limitation_note": (
                            "Reviewer projection provenance is review-only; "
                            "no implementation."
                        ),
                    }
                ],
                "spec_review_checklist_rows": sorted(
                    checklist_rows,
                    key=lambda row: row["review_check_ref"],
                ),
                "implementation_spec_quality_gate_rows": [
                    {
                        "quality_gate_ref": "quality-gate:v83c:later-implementation-slice-review",
                        "projection_packet_refs": [packet_ref],
                        "required_check_refs": sorted(
                            row["review_check_ref"] for row in checklist_rows
                        ),
                        "gate_posture": "ready_for_later_implementation_slice_review",
                        "ready_basis_posture": "ready_no_blockers",
                        "carried_blocker_refs": [],
                        "carried_warning_refs": carried_warnings,
                        "non_implementation_guardrail": "non_implementation_guardrail_active",
                        "limitation_note": (
                            "Quality gate is ready for later implementation slice review "
                            "only; no implementation."
                        ),
                    }
                ],
                "projection_posture": "projection_packet_ready_for_review",
                "semantic_coverage_posture": "all_required_edges_covered",
                "ready_basis_posture": "ready_no_blockers",
                "carried_blocker_refs": [],
                "carried_warning_refs": carried_warnings,
                "non_implementation_posture": "non_implementation_guardrail_active",
                "guardrail_refs": guardrail_refs,
                "limitation_note": (
                    "V83-C projection packet is ready for later review with no implementation."
                ),
            }
        ],
        "projection_packet_summary": (
            "V83-C projection packet packages semantic implementation spec obligations "
            "for review with no implementation."
        ),
    }
    payload["implementation_spec_projection_packet_id"] = _surface_id(
        "repo_implementation_spec_projection_packet",
        REPO_IMPLEMENTATION_SPEC_PROJECTION_PACKET_SCHEMA,
        payload,
        "implementation_spec_projection_packet_id",
    )
    return RepoImplementationSpecProjectionPacket.model_validate(payload)


def derive_v83c_repo_intent_to_work_packet_handoff(
    *,
    repo_root: Path | None = None,
    semantic_intent_contract: RepoSemanticIntentContract | None = None,
    intent_non_implementation_guardrail: RepoIntentNonImplementationGuardrail | None = None,
    artifact_obligation_map: RepoArtifactObligationMap | None = None,
    semantic_drift_ambiguity_register: RepoSemanticDriftAmbiguityRegister | None = None,
    implementation_spec_projection_packet: RepoImplementationSpecProjectionPacket | None = None,
) -> RepoIntentToWorkPacketHandoff:
    _ = repo_root
    if any(
        item is None
        for item in (
            semantic_intent_contract,
            intent_non_implementation_guardrail,
            artifact_obligation_map,
            semantic_drift_ambiguity_register,
            implementation_spec_projection_packet,
        )
    ):
        (
            _source_index,
            semantic_intent_contract,
            intent_non_implementation_guardrail,
            _edge_decomposition,
            artifact_obligation_map,
            semantic_drift_ambiguity_register,
        ) = derive_v83b_semantic_edge_obligation_bundle(repo_root=repo_root)
        implementation_spec_projection_packet = (
            derive_v83c_repo_implementation_spec_projection_packet(
                repo_root=repo_root,
                semantic_intent_contract=semantic_intent_contract,
                intent_non_implementation_guardrail=intent_non_implementation_guardrail,
                intent_edge_decomposition=_edge_decomposition,
                artifact_obligation_map=artifact_obligation_map,
                semantic_drift_ambiguity_register=semantic_drift_ambiguity_register,
            )
        )
    assert semantic_intent_contract is not None
    assert intent_non_implementation_guardrail is not None
    assert artifact_obligation_map is not None
    assert semantic_drift_ambiguity_register is not None
    assert implementation_spec_projection_packet is not None
    packet_row = implementation_spec_projection_packet.projection_packet_rows[0]
    obligation_refs = sorted(
        {
            obligation.artifact_obligation_ref
            for row in artifact_obligation_map.obligation_map_rows
            for obligation in row.artifact_obligation_rows
        }
    )
    drift_refs = sorted(
        {
            drift.drift_ref
            for row in semantic_drift_ambiguity_register.drift_register_rows
            for drift in row.drift_or_ambiguity_rows
            if drift.blocking_posture in {"warning_only", "carried_for_later_review"}
        }
    )
    guardrail_refs = sorted(
        {row.guardrail_ref for row in intent_non_implementation_guardrail.guardrail_rows}
    )
    rows = [
        {
            "handoff_ref": "handoff:v83c:implementation-slice-review",
            "candidate_ref": packet_row.candidate_ref,
            "projection_packet_refs": [packet_row.projection_packet_ref],
            "intent_contract_refs": packet_row.intent_contract_refs,
            "artifact_obligation_refs": obligation_refs,
            "carried_drift_refs": drift_refs,
            "handoff_target": "future_implementation_slice_review",
            "handoff_subject_horizon": "implementation_spec_package",
            "handoff_posture": "ready_for_later_review",
            "required_later_authority_refs": ["intent:v83a:authority-boundary:later-lock-required"],
            "work_packet_authority_posture": "work_packet_requires_later_lock",
            "implementation_lock_requirement": "canonical_starter_lock_required",
            "work_packet_execution_posture": "no_execution_performed_by_v83",
            "implementation_execution_posture": "no_execution_performed_by_v83",
            "meta_orchestrator_runtime_posture": "not_applicable",
            "guardrail_refs": guardrail_refs,
            "limitation_note": (
                "Handoff requests later implementation slice review under canonical lock; "
                "no implementation and no execution."
            ),
        },
        {
            "handoff_ref": "handoff:v83c:morphic-ux-projection-review",
            "candidate_ref": packet_row.candidate_ref,
            "projection_packet_refs": [packet_row.projection_packet_ref],
            "intent_contract_refs": packet_row.intent_contract_refs,
            "artifact_obligation_refs": [],
            "carried_drift_refs": ["drift:v83b:morphic-ux-scope"],
            "handoff_target": "future_morphic_ux_projection_review",
            "handoff_subject_horizon": "ux_projection_spec",
            "handoff_posture": "ready_with_nonblocking_warnings",
            "required_later_authority_refs": [
                "intent:v83a:authority-boundary:morphic-runtime-not-selected"
            ],
            "work_packet_authority_posture": "work_packet_requires_later_lock",
            "implementation_lock_requirement": "canonical_starter_lock_required",
            "work_packet_execution_posture": "no_execution_performed_by_v83",
            "implementation_execution_posture": "no_execution_performed_by_v83",
            "meta_orchestrator_runtime_posture": "not_applicable",
            "guardrail_refs": guardrail_refs,
            "limitation_note": (
                "Morphic UX projection handoff is review-only with no runtime change "
                "and no implementation."
            ),
        },
        {
            "handoff_ref": "handoff:v83c:workflow-orchestrator-review",
            "candidate_ref": packet_row.candidate_ref,
            "projection_packet_refs": [packet_row.projection_packet_ref],
            "intent_contract_refs": packet_row.intent_contract_refs,
            "artifact_obligation_refs": [],
            "carried_drift_refs": ["drift:v83b:direct-oai-runtime-scope"],
            "handoff_target": "future_meta_orchestrator_workflow_review",
            "handoff_subject_horizon": "workflow_orchestrator_spec",
            "handoff_posture": "ready_with_nonblocking_warnings",
            "required_later_authority_refs": [
                "intent:v83a:authority-boundary:direct-oai-runtime-not-selected"
            ],
            "work_packet_authority_posture": "work_packet_requires_later_lock",
            "implementation_lock_requirement": "canonical_starter_lock_required",
            "work_packet_execution_posture": "no_execution_performed_by_v83",
            "implementation_execution_posture": "no_execution_performed_by_v83",
            "meta_orchestrator_runtime_posture": "workflow_transition_review_only",
            "guardrail_refs": guardrail_refs,
            "limitation_note": (
                "Workflow orchestrator handoff is transition review only; no workflow "
                "transition completed and no implementation."
            ),
        },
    ]
    payload = {
        "schema": REPO_INTENT_TO_WORK_PACKET_HANDOFF_SCHEMA,
        "intent_to_work_packet_handoff_id": "",
        "implementation_spec_projection_packet_id": (
            implementation_spec_projection_packet.implementation_spec_projection_packet_id
        ),
        "semantic_intent_contract_id": semantic_intent_contract.semantic_intent_contract_id,
        "artifact_obligation_map_id": artifact_obligation_map.artifact_obligation_map_id,
        "semantic_drift_ambiguity_register_id": (
            semantic_drift_ambiguity_register.semantic_drift_ambiguity_register_id
        ),
        "intent_non_implementation_guardrail_id": (
            intent_non_implementation_guardrail.intent_non_implementation_guardrail_id
        ),
        "review_id": implementation_spec_projection_packet.review_id,
        "snapshot_id": implementation_spec_projection_packet.snapshot_id,
        "source_set_id": implementation_spec_projection_packet.source_set_id,
        "handoff_rows": sorted(rows, key=lambda row: row["handoff_ref"]),
        "handoff_summary": (
            "V83-C intent-to-work-packet handoffs request later review and later lock "
            "with no implementation."
        ),
    }
    payload["intent_to_work_packet_handoff_id"] = _surface_id(
        "repo_intent_to_work_packet_handoff",
        REPO_INTENT_TO_WORK_PACKET_HANDOFF_SCHEMA,
        payload,
        "intent_to_work_packet_handoff_id",
    )
    return RepoIntentToWorkPacketHandoff.model_validate(payload)


def derive_v83c_repo_semantic_implementation_spec_family_closeout_alignment(
    *,
    repo_root: Path | None = None,
    implementation_spec_projection_packet: RepoImplementationSpecProjectionPacket | None = None,
    intent_to_work_packet_handoff: RepoIntentToWorkPacketHandoff | None = None,
) -> RepoSemanticImplementationSpecFamilyCloseoutAlignment:
    if implementation_spec_projection_packet is None or intent_to_work_packet_handoff is None:
        (
            _source_index,
            contract,
            guardrail,
            edge_decomposition,
            obligation_map,
            drift_register,
        ) = derive_v83b_semantic_edge_obligation_bundle(repo_root=repo_root)
        implementation_spec_projection_packet = (
            derive_v83c_repo_implementation_spec_projection_packet(
                repo_root=repo_root,
                semantic_intent_contract=contract,
                intent_non_implementation_guardrail=guardrail,
                intent_edge_decomposition=edge_decomposition,
                artifact_obligation_map=obligation_map,
                semantic_drift_ambiguity_register=drift_register,
            )
        )
        intent_to_work_packet_handoff = derive_v83c_repo_intent_to_work_packet_handoff(
            repo_root=repo_root,
            semantic_intent_contract=contract,
            intent_non_implementation_guardrail=guardrail,
            artifact_obligation_map=obligation_map,
            semantic_drift_ambiguity_register=drift_register,
            implementation_spec_projection_packet=implementation_spec_projection_packet,
        )
    payload = {
        "schema": REPO_SEMANTIC_IMPLEMENTATION_SPEC_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
        "semantic_implementation_spec_family_closeout_alignment_id": "",
        "implementation_spec_projection_packet_id": (
            implementation_spec_projection_packet.implementation_spec_projection_packet_id
        ),
        "intent_to_work_packet_handoff_id": (
            intent_to_work_packet_handoff.intent_to_work_packet_handoff_id
        ),
        "family": "V83",
        "closed_by_arc": "vNext+235",
        "closed_slice_ladder": ["V83-A", "V83-B", "V83-C"],
        "shipped_record_shapes": sorted(
            [
                REPO_INTENT_SOURCE_INDEX_SCHEMA,
                REPO_SEMANTIC_INTENT_CONTRACT_SCHEMA,
                REPO_INTENT_NON_IMPLEMENTATION_GUARDRAIL_SCHEMA,
                REPO_INTENT_EDGE_DECOMPOSITION_SCHEMA,
                REPO_ARTIFACT_OBLIGATION_MAP_SCHEMA,
                REPO_SEMANTIC_DRIFT_AMBIGUITY_REGISTER_SCHEMA,
                REPO_IMPLEMENTATION_SPEC_PROJECTION_PACKET_SCHEMA,
                REPO_INTENT_TO_WORK_PACKET_HANDOFF_SCHEMA,
                REPO_SEMANTIC_IMPLEMENTATION_SPEC_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            ]
        ),
        "consumed_source_families": [
            "V68",
            "V69",
            "V70",
            "V71",
            "V72",
            "V73",
            "V74",
            "V75",
            "V76",
            "V77",
            "V78",
            "V79",
            "V80",
            "V81",
            "V82",
            "V83",
        ],
        "family_closed_on_main": "closed_after_v83c_merge",
        "future_family_authority": "next_selector_required",
        "unselected_future_surfaces": [
            "code_implementation",
            "direct_oai_runtime_behavior",
            "graph_memory_authority",
            "meta_orchestrator_runtime",
            "morphic_ux_runtime_change",
            "product_authorization",
            "recursive_policy_amendment",
            "release",
            "v84_selection",
            "work_packet_execution",
        ],
        "semantic_implementation_spec_boundary": (
            "V83 closes semantic implementation-spec projection packet review with "
            "no implementation, no work-packet execution, and no v84 selection."
        ),
        "limitation_note": (
            "V83 is closed as semantic implementation-spec review only; no implementation, "
            "no execution, no product authority, no release, no graph-memory authority, "
            "and no v84 selection."
        ),
    }
    payload["semantic_implementation_spec_family_closeout_alignment_id"] = _surface_id(
        "repo_semantic_implementation_spec_family_closeout_alignment",
        REPO_SEMANTIC_IMPLEMENTATION_SPEC_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
        payload,
        "semantic_implementation_spec_family_closeout_alignment_id",
    )
    return RepoSemanticImplementationSpecFamilyCloseoutAlignment.model_validate(payload)


def validate_v83c_semantic_implementation_projection_bundle(
    *,
    intent_source_index: RepoIntentSourceIndex,
    semantic_intent_contract: RepoSemanticIntentContract,
    intent_non_implementation_guardrail: RepoIntentNonImplementationGuardrail,
    intent_edge_decomposition: RepoIntentEdgeDecomposition,
    artifact_obligation_map: RepoArtifactObligationMap,
    semantic_drift_ambiguity_register: RepoSemanticDriftAmbiguityRegister,
    implementation_spec_projection_packet: RepoImplementationSpecProjectionPacket,
    intent_to_work_packet_handoff: RepoIntentToWorkPacketHandoff,
    semantic_implementation_spec_family_closeout_alignment: (
        RepoSemanticImplementationSpecFamilyCloseoutAlignment
    ),
) -> None:
    validate_v83b_semantic_edge_obligation_bundle(
        intent_source_index=intent_source_index,
        semantic_intent_contract=semantic_intent_contract,
        intent_non_implementation_guardrail=intent_non_implementation_guardrail,
        intent_edge_decomposition=intent_edge_decomposition,
        artifact_obligation_map=artifact_obligation_map,
        semantic_drift_ambiguity_register=semantic_drift_ambiguity_register,
    )
    expected_ids = (
        semantic_intent_contract.semantic_intent_contract_id,
        intent_edge_decomposition.intent_edge_decomposition_id,
        artifact_obligation_map.artifact_obligation_map_id,
        semantic_drift_ambiguity_register.semantic_drift_ambiguity_register_id,
        intent_non_implementation_guardrail.intent_non_implementation_guardrail_id,
    )
    if (
        implementation_spec_projection_packet.semantic_intent_contract_id,
        implementation_spec_projection_packet.intent_edge_decomposition_id,
        implementation_spec_projection_packet.artifact_obligation_map_id,
        implementation_spec_projection_packet.semantic_drift_ambiguity_register_id,
        implementation_spec_projection_packet.intent_non_implementation_guardrail_id,
    ) != expected_ids:
        raise ValueError("V83-C projection packet must reference released V83-A/B surfaces")
    if (
        intent_to_work_packet_handoff.implementation_spec_projection_packet_id
        != implementation_spec_projection_packet.implementation_spec_projection_packet_id
    ):
        raise ValueError("V83-C handoff must reference released projection packet")
    if (
        intent_to_work_packet_handoff.semantic_intent_contract_id,
        intent_to_work_packet_handoff.artifact_obligation_map_id,
        intent_to_work_packet_handoff.semantic_drift_ambiguity_register_id,
        intent_to_work_packet_handoff.intent_non_implementation_guardrail_id,
    ) != (
        semantic_intent_contract.semantic_intent_contract_id,
        artifact_obligation_map.artifact_obligation_map_id,
        semantic_drift_ambiguity_register.semantic_drift_ambiguity_register_id,
        intent_non_implementation_guardrail.intent_non_implementation_guardrail_id,
    ):
        raise ValueError("V83-C handoff must reference released V83-A/B surfaces")
    if (
        semantic_implementation_spec_family_closeout_alignment.implementation_spec_projection_packet_id
        != implementation_spec_projection_packet.implementation_spec_projection_packet_id
        or semantic_implementation_spec_family_closeout_alignment.intent_to_work_packet_handoff_id
        != intent_to_work_packet_handoff.intent_to_work_packet_handoff_id
    ):
        raise ValueError("V83-C closeout must reference projection packet and handoff")

    known_sources = {row.source_ref for row in intent_source_index.source_rows}
    known_contracts = {
        row.intent_contract_ref: row for row in semantic_intent_contract.intent_contract_rows
    }
    known_guardrails = {
        row.guardrail_ref for row in intent_non_implementation_guardrail.guardrail_rows
    }
    known_decompositions = {
        row.edge_decomposition_ref: row for row in intent_edge_decomposition.edge_decomposition_rows
    }
    known_edges = {
        relation.semantic_relation_ref: relation
        for row in intent_edge_decomposition.edge_decomposition_rows
        for relation in row.semantic_relation_rows
    }
    known_validations = {
        validation.validation_need_ref
        for row in intent_edge_decomposition.edge_decomposition_rows
        for validation in row.validation_need_rows
    }
    known_obligation_maps = {
        row.obligation_map_ref: row for row in artifact_obligation_map.obligation_map_rows
    }
    known_obligations = {
        obligation.artifact_obligation_ref: obligation
        for row in artifact_obligation_map.obligation_map_rows
        for obligation in row.artifact_obligation_rows
    }
    known_evidence_requirements = {
        evidence.evidence_requirement_ref
        for obligation in known_obligations.values()
        for evidence in obligation.acceptance_evidence_requirements
    }
    known_drift_registers = {
        row.drift_register_ref: row for row in semantic_drift_ambiguity_register.drift_register_rows
    }
    known_drift = {
        drift.drift_ref: drift
        for row in semantic_drift_ambiguity_register.drift_register_rows
        for drift in row.drift_or_ambiguity_rows
    }

    known_projection_packets = {
        row.projection_packet_ref: row
        for row in implementation_spec_projection_packet.projection_packet_rows
    }
    known_projection_spec_refs: set[str] = set()
    for packet_row in implementation_spec_projection_packet.projection_packet_rows:
        if any(ref not in known_contracts for ref in packet_row.intent_contract_refs):
            raise ValueError("projection packet intent refs must be known")
        if any(ref not in known_decompositions for ref in packet_row.edge_decomposition_refs):
            raise ValueError("projection packet edge decomposition refs must be known")
        if any(ref not in known_obligation_maps for ref in packet_row.obligation_map_refs):
            raise ValueError("projection packet obligation map refs must be known")
        if any(ref not in known_drift_registers for ref in packet_row.drift_register_refs):
            raise ValueError("projection packet drift register refs must be known")
        if any(ref not in known_sources for ref in packet_row.source_refs):
            raise ValueError("projection packet source refs must be known")
        if any(ref not in known_guardrails for ref in packet_row.guardrail_refs):
            raise ValueError("projection packet guardrail refs must be known")
        blocking_drift_refs = [
            ref
            for ref in packet_row.carried_blocker_refs
            if ref in known_drift and known_drift[ref].blocking_posture == "blocking"
        ]
        if (
            packet_row.projection_posture == "projection_packet_ready_for_review"
            and blocking_drift_refs
        ):
            raise ValueError("ready projection packets cannot hide blocking drift")
        for spec_row in packet_row.implementation_spec_rows:
            known_projection_spec_refs.add(spec_row.implementation_spec_ref)
            if any(ref not in known_obligations for ref in spec_row.artifact_obligation_refs):
                raise ValueError("implementation specs must reference known artifact obligations")
            if any(ref not in known_validations for ref in spec_row.required_validation_refs):
                raise ValueError("implementation specs must reference known validation needs")
            if any(ref not in known_edges for ref in spec_row.semantic_preservation_refs):
                raise ValueError("implementation specs must reference known semantic edges")
            if any(
                ref not in known_evidence_requirements
                for ref in spec_row.acceptance_evidence_requirements
            ):
                raise ValueError("implementation specs must reference known acceptance evidence")
        for provenance_row in packet_row.projection_provenance_rows:
            if any(ref not in known_contracts for ref in provenance_row.input_intent_contract_refs):
                raise ValueError("projection provenance must reference known intent contracts")
            if any(
                ref not in known_decompositions
                for ref in provenance_row.input_edge_decomposition_refs
            ):
                raise ValueError("projection provenance must reference known edge decompositions")
            if any(
                ref not in known_obligation_maps
                for ref in provenance_row.input_obligation_map_refs
            ):
                raise ValueError("projection provenance must reference known obligation maps")
        check_kinds = {row.check_kind for row in packet_row.spec_review_checklist_rows}
        if packet_row.projection_posture == "projection_packet_ready_for_review":
            if {
                "edge_coverage_check",
                "validation_evidence_check",
                "reject_fixture_check",
                "source_binding_check",
            }.difference(check_kinds):
                raise ValueError("ready projection packets require edge-bound quality checks")
            if check_kinds == {"validation_evidence_check"}:
                raise ValueError(
                    "tests alone cannot pass semantic implementation-spec quality gate"
                )

    for handoff_row in intent_to_work_packet_handoff.handoff_rows:
        if any(ref not in known_projection_packets for ref in handoff_row.projection_packet_refs):
            raise ValueError("work-packet handoff projection refs must be known")
        if any(ref not in known_contracts for ref in handoff_row.intent_contract_refs):
            raise ValueError("work-packet handoff intent refs must be known")
        if any(ref not in known_obligations for ref in handoff_row.artifact_obligation_refs):
            raise ValueError("work-packet handoff obligation refs must be known")
        if any(ref not in known_drift for ref in handoff_row.carried_drift_refs):
            raise ValueError("work-packet handoff carried drift refs must be known")
        if any(ref not in known_guardrails for ref in handoff_row.guardrail_refs):
            raise ValueError("work-packet handoff guardrail refs must be known")
        if handoff_row.handoff_posture == "ready_for_later_review":
            if handoff_row.implementation_lock_requirement != "canonical_starter_lock_required":
                raise ValueError("ready handoffs require canonical later lock")


def derive_v83c_semantic_implementation_projection_bundle(
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
]:
    (
        source_index,
        contract,
        guardrail,
        edge_decomposition,
        obligation_map,
        drift_register,
    ) = derive_v83b_semantic_edge_obligation_bundle(repo_root=repo_root)
    projection_packet = derive_v83c_repo_implementation_spec_projection_packet(
        repo_root=repo_root,
        semantic_intent_contract=contract,
        intent_non_implementation_guardrail=guardrail,
        intent_edge_decomposition=edge_decomposition,
        artifact_obligation_map=obligation_map,
        semantic_drift_ambiguity_register=drift_register,
    )
    handoff = derive_v83c_repo_intent_to_work_packet_handoff(
        repo_root=repo_root,
        semantic_intent_contract=contract,
        intent_non_implementation_guardrail=guardrail,
        artifact_obligation_map=obligation_map,
        semantic_drift_ambiguity_register=drift_register,
        implementation_spec_projection_packet=projection_packet,
    )
    closeout = derive_v83c_repo_semantic_implementation_spec_family_closeout_alignment(
        repo_root=repo_root,
        implementation_spec_projection_packet=projection_packet,
        intent_to_work_packet_handoff=handoff,
    )
    validate_v83c_semantic_implementation_projection_bundle(
        intent_source_index=source_index,
        semantic_intent_contract=contract,
        intent_non_implementation_guardrail=guardrail,
        intent_edge_decomposition=edge_decomposition,
        artifact_obligation_map=obligation_map,
        semantic_drift_ambiguity_register=drift_register,
        implementation_spec_projection_packet=projection_packet,
        intent_to_work_packet_handoff=handoff,
        semantic_implementation_spec_family_closeout_alignment=closeout,
    )
    return (
        source_index,
        contract,
        guardrail,
        edge_decomposition,
        obligation_map,
        drift_register,
        projection_packet,
        handoff,
        closeout,
    )
