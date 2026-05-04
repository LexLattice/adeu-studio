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

REPO_WORK_PACKET_ACTIVATION_SOURCE_INDEX_SCHEMA = "repo_work_packet_activation_source_index@1"
REPO_WORK_PACKET_ACTIVATION_REVIEW_REQUEST_SCHEMA = "repo_work_packet_activation_review_request@1"
REPO_WORK_PACKET_ACTIVATION_NON_EXECUTION_GUARDRAIL_SCHEMA = (
    "repo_work_packet_activation_non_execution_guardrail@1"
)
REPO_WORK_PACKET_SCOPE_CONTRACT_SCHEMA = "repo_work_packet_scope_contract@1"
REPO_IMPLEMENTATION_TARGET_SURFACE_BOUNDARY_SCHEMA = "repo_implementation_target_surface_boundary@1"
REPO_WORK_PACKET_VALIDATION_EVIDENCE_PLAN_SCHEMA = "repo_work_packet_validation_evidence_plan@1"
REPO_WORK_PACKET_ACTIVATION_EXCEPTION_REGISTER_SCHEMA = (
    "repo_work_packet_activation_exception_register@1"
)
REPO_WORK_PACKET_ACTIVATION_READINESS_SUMMARY_SCHEMA = (
    "repo_work_packet_activation_readiness_summary@1"
)
REPO_POST_WORK_PACKET_ACTIVATION_REVIEW_HANDOFF_SCHEMA = (
    "repo_post_work_packet_activation_review_handoff@1"
)
REPO_WORK_PACKET_ACTIVATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA = (
    "repo_work_packet_activation_family_closeout_alignment@1"
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
WorkPacketKind = Literal[
    "schema_model_fixture_test_slice",
    "docs_support_slice",
    "morphic_ux_projection_slice",
    "direct_oai_harness_slice",
    "meta_orchestrator_workflow_slice",
    "product_future_family_slice",
    "graph_memory_future_family_slice",
    "future_family_only",
]
ScopeCompletenessPosture = Literal[
    "complete_for_activation_review_only",
    "incomplete_for_review",
    "blocked_by_missing_projection_packet",
    "blocked_by_unbounded_target_surface",
    "blocked_by_missing_validation_plan",
    "blocked_by_authority_gap",
    "future_family_only",
    "rejected_out_of_scope",
]
ActivationReviewPosture = Literal[
    "package_ready_for_review_only",
    "package_incomplete_for_review",
    "blocked_by_package_lineage_gap",
    "blocked_by_target_boundary_gap",
    "blocked_by_validation_gap",
    "blocked_by_exception",
    "future_family_only",
]
TargetSurfaceKind = Literal[
    "repo_description_module",
    "schema_file",
    "spec_schema_file",
    "fixture_file",
    "test_file",
    "support_doc",
    "external_support_context",
    "future_family_surface",
]
TargetResolutionKind = Literal[
    "concrete_file_ref",
    "concrete_schema_ref",
    "concrete_fixture_ref",
    "concrete_test_ref",
    "concrete_doc_ref",
    "bounded_directory_with_child_refs",
    "support_artifact_ref",
    "external_support_ref",
    "no_target_boundary",
]
TargetCurrentnessPosture = Literal[
    "current_repo_surface",
    "generated_future_surface",
    "support_context_only",
    "explicitly_absent",
    "unknown_needs_review",
]
TargetMutabilityReviewPosture = Literal[
    "mutation_requires_later_lock",
    "read_only_dependency",
    "validation_target_only",
    "generated_artifact_requires_later_lock",
    "mutation_forbidden",
    "context_only_not_mutable",
]
TargetAccessRole = Literal[
    "read_dependency",
    "prospective_write_target_for_later_lock",
    "validation_target",
    "generated_artifact_target",
    "forbidden_target",
    "context_only",
]
InScopeCountingPosture = Literal[
    "counts_as_bounded_later_scope",
    "context_only_not_counted",
    "forbidden_not_counted",
    "validation_only_not_write_scope",
]
AllowedTargetReviewAction = Literal[
    "describe_target_boundary",
    "inspect_source_metadata",
    "record_target_absence",
    "request_later_lock_review",
    "preserve_target_gap",
]
ForbiddenTargetMutationAction = Literal[
    "edit_file",
    "create_file",
    "delete_file",
    "mutate_schema",
    "mutate_fixture",
    "run_formatter_for_effect",
    "open_pr",
    "commit_change",
]
BoundaryPosture = Literal[
    "bounded_for_review_only",
    "blocked_by_missing_child_refs",
    "blocked_by_glob_target",
    "blocked_by_forbidden_target",
    "future_family_only",
]
ValidationEvidenceKind = Literal[
    "schema_export_check",
    "model_shape_check",
    "validator_acceptance_check",
    "validator_reject_check",
    "fixture_positive_case",
    "fixture_negative_case",
    "unit_test_requirement",
    "integration_test_requirement",
    "doc_alignment_review",
    "semantic_edge_review",
    "manual_reviewer_check",
    "tool_run_review_only",
    "future_family_review",
]
EvidencePresencePosture = Literal[
    "requirement_recorded_for_review_only",
    "missing_required_evidence",
    "evidence_requires_later_execution",
    "not_applicable",
]
ValidationRequirementPosture = Literal[
    "required_for_later_review",
    "missing_required_evidence",
    "not_applicable",
]
ToolApplicabilityPosture = Literal[
    "tool_applicable_for_later_review",
    "tool_run_requires_later_lock",
    "tool_not_applicable",
]
ValidationPlanPosture = Literal[
    "plan_complete_for_review_only",
    "plan_incomplete_for_review",
    "blocked_by_missing_semantic_edges",
    "blocked_by_missing_artifact_obligations",
    "blocked_by_missing_positive_evidence",
    "blocked_by_missing_reject_evidence",
    "blocked_by_tests_as_truth_gap",
    "future_family_only",
]
ManualReviewPosture = Literal[
    "manual_review_required_later",
    "manual_review_not_applicable",
    "manual_review_missing",
]
ToolRunPosture = Literal[
    "no_tool_run_performed_by_v84",
    "tool_run_requires_later_lock",
    "tool_run_not_applicable",
]
ActivationExceptionKind = Literal[
    "missing_released_projection_packet",
    "missing_quality_gate",
    "carried_semantic_drift_blocker",
    "generated_spec_provenance_gap",
    "unbounded_target_surface",
    "target_glob_without_child_refs",
    "missing_validation_plan",
    "missing_positive_evidence_requirement",
    "missing_reject_evidence_requirement",
    "operator_confirmation_as_authority",
    "implementation_authority_gap",
    "runtime_authority_gap",
    "product_authority_gap",
    "release_authority_gap",
    "graph_memory_authority_gap",
    "activation_package_lineage_mismatch",
    "scope_target_validation_candidate_mismatch",
    "canonical_lock_requirement_missing_or_untyped",
    "read_set_write_set_collision",
    "forbidden_target_included_in_scope",
    "generated_candidate_without_review_provenance",
    "quality_gate_ready_but_blockers_carried",
    "validation_plan_not_edge_complete",
    "validation_plan_not_obligation_complete",
    "later_family_boundary_unclear",
    "unknown_needs_review",
]
BlockingPosture = Literal[
    "blocking",
    "warning",
    "not_applicable",
    "future_family_only",
]
VisibilityPosture = Literal[
    "visible_to_later_lock_review",
    "visible_warning",
    "hidden_rejected",
]
RequiredResolutionHorizon = Literal[
    "later_canonical_lock_review",
    "later_target_boundary_review",
    "later_validation_plan_review",
    "later_authority_review",
    "future_family_review",
    "not_applicable",
]
ActivationReadinessSummaryPosture = Literal[
    "ready_for_later_implementation_lock_review",
    "ready_with_nonblocking_warnings",
    "blocked_by_missing_projection_packet",
    "blocked_by_missing_scope_contract",
    "blocked_by_unbounded_target_surface",
    "blocked_by_missing_validation_plan",
    "blocked_by_carried_semantic_drift",
    "blocked_by_authority_gap",
    "future_family_only",
    "rejected_out_of_scope",
]
ActivationReadyBasisPosture = Literal[
    "ready_no_blockers",
    "ready_with_nonblocking_warnings",
    "not_ready_blockers_remain",
    "authority_review_requested_for_blockers",
    "blocker_settlement_review_requested",
    "future_family_only",
    "rejected_out_of_scope",
]
ActivationCoveragePosture = Literal[
    "edge_and_obligation_complete_for_review",
    "missing_semantic_edge_coverage",
    "missing_artifact_obligation_coverage",
    "missing_target_boundary_coverage",
    "missing_reject_evidence_coverage",
    "future_family_only",
]
ActivationHandoffTarget = Literal[
    "future_canonical_implementation_lock_review",
    "future_implementation_slice_review",
    "future_morphic_ux_implementation_review",
    "future_direct_oai_harness_implementation_review",
    "future_meta_orchestrator_workflow_activation_review",
    "future_product_review",
    "future_graph_memory_review",
    "future_family_review",
    "deferred_no_selection",
]
ActivationHandoffSubjectHorizon = Literal[
    "implementation_lock_review_package",
    "implementation_slice_review_package",
    "morphic_ux_runtime_review_pressure",
    "direct_oai_runtime_review_pressure",
    "meta_orchestrator_workflow_review_pressure",
    "product_review_pressure",
    "graph_memory_review_pressure",
    "future_family_pressure",
]
ActivationHandoffPosture = Literal[
    "ready_for_later_review",
    "ready_with_nonblocking_warnings",
    "blocked_by_carried_exceptions",
    "future_family_only",
    "deferred_no_selection",
]
ActivationHandoffAuthorityHorizon = Literal[
    "canonical_implementation_lock_review",
    "implementation_slice_review",
    "work_packet_execution_authority_review",
    "target_mutation_authority_review",
    "test_execution_review",
    "tool_invocation_review",
    "morphic_ux_runtime_authority_review",
    "direct_oai_runtime_authority_review",
    "meta_orchestrator_runtime_authority_review",
    "product_authority_review",
    "graph_memory_authority_review",
    "future_family_review",
]
ActivationHandoffStatus = Literal[
    "no_work_packet_activated_by_v84",
    "later_lock_review_requested",
    "blocker_settlement_requested",
    "future_family_only",
]
PrCommitReleasePosture = Literal[
    "no_pr_commit_merge_release_performed_by_v84",
    "pr_commit_merge_release_requires_later_lock",
    "pr_commit_merge_release_forbidden_by_this_family",
]
WorkPacketActivationClosedSlice = Literal["V84-A", "V84-B", "V84-C"]
WorkPacketActivationConsumedFamily = Literal[
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
    "V84",
]
WorkPacketActivationShippedRecordShape = Literal[
    "repo_work_packet_activation_review_request@1",
    "repo_work_packet_activation_source_index@1",
    "repo_work_packet_activation_non_execution_guardrail@1",
    "repo_work_packet_scope_contract@1",
    "repo_implementation_target_surface_boundary@1",
    "repo_work_packet_validation_evidence_plan@1",
    "repo_work_packet_activation_exception_register@1",
    "repo_work_packet_activation_readiness_summary@1",
    "repo_post_work_packet_activation_review_handoff@1",
    "repo_work_packet_activation_family_closeout_alignment@1",
]
WorkPacketActivationUnselectedFutureSurface = Literal[
    "command_execution",
    "direct_oai_runtime_behavior",
    "graph_memory_authority",
    "implementation_execution",
    "implementation_lock_creation",
    "meta_orchestrator_runtime_transition",
    "morphic_ux_runtime_change",
    "pr_commit_merge_release",
    "product_authorization",
    "recursive_policy_amendment",
    "target_mutation",
    "tool_invocation",
    "v85_selection",
    "work_packet_activation",
    "work_packet_execution",
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
_V84_MAPPING_DOC = "docs/DRAFT_ADEU_WORK_PACKET_ACTIVATION_REVIEW_V84_IMPLEMENTATION_MAPPING_v0.md"
_V84A_MAPPING_DOC = (
    "docs/DRAFT_ADEU_WORK_PACKET_ACTIVATION_REVIEW_V84A_IMPLEMENTATION_MAPPING_v0.md"
)
_V83_COMBINED_DOGFOOD_JSON = (
    "docs/support/arc_series_mapping/"
    "V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_V82_V83_"
    "COMBINED_DOGFOOD_TEST_v0.json"
)
_V84A_REQUEST_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus236/"
    "repo_work_packet_activation_review_request_v236_reference.json"
)
_V84A_SOURCE_INDEX_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus236/"
    "repo_work_packet_activation_source_index_v236_reference.json"
)
_V84A_GUARDRAIL_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus236/"
    "repo_work_packet_activation_non_execution_guardrail_v236_reference.json"
)
_V84B_SCOPE_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus237/"
    "repo_work_packet_scope_contract_v237_reference.json"
)
_V84B_TARGET_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus237/"
    "repo_implementation_target_surface_boundary_v237_reference.json"
)
_V84B_VALIDATION_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus237/"
    "repo_work_packet_validation_evidence_plan_v237_reference.json"
)
_V84B_EXCEPTION_FIXTURE = (
    "apps/api/fixtures/repo_description/vnext_plus237/"
    "repo_work_packet_activation_exception_register_v237_reference.json"
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
                raise ValueError("generated candidates require prompt and model/agent profile refs")
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
                "Released V83 family closeout source for activation review only; no implementation."
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
                "V84-A assessment records later lock requirements for review; no implementation."
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
                "V84-A lock defines review scope and later lock requirements; no implementation."
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
                "Morphic UX support remains runtime-UI context for review only; no implementation."
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
                "model_or_agent_profile_refs": ["docs/LOCKED_CONTINUATION_vNEXT_PLUS236.md"],
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
                    "work_packet_execution_posture": ("no_work_packet_execution_performed_by_v84"),
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
    work_packet_activation_non_execution_guardrail: (RepoWorkPacketActivationNonExecutionGuardrail),
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
        raise ValueError("V84-A guardrails must reference released V84-A request and source index")

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


class RepoCanonicalLockRequirementRow(_CartographyBase):
    canonical_lock_requirement_ref: str
    activation_package_ref: str
    required_lock_kind: WorkPacketKind
    required_lock_inputs: list[str] = Field(min_length=1)
    required_lock_guardrails: list[str] = Field(min_length=1)
    required_stop_gate_refs: list[str] = Field(min_length=1)
    required_assessment_refs: list[str] = Field(min_length=1)
    required_closeout_refs: list[str] = Field(min_length=1)
    required_later_authority_refs: list[str] = Field(default_factory=list)
    lock_not_created_by_v84: bool
    limitation_note: str

    @model_validator(mode="after")
    def _validate_canonical_lock_requirement(self) -> "RepoCanonicalLockRequirementRow":
        for attr in ("canonical_lock_requirement_ref", "activation_package_ref"):
            _non_empty(getattr(self, attr), field_name=attr)
        for attr in (
            "required_lock_inputs",
            "required_lock_guardrails",
            "required_stop_gate_refs",
            "required_assessment_refs",
            "required_closeout_refs",
            "required_later_authority_refs",
        ):
            _validate_sorted_refs(getattr(self, attr), field_name=attr)
        if not self.lock_not_created_by_v84:
            raise ValueError("canonical lock requirements must not create locks in V84-B")
        _reject_v84_action_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("requirement", "later lock", "no implementation"),
            ),
            field_name="limitation_note",
        )
        return self


class RepoActivationPackageLineageRow(_CartographyBase):
    activation_package_lineage_ref: str
    activation_package_ref: str
    candidate_ref: str
    projection_packet_refs: list[str] = Field(min_length=1)
    quality_gate_refs: list[str] = Field(min_length=1)
    implementation_spec_refs: list[str] = Field(min_length=1)
    scope_contract_refs: list[str] = Field(default_factory=list)
    target_boundary_refs: list[str] = Field(default_factory=list)
    validation_plan_refs: list[str] = Field(default_factory=list)
    lineage_posture: Literal[
        "lineage_bound_for_review_only",
        "lineage_incomplete",
        "lineage_mismatch_blocked",
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_activation_package_lineage(self) -> "RepoActivationPackageLineageRow":
        for attr in (
            "activation_package_lineage_ref",
            "activation_package_ref",
            "candidate_ref",
        ):
            _non_empty(getattr(self, attr), field_name=attr)
        for attr in (
            "projection_packet_refs",
            "quality_gate_refs",
            "implementation_spec_refs",
            "scope_contract_refs",
            "target_boundary_refs",
            "validation_plan_refs",
        ):
            _validate_sorted_refs(getattr(self, attr), field_name=attr)
        if self.lineage_posture == "lineage_bound_for_review_only":
            if (
                not self.projection_packet_refs
                or not self.quality_gate_refs
                or not self.implementation_spec_refs
            ):
                raise ValueError("bound activation package lineage requires released V83-C refs")
        _reject_v84_action_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("lineage", "review", "no implementation"),
            ),
            field_name="limitation_note",
        )
        return self


class RepoWorkPacketScopeContractRow(_CartographyBase):
    scope_contract_ref: str
    activation_package_ref: str
    activation_request_refs: list[str] = Field(min_length=1)
    projection_packet_refs: list[str] = Field(min_length=1)
    implementation_spec_refs: list[str] = Field(min_length=1)
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    work_packet_kind: WorkPacketKind
    scope_statement: str
    in_scope_artifact_refs: list[str] = Field(min_length=1)
    out_of_scope_artifact_refs: list[str] = Field(default_factory=list)
    target_boundary_refs: list[str] = Field(min_length=1)
    validation_plan_refs: list[str] = Field(min_length=1)
    canonical_lock_requirement_refs: list[str] = Field(min_length=1)
    activation_package_lineage_refs: list[str] = Field(min_length=1)
    canonical_lock_requirement_rows: list[RepoCanonicalLockRequirementRow] = Field(min_length=1)
    activation_package_lineage_rows: list[RepoActivationPackageLineageRow] = Field(min_length=1)
    scope_completeness_posture: ScopeCompletenessPosture
    activation_review_posture: ActivationReviewPosture
    work_packet_execution_posture: WorkPacketExecutionPosture
    implementation_execution_posture: ImplementationExecutionPosture
    guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_scope_contract_row(self) -> "RepoWorkPacketScopeContractRow":
        for attr in ("scope_contract_ref", "activation_package_ref", "candidate_ref"):
            _non_empty(getattr(self, attr), field_name=attr)
        for attr in (
            "activation_request_refs",
            "projection_packet_refs",
            "implementation_spec_refs",
            "source_refs",
            "in_scope_artifact_refs",
            "out_of_scope_artifact_refs",
            "target_boundary_refs",
            "validation_plan_refs",
            "canonical_lock_requirement_refs",
            "activation_package_lineage_refs",
            "guardrail_refs",
        ):
            _validate_sorted_refs(getattr(self, attr), field_name=attr)
        _sorted_unique_by_ref(
            self.canonical_lock_requirement_rows,
            attr="canonical_lock_requirement_ref",
            field_name="canonical_lock_requirement_rows",
        )
        _sorted_unique_by_ref(
            self.activation_package_lineage_rows,
            attr="activation_package_lineage_ref",
            field_name="activation_package_lineage_rows",
        )
        _reject_v84_action_claim(
            _require_terms(
                self.scope_statement,
                field_name="scope_statement",
                terms=("review", "later lock"),
            ),
            field_name="scope_statement",
        )
        _reject_v84_action_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("scope", "no implementation", "later lock"),
            ),
            field_name="limitation_note",
        )
        if self.work_packet_execution_posture != "no_work_packet_execution_performed_by_v84":
            raise ValueError("V84-B scope contracts cannot execute work packets")
        if self.implementation_execution_posture != "no_implementation_performed_by_v84":
            raise ValueError("V84-B scope contracts cannot perform implementation")
        if self.scope_completeness_posture == "complete_for_activation_review_only":
            if self.activation_review_posture != "package_ready_for_review_only":
                raise ValueError("complete scope contracts must remain review-only ready")
            if not self.target_boundary_refs or not self.validation_plan_refs:
                raise ValueError("complete scope contracts require target and validation refs")
            if not self.canonical_lock_requirement_refs:
                raise ValueError("complete scope contracts require canonical lock refs")
        canonical_refs = {
            row.canonical_lock_requirement_ref for row in self.canonical_lock_requirement_rows
        }
        if not set(self.canonical_lock_requirement_refs).issubset(canonical_refs):
            raise ValueError("canonical lock requirement refs must resolve to embedded rows")
        lineage_refs = {
            row.activation_package_lineage_ref for row in self.activation_package_lineage_rows
        }
        if not set(self.activation_package_lineage_refs).issubset(lineage_refs):
            raise ValueError("activation package lineage refs must resolve to embedded rows")
        for row in self.canonical_lock_requirement_rows:
            if row.activation_package_ref != self.activation_package_ref:
                raise ValueError("canonical lock requirement rows must match package")
        for row in self.activation_package_lineage_rows:
            if (
                row.activation_package_ref != self.activation_package_ref
                or row.candidate_ref != self.candidate_ref
            ):
                raise ValueError("activation package lineage rows must match package")
        return self


class RepoWorkPacketScopeContract(_CartographyBase):
    schema: Literal[REPO_WORK_PACKET_SCOPE_CONTRACT_SCHEMA]
    work_packet_scope_contract_id: str
    work_packet_activation_review_request_id: str
    work_packet_activation_source_index_id: str
    work_packet_activation_non_execution_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    scope_contract_rows: list[RepoWorkPacketScopeContractRow] = Field(min_length=1)
    scope_contract_summary: str

    @model_validator(mode="after")
    def _validate_scope_contract(self) -> "RepoWorkPacketScopeContract":
        for attr in (
            "work_packet_scope_contract_id",
            "work_packet_activation_review_request_id",
            "work_packet_activation_source_index_id",
            "work_packet_activation_non_execution_guardrail_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
        ):
            _non_empty(getattr(self, attr), field_name=attr)
        _sorted_unique_by_ref(
            self.scope_contract_rows,
            attr="scope_contract_ref",
            field_name="scope_contract_rows",
        )
        _reject_v84_action_claim(
            _require_terms(
                self.scope_contract_summary,
                field_name="scope_contract_summary",
                terms=("scope", "review", "no implementation"),
            ),
            field_name="scope_contract_summary",
        )
        _assert_surface_id(
            surface_name="repo_work_packet_scope_contract",
            schema=REPO_WORK_PACKET_SCOPE_CONTRACT_SCHEMA,
            payload=self.model_dump(mode="json"),
            id_key="work_packet_scope_contract_id",
            actual=self.work_packet_scope_contract_id,
        )
        return self


class RepoTargetAccessRoleRow(_CartographyBase):
    target_access_role_ref: str
    target_surface_refs: list[str] = Field(min_length=1)
    target_access_role: TargetAccessRole
    source_refs: list[str] = Field(min_length=1)
    target_mutability_review_posture: TargetMutabilityReviewPosture
    in_scope_counting_posture: InScopeCountingPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_target_access_role(self) -> "RepoTargetAccessRoleRow":
        _non_empty(self.target_access_role_ref, field_name="target_access_role_ref")
        _validate_sorted_refs(self.target_surface_refs, field_name="target_surface_refs")
        _validate_sorted_refs(self.source_refs, field_name="source_refs")
        if self.target_access_role == "prospective_write_target_for_later_lock":
            if self.target_mutability_review_posture != "mutation_requires_later_lock":
                raise ValueError("prospective write targets require later lock mutation posture")
            if self.in_scope_counting_posture != "counts_as_bounded_later_scope":
                raise ValueError("prospective write targets must count as bounded later scope")
        if self.target_access_role == "forbidden_target":
            if self.in_scope_counting_posture != "forbidden_not_counted":
                raise ValueError("forbidden targets cannot count as bounded scope")
            if self.target_mutability_review_posture != "mutation_forbidden":
                raise ValueError("forbidden targets require mutation-forbidden posture")
        if self.target_access_role == "context_only":
            if self.in_scope_counting_posture != "context_only_not_counted":
                raise ValueError("context-only targets cannot count as bounded scope")
        _reject_v84_action_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("target", "review", "later lock"),
            ),
            field_name="limitation_note",
        )
        return self


class RepoImplementationTargetSurfaceBoundaryRow(_CartographyBase):
    target_boundary_ref: str
    activation_package_ref: str
    scope_contract_refs: list[str] = Field(min_length=1)
    activation_request_refs: list[str] = Field(min_length=1)
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    target_surface_kind: TargetSurfaceKind
    target_surface_refs: list[str] = Field(min_length=1)
    target_resolution_kind: TargetResolutionKind
    target_currentness_posture: TargetCurrentnessPosture
    target_mutability_review_posture: TargetMutabilityReviewPosture
    target_access_role_rows: list[RepoTargetAccessRoleRow] = Field(min_length=1)
    allowed_target_review_actions: list[AllowedTargetReviewAction] = Field(min_length=1)
    forbidden_target_mutation_actions: list[ForbiddenTargetMutationAction] = Field(min_length=1)
    ownership_or_authority_refs: list[str] = Field(default_factory=list)
    boundary_posture: BoundaryPosture
    guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_target_boundary_row(self) -> "RepoImplementationTargetSurfaceBoundaryRow":
        for attr in ("target_boundary_ref", "activation_package_ref", "candidate_ref"):
            _non_empty(getattr(self, attr), field_name=attr)
        for attr in (
            "scope_contract_refs",
            "activation_request_refs",
            "source_refs",
            "target_surface_refs",
            "allowed_target_review_actions",
            "forbidden_target_mutation_actions",
            "ownership_or_authority_refs",
            "guardrail_refs",
        ):
            _validate_sorted_refs(getattr(self, attr), field_name=attr)
        _sorted_unique_by_ref(
            self.target_access_role_rows,
            attr="target_access_role_ref",
            field_name="target_access_role_rows",
        )
        if any("*" in ref for ref in self.target_surface_refs):
            raise ValueError("target globs cannot become implementation target boundaries")
        if self.target_resolution_kind == "bounded_directory_with_child_refs":
            if len(self.target_surface_refs) < 2:
                raise ValueError("bounded directories require concrete child refs")
            if (
                self.boundary_posture == "bounded_for_review_only"
                and len(self.target_surface_refs) < 2
            ):
                raise ValueError("bounded directory cannot be bounded without child refs")
        if self.target_resolution_kind == "no_target_boundary":
            if self.boundary_posture == "bounded_for_review_only":
                raise ValueError("missing target boundary cannot be bounded")
        if self.boundary_posture == "bounded_for_review_only":
            if not any(
                row.target_access_role
                in {
                    "generated_artifact_target",
                    "prospective_write_target_for_later_lock",
                }
                for row in self.target_access_role_rows
            ):
                raise ValueError("bounded target boundaries require bounded target role")
        if self.target_mutability_review_posture not in {
            "mutation_requires_later_lock",
            "generated_artifact_requires_later_lock",
            "validation_target_only",
        } and any(
            row.target_access_role == "prospective_write_target_for_later_lock"
            for row in self.target_access_role_rows
        ):
            raise ValueError("prospective write boundaries require later lock mutation posture")
        required_forbidden = {
            "edit_file",
            "create_file",
            "delete_file",
            "open_pr",
            "commit_change",
        }
        if not required_forbidden.issubset(self.forbidden_target_mutation_actions):
            raise ValueError("target boundaries must forbid mutation actions in V84-B")
        _reject_v84_action_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("target", "review", "no implementation"),
            ),
            field_name="limitation_note",
        )
        return self


class RepoImplementationTargetSurfaceBoundary(_CartographyBase):
    schema: Literal[REPO_IMPLEMENTATION_TARGET_SURFACE_BOUNDARY_SCHEMA]
    implementation_target_surface_boundary_id: str
    work_packet_scope_contract_id: str
    work_packet_activation_review_request_id: str
    work_packet_activation_source_index_id: str
    work_packet_activation_non_execution_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    target_boundary_rows: list[RepoImplementationTargetSurfaceBoundaryRow] = Field(min_length=1)
    target_boundary_summary: str

    @model_validator(mode="after")
    def _validate_target_boundary(self) -> "RepoImplementationTargetSurfaceBoundary":
        for attr in (
            "implementation_target_surface_boundary_id",
            "work_packet_scope_contract_id",
            "work_packet_activation_review_request_id",
            "work_packet_activation_source_index_id",
            "work_packet_activation_non_execution_guardrail_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
        ):
            _non_empty(getattr(self, attr), field_name=attr)
        _sorted_unique_by_ref(
            self.target_boundary_rows,
            attr="target_boundary_ref",
            field_name="target_boundary_rows",
        )
        _reject_v84_action_claim(
            _require_terms(
                self.target_boundary_summary,
                field_name="target_boundary_summary",
                terms=("target", "review", "no implementation"),
            ),
            field_name="target_boundary_summary",
        )
        _assert_surface_id(
            surface_name="repo_implementation_target_surface_boundary",
            schema=REPO_IMPLEMENTATION_TARGET_SURFACE_BOUNDARY_SCHEMA,
            payload=self.model_dump(mode="json"),
            id_key="implementation_target_surface_boundary_id",
            actual=self.implementation_target_surface_boundary_id,
        )
        return self


class RepoValidationEvidenceRow(_CartographyBase):
    validation_evidence_ref: str
    semantic_edge_refs: list[str] = Field(min_length=1)
    artifact_obligation_refs: list[str] = Field(min_length=1)
    implementation_spec_refs: list[str] = Field(min_length=1)
    evidence_kind: ValidationEvidenceKind
    required_artifact_refs: list[str] = Field(min_length=1)
    required_execution_horizon: Literal[
        "later_lock_execution_required",
        "manual_review_only",
        "no_execution_required",
        "future_family_only",
    ]
    evidence_presence_posture: EvidencePresencePosture
    acceptance_not_truth_guardrail: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_validation_evidence_row(self) -> "RepoValidationEvidenceRow":
        _non_empty(self.validation_evidence_ref, field_name="validation_evidence_ref")
        for attr in (
            "semantic_edge_refs",
            "artifact_obligation_refs",
            "implementation_spec_refs",
            "required_artifact_refs",
        ):
            _validate_sorted_refs(getattr(self, attr), field_name=attr)
        _require_terms(
            self.acceptance_not_truth_guardrail,
            field_name="acceptance_not_truth_guardrail",
            terms=("not truth",),
        )
        _reject_v84_action_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("evidence", "review", "no implementation"),
            ),
            field_name="limitation_note",
        )
        if self.evidence_presence_posture == "requirement_recorded_for_review_only":
            if self.required_execution_horizon == "no_execution_required":
                return self
        return self


class RepoValidationMatrixRow(_CartographyBase):
    validation_matrix_ref: str
    semantic_edge_refs: list[str] = Field(min_length=1)
    artifact_obligation_refs: list[str] = Field(min_length=1)
    implementation_spec_refs: list[str] = Field(min_length=1)
    target_boundary_refs: list[str] = Field(min_length=1)
    evidence_kind: ValidationEvidenceKind
    positive_evidence_requirement: ValidationRequirementPosture
    reject_evidence_requirement: ValidationRequirementPosture
    regression_evidence_requirement: ValidationRequirementPosture
    manual_review_requirement: ManualReviewPosture
    tool_applicability_posture: ToolApplicabilityPosture
    execution_required_later: bool
    acceptance_not_truth_guardrail: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_validation_matrix_row(self) -> "RepoValidationMatrixRow":
        _non_empty(self.validation_matrix_ref, field_name="validation_matrix_ref")
        for attr in (
            "semantic_edge_refs",
            "artifact_obligation_refs",
            "implementation_spec_refs",
            "target_boundary_refs",
        ):
            _validate_sorted_refs(getattr(self, attr), field_name=attr)
        _require_terms(
            self.acceptance_not_truth_guardrail,
            field_name="acceptance_not_truth_guardrail",
            terms=("not truth",),
        )
        if self.positive_evidence_requirement == "missing_required_evidence":
            raise ValueError("validation matrix rows require positive evidence posture")
        if self.reject_evidence_requirement == "missing_required_evidence":
            raise ValueError("validation matrix rows require reject evidence posture")
        _reject_v84_action_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("matrix", "review", "no implementation"),
            ),
            field_name="limitation_note",
        )
        return self


class RepoWorkPacketValidationEvidencePlanRow(_CartographyBase):
    validation_plan_ref: str
    activation_package_ref: str
    scope_contract_refs: list[str] = Field(min_length=1)
    activation_request_refs: list[str] = Field(min_length=1)
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    semantic_edge_refs: list[str] = Field(min_length=1)
    artifact_obligation_refs: list[str] = Field(min_length=1)
    implementation_spec_refs: list[str] = Field(min_length=1)
    validation_evidence_rows: list[RepoValidationEvidenceRow] = Field(min_length=1)
    validation_matrix_rows: list[RepoValidationMatrixRow] = Field(min_length=1)
    required_positive_evidence_posture: ValidationRequirementPosture
    required_reject_evidence_posture: ValidationRequirementPosture
    manual_review_posture: ManualReviewPosture
    tool_run_posture: ToolRunPosture
    validation_plan_posture: ValidationPlanPosture
    tests_not_truth_guardrail: str
    work_packet_execution_posture: WorkPacketExecutionPosture
    implementation_execution_posture: ImplementationExecutionPosture
    guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_validation_plan_row(self) -> "RepoWorkPacketValidationEvidencePlanRow":
        for attr in ("validation_plan_ref", "activation_package_ref", "candidate_ref"):
            _non_empty(getattr(self, attr), field_name=attr)
        for attr in (
            "scope_contract_refs",
            "activation_request_refs",
            "source_refs",
            "semantic_edge_refs",
            "artifact_obligation_refs",
            "implementation_spec_refs",
            "guardrail_refs",
        ):
            _validate_sorted_refs(getattr(self, attr), field_name=attr)
        _sorted_unique_by_ref(
            self.validation_evidence_rows,
            attr="validation_evidence_ref",
            field_name="validation_evidence_rows",
        )
        _sorted_unique_by_ref(
            self.validation_matrix_rows,
            attr="validation_matrix_ref",
            field_name="validation_matrix_rows",
        )
        _require_terms(
            self.tests_not_truth_guardrail,
            field_name="tests_not_truth_guardrail",
            terms=("tests", "not truth"),
        )
        if self.work_packet_execution_posture != "no_work_packet_execution_performed_by_v84":
            raise ValueError("V84-B validation plans cannot execute work packets")
        if self.implementation_execution_posture != "no_implementation_performed_by_v84":
            raise ValueError("V84-B validation plans cannot perform implementation")
        if self.tool_run_posture != "no_tool_run_performed_by_v84":
            raise ValueError("V84-B validation plans cannot run tools")
        if self.validation_plan_posture == "plan_complete_for_review_only":
            if self.required_positive_evidence_posture != "required_for_later_review":
                raise ValueError("complete validation plans require positive evidence posture")
            if self.required_reject_evidence_posture != "required_for_later_review":
                raise ValueError("complete validation plans require reject evidence posture")
            covered_edges = {
                ref for row in self.validation_matrix_rows for ref in row.semantic_edge_refs
            }
            if not set(self.semantic_edge_refs).issubset(covered_edges):
                raise ValueError("validation plan is not complete across semantic edges")
            covered_obligations = {
                ref for row in self.validation_matrix_rows for ref in row.artifact_obligation_refs
            }
            if not set(self.artifact_obligation_refs).issubset(covered_obligations):
                raise ValueError("validation plan is not complete across artifact obligations")
        _reject_v84_action_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("validation", "review", "no implementation"),
            ),
            field_name="limitation_note",
        )
        return self


class RepoWorkPacketValidationEvidencePlan(_CartographyBase):
    schema: Literal[REPO_WORK_PACKET_VALIDATION_EVIDENCE_PLAN_SCHEMA]
    work_packet_validation_evidence_plan_id: str
    work_packet_scope_contract_id: str
    implementation_target_surface_boundary_id: str
    work_packet_activation_review_request_id: str
    work_packet_activation_source_index_id: str
    work_packet_activation_non_execution_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    validation_plan_rows: list[RepoWorkPacketValidationEvidencePlanRow] = Field(min_length=1)
    validation_plan_summary: str

    @model_validator(mode="after")
    def _validate_validation_plan(self) -> "RepoWorkPacketValidationEvidencePlan":
        for attr in (
            "work_packet_validation_evidence_plan_id",
            "work_packet_scope_contract_id",
            "implementation_target_surface_boundary_id",
            "work_packet_activation_review_request_id",
            "work_packet_activation_source_index_id",
            "work_packet_activation_non_execution_guardrail_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
        ):
            _non_empty(getattr(self, attr), field_name=attr)
        _sorted_unique_by_ref(
            self.validation_plan_rows,
            attr="validation_plan_ref",
            field_name="validation_plan_rows",
        )
        _reject_v84_action_claim(
            _require_terms(
                self.validation_plan_summary,
                field_name="validation_plan_summary",
                terms=("validation", "review", "no implementation"),
            ),
            field_name="validation_plan_summary",
        )
        _assert_surface_id(
            surface_name="repo_work_packet_validation_evidence_plan",
            schema=REPO_WORK_PACKET_VALIDATION_EVIDENCE_PLAN_SCHEMA,
            payload=self.model_dump(mode="json"),
            id_key="work_packet_validation_evidence_plan_id",
            actual=self.work_packet_validation_evidence_plan_id,
        )
        return self


class RepoActivationExceptionRow(_CartographyBase):
    exception_ref: str
    exception_kind: ActivationExceptionKind
    source_refs: list[str] = Field(min_length=1)
    related_scope_refs: list[str] = Field(default_factory=list)
    related_target_refs: list[str] = Field(default_factory=list)
    related_validation_refs: list[str] = Field(default_factory=list)
    related_drift_refs: list[str] = Field(default_factory=list)
    blocking_posture: BlockingPosture
    visibility_posture: VisibilityPosture
    required_resolution_horizon: RequiredResolutionHorizon
    limitation_note: str

    @model_validator(mode="after")
    def _validate_activation_exception_row(self) -> "RepoActivationExceptionRow":
        _non_empty(self.exception_ref, field_name="exception_ref")
        for attr in (
            "source_refs",
            "related_scope_refs",
            "related_target_refs",
            "related_validation_refs",
            "related_drift_refs",
        ):
            _validate_sorted_refs(getattr(self, attr), field_name=attr)
        if self.visibility_posture == "hidden_rejected":
            raise ValueError("V84-B exceptions cannot be hidden")
        if self.blocking_posture == "blocking":
            if self.required_resolution_horizon == "not_applicable":
                raise ValueError("blocking exceptions require a resolution horizon")
        _reject_v84_action_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("exception", "review", "no implementation"),
            ),
            field_name="limitation_note",
        )
        return self


class RepoWorkPacketActivationExceptionRegisterRow(_CartographyBase):
    exception_register_ref: str
    activation_package_ref: str
    activation_request_refs: list[str] = Field(min_length=1)
    scope_contract_refs: list[str] = Field(min_length=1)
    target_boundary_refs: list[str] = Field(min_length=1)
    validation_plan_refs: list[str] = Field(min_length=1)
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    exception_rows: list[RepoActivationExceptionRow] = Field(min_length=1)
    blocking_posture: BlockingPosture
    required_next_surface: RequiredResolutionHorizon
    guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_exception_register_row(self) -> "RepoWorkPacketActivationExceptionRegisterRow":
        for attr in ("exception_register_ref", "activation_package_ref", "candidate_ref"):
            _non_empty(getattr(self, attr), field_name=attr)
        for attr in (
            "activation_request_refs",
            "scope_contract_refs",
            "target_boundary_refs",
            "validation_plan_refs",
            "source_refs",
            "guardrail_refs",
        ):
            _validate_sorted_refs(getattr(self, attr), field_name=attr)
        _sorted_unique_by_ref(
            self.exception_rows,
            attr="exception_ref",
            field_name="exception_rows",
        )
        if self.blocking_posture == "not_applicable" and any(
            row.blocking_posture == "blocking" for row in self.exception_rows
        ):
            raise ValueError("exception register cannot hide blocking exceptions")
        _reject_v84_action_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("exception", "review", "no implementation"),
            ),
            field_name="limitation_note",
        )
        return self


class RepoWorkPacketActivationExceptionRegister(_CartographyBase):
    schema: Literal[REPO_WORK_PACKET_ACTIVATION_EXCEPTION_REGISTER_SCHEMA]
    work_packet_activation_exception_register_id: str
    work_packet_scope_contract_id: str
    implementation_target_surface_boundary_id: str
    work_packet_validation_evidence_plan_id: str
    work_packet_activation_review_request_id: str
    work_packet_activation_source_index_id: str
    work_packet_activation_non_execution_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    exception_register_rows: list[RepoWorkPacketActivationExceptionRegisterRow] = Field(
        min_length=1
    )
    exception_register_summary: str

    @model_validator(mode="after")
    def _validate_exception_register(self) -> "RepoWorkPacketActivationExceptionRegister":
        for attr in (
            "work_packet_activation_exception_register_id",
            "work_packet_scope_contract_id",
            "implementation_target_surface_boundary_id",
            "work_packet_validation_evidence_plan_id",
            "work_packet_activation_review_request_id",
            "work_packet_activation_source_index_id",
            "work_packet_activation_non_execution_guardrail_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
        ):
            _non_empty(getattr(self, attr), field_name=attr)
        _sorted_unique_by_ref(
            self.exception_register_rows,
            attr="exception_register_ref",
            field_name="exception_register_rows",
        )
        _reject_v84_action_claim(
            _require_terms(
                self.exception_register_summary,
                field_name="exception_register_summary",
                terms=("exception", "review", "no implementation"),
            ),
            field_name="exception_register_summary",
        )
        _assert_surface_id(
            surface_name="repo_work_packet_activation_exception_register",
            schema=REPO_WORK_PACKET_ACTIVATION_EXCEPTION_REGISTER_SCHEMA,
            payload=self.model_dump(mode="json"),
            id_key="work_packet_activation_exception_register_id",
            actual=self.work_packet_activation_exception_register_id,
        )
        return self


def _v84a_released_bundle(
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
    RepoWorkPacketActivationSourceIndex,
    RepoWorkPacketActivationReviewRequest,
    RepoWorkPacketActivationNonExecutionGuardrail,
]:
    return derive_v84a_work_packet_activation_review_bundle(repo_root=repo_root)


def _eligible_v84a_request(
    request: RepoWorkPacketActivationReviewRequest,
) -> RepoWorkPacketActivationReviewRequestRow:
    return next(
        row
        for row in request.activation_request_rows
        if row.activation_review_eligibility_posture == "eligible_for_work_packet_activation_review"
    )


def _v83c_projection_refs(
    projection_packet: RepoImplementationSpecProjectionPacket,
) -> tuple[
    RepoIntentEdgeDecomposition,
    RepoArtifactObligationMap,
    RepoImplementationSpecProjectionPacket,
]:
    _ = projection_packet
    (
        _intent_source_index,
        _contract,
        _guardrail,
        edge_decomposition,
        obligation_map,
        _drift_register,
        v83_projection_packet,
        _handoff,
        _closeout,
    ) = _v83c_released_bundle()
    return edge_decomposition, obligation_map, v83_projection_packet


def derive_v84b_repo_work_packet_scope_contract(
    *,
    repo_root: Path | None = None,
    work_packet_activation_source_index: RepoWorkPacketActivationSourceIndex | None = None,
    work_packet_activation_review_request: RepoWorkPacketActivationReviewRequest | None = None,
    work_packet_activation_non_execution_guardrail: (
        RepoWorkPacketActivationNonExecutionGuardrail | None
    ) = None,
) -> RepoWorkPacketScopeContract:
    if (
        work_packet_activation_source_index is None
        or work_packet_activation_review_request is None
        or work_packet_activation_non_execution_guardrail is None
    ):
        v84a_bundle = _v84a_released_bundle(repo_root=repo_root)
        work_packet_activation_source_index = v84a_bundle[-3]
        work_packet_activation_review_request = v84a_bundle[-2]
        work_packet_activation_non_execution_guardrail = v84a_bundle[-1]
    (
        _intent_source_index,
        _contract,
        _intent_guardrail,
        _edge_decomposition,
        _obligation_map,
        _drift_register,
        projection_packet,
        _handoff,
        _closeout,
    ) = _v83c_released_bundle(repo_root=repo_root)
    request_row = _eligible_v84a_request(work_packet_activation_review_request)
    packet_row = projection_packet.projection_packet_rows[0]
    quality_gate_ref = packet_row.implementation_spec_quality_gate_rows[0].quality_gate_ref
    schema_targets = [
        "packages/adeu_repo_description/schema",
        "packages/adeu_repo_description/schema/repo_work_packet_scope_contract.v1.json",
        "packages/adeu_repo_description/schema/repo_implementation_target_surface_boundary.v1.json",
        "packages/adeu_repo_description/schema/repo_work_packet_validation_evidence_plan.v1.json",
        "packages/adeu_repo_description/schema/repo_work_packet_activation_exception_register.v1.json",
    ]
    in_scope = sorted(
        [
            "apps/api/fixtures/repo_description/vnext_plus237",
            "packages/adeu_repo_description/src/adeu_repo_description/__init__.py",
            "packages/adeu_repo_description/src/adeu_repo_description/export_schema.py",
            "packages/adeu_repo_description/src/adeu_repo_description/work_packet_activation_review.py",
            "packages/adeu_repo_description/tests/test_repo_description_export_schema.py",
            "packages/adeu_repo_description/tests/test_work_packet_activation_review_v84b.py",
            *schema_targets,
            "spec/repo_work_packet_scope_contract.schema.json",
            "spec/repo_implementation_target_surface_boundary.schema.json",
            "spec/repo_work_packet_validation_evidence_plan.schema.json",
            "spec/repo_work_packet_activation_exception_register.schema.json",
        ]
    )
    payload = {
        "schema": REPO_WORK_PACKET_SCOPE_CONTRACT_SCHEMA,
        "work_packet_scope_contract_id": "",
        "work_packet_activation_review_request_id": (
            work_packet_activation_review_request.work_packet_activation_review_request_id
        ),
        "work_packet_activation_source_index_id": (
            work_packet_activation_source_index.work_packet_activation_source_index_id
        ),
        "work_packet_activation_non_execution_guardrail_id": (
            work_packet_activation_non_execution_guardrail.work_packet_activation_non_execution_guardrail_id
        ),
        "review_id": "vNext+237",
        "snapshot_id": "vNext+237-work-packet-package-review-start",
        "source_set_id": "source-set:v84b:work-packet-package-review",
        "scope_contract_rows": [
            {
                "scope_contract_ref": "scope-contract:v84b:intent-to-spec-lock-review",
                "activation_package_ref": request_row.activation_package_ref,
                "activation_request_refs": [request_row.activation_request_ref],
                "projection_packet_refs": request_row.projection_packet_refs,
                "implementation_spec_refs": request_row.implementation_spec_refs,
                "candidate_ref": request_row.candidate_ref,
                "source_refs": sorted(
                    [
                        "docs/ASSESSMENT_vNEXT_PLUS236_EDGES.md",
                        "docs/LOCKED_CONTINUATION_vNEXT_PLUS236.md",
                        _V83_PROJECTION_FIXTURE,
                    ]
                ),
                "work_packet_kind": "schema_model_fixture_test_slice",
                "scope_statement": (
                    "Review-only scope package for a later lock over V84-B schema, "
                    "fixture, model, export, and test surfaces."
                ),
                "in_scope_artifact_refs": in_scope,
                "out_of_scope_artifact_refs": sorted(
                    [
                        "docs/DRAFT_NEXT_ARC_OPTIONS_v74.md",
                        "packages/adeu_repo_description/src/adeu_repo_description/semantic_implementation_spec.py",
                    ]
                ),
                "target_boundary_refs": [
                    "target-boundary:v84b:fixtures",
                    "target-boundary:v84b:module",
                    "target-boundary:v84b:schemas",
                    "target-boundary:v84b:tests",
                ],
                "validation_plan_refs": ["validation-plan:v84b:intent-to-spec-lock-review"],
                "canonical_lock_requirement_refs": [
                    "canonical-lock-requirement:v84b:intent-to-spec-lock-review"
                ],
                "activation_package_lineage_refs": [
                    "activation-package-lineage:v84b:intent-to-spec-lock-review"
                ],
                "canonical_lock_requirement_rows": [
                    {
                        "canonical_lock_requirement_ref": (
                            "canonical-lock-requirement:v84b:intent-to-spec-lock-review"
                        ),
                        "activation_package_ref": request_row.activation_package_ref,
                        "required_lock_kind": "schema_model_fixture_test_slice",
                        "required_lock_inputs": [
                            request_row.activation_request_ref,
                            packet_row.projection_packet_ref,
                        ],
                        "required_lock_guardrails": request_row.guardrail_refs,
                        "required_stop_gate_refs": [
                            "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS237.md"
                        ],
                        "required_assessment_refs": ["docs/ASSESSMENT_vNEXT_PLUS237_EDGES.md"],
                        "required_closeout_refs": [
                            "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS236.md"
                        ],
                        "required_later_authority_refs": (
                            request_row.canonical_lock_requirement_refs
                        ),
                        "lock_not_created_by_v84": True,
                        "limitation_note": (
                            "Canonical lock requirement is for later lock review with "
                            "no implementation."
                        ),
                    }
                ],
                "activation_package_lineage_rows": [
                    {
                        "activation_package_lineage_ref": (
                            "activation-package-lineage:v84b:intent-to-spec-lock-review"
                        ),
                        "activation_package_ref": request_row.activation_package_ref,
                        "candidate_ref": request_row.candidate_ref,
                        "projection_packet_refs": request_row.projection_packet_refs,
                        "quality_gate_refs": [quality_gate_ref],
                        "implementation_spec_refs": request_row.implementation_spec_refs,
                        "scope_contract_refs": ["scope-contract:v84b:intent-to-spec-lock-review"],
                        "target_boundary_refs": [
                            "target-boundary:v84b:fixtures",
                            "target-boundary:v84b:module",
                            "target-boundary:v84b:schemas",
                            "target-boundary:v84b:tests",
                        ],
                        "validation_plan_refs": ["validation-plan:v84b:intent-to-spec-lock-review"],
                        "lineage_posture": "lineage_bound_for_review_only",
                        "limitation_note": (
                            "Activation package lineage binds V83 projection, "
                            "quality gate, and V84-B package rows for review with "
                            "no implementation."
                        ),
                    }
                ],
                "scope_completeness_posture": "complete_for_activation_review_only",
                "activation_review_posture": "package_ready_for_review_only",
                "work_packet_execution_posture": "no_work_packet_execution_performed_by_v84",
                "implementation_execution_posture": "no_implementation_performed_by_v84",
                "guardrail_refs": request_row.guardrail_refs,
                "limitation_note": (
                    "Scope contract assembles a later lock review package with no "
                    "implementation and no work-packet execution."
                ),
            }
        ],
        "scope_contract_summary": (
            "V84-B scope contracts package target and validation requirements for "
            "review with no implementation."
        ),
    }
    payload["work_packet_scope_contract_id"] = _surface_id(
        "repo_work_packet_scope_contract",
        REPO_WORK_PACKET_SCOPE_CONTRACT_SCHEMA,
        payload,
        "work_packet_scope_contract_id",
    )
    scope_contract = RepoWorkPacketScopeContract.model_validate(payload)
    return scope_contract


def _target_boundary_row(
    *,
    target_boundary_ref: str,
    activation_package_ref: str,
    scope_contract_ref: str,
    activation_request_ref: str,
    candidate_ref: str,
    source_refs: list[str],
    target_surface_kind: TargetSurfaceKind,
    target_surface_refs: list[str],
    target_resolution_kind: TargetResolutionKind,
    target_access_role: TargetAccessRole,
    target_mutability_review_posture: TargetMutabilityReviewPosture,
    in_scope_counting_posture: InScopeCountingPosture,
    boundary_posture: BoundaryPosture = "bounded_for_review_only",
) -> dict[str, object]:
    return {
        "target_boundary_ref": target_boundary_ref,
        "activation_package_ref": activation_package_ref,
        "scope_contract_refs": [scope_contract_ref],
        "activation_request_refs": [activation_request_ref],
        "candidate_ref": candidate_ref,
        "source_refs": sorted(source_refs),
        "target_surface_kind": target_surface_kind,
        "target_surface_refs": sorted(target_surface_refs),
        "target_resolution_kind": target_resolution_kind,
        "target_currentness_posture": "current_repo_surface",
        "target_mutability_review_posture": target_mutability_review_posture,
        "target_access_role_rows": [
            {
                "target_access_role_ref": (
                    f"target-access-role:{target_boundary_ref.split(':')[-1]}"
                ),
                "target_surface_refs": sorted(target_surface_refs),
                "target_access_role": target_access_role,
                "source_refs": sorted(source_refs),
                "target_mutability_review_posture": target_mutability_review_posture,
                "in_scope_counting_posture": in_scope_counting_posture,
                "limitation_note": ("Target role is recorded for review and later lock only."),
            }
        ],
        "allowed_target_review_actions": sorted(
            [
                "describe_target_boundary",
                "inspect_source_metadata",
                "request_later_lock_review",
            ]
        ),
        "forbidden_target_mutation_actions": sorted(
            [
                "commit_change",
                "create_file",
                "delete_file",
                "edit_file",
                "mutate_fixture",
                "mutate_schema",
                "open_pr",
                "run_formatter_for_effect",
            ]
        ),
        "ownership_or_authority_refs": [
            "canonical-lock-requirement:v84b:intent-to-spec-lock-review"
        ],
        "boundary_posture": boundary_posture,
        "guardrail_refs": ["guardrail:v84a:intent-to-spec-lock-review"],
        "limitation_note": (
            "Target boundary is review-only with no implementation and no target mutation."
        ),
    }


def derive_v84b_repo_implementation_target_surface_boundary(
    *,
    repo_root: Path | None = None,
    work_packet_scope_contract: RepoWorkPacketScopeContract | None = None,
) -> RepoImplementationTargetSurfaceBoundary:
    if work_packet_scope_contract is None:
        *_, source_index, request, guardrail = _v84a_released_bundle(repo_root=repo_root)
        work_packet_scope_contract = derive_v84b_repo_work_packet_scope_contract(
            repo_root=repo_root,
            work_packet_activation_source_index=source_index,
            work_packet_activation_review_request=request,
            work_packet_activation_non_execution_guardrail=guardrail,
        )
    scope_row = work_packet_scope_contract.scope_contract_rows[0]
    activation_request_ref = scope_row.activation_request_refs[0]
    source_refs = scope_row.source_refs
    payload = {
        "schema": REPO_IMPLEMENTATION_TARGET_SURFACE_BOUNDARY_SCHEMA,
        "implementation_target_surface_boundary_id": "",
        "work_packet_scope_contract_id": work_packet_scope_contract.work_packet_scope_contract_id,
        "work_packet_activation_review_request_id": (
            work_packet_scope_contract.work_packet_activation_review_request_id
        ),
        "work_packet_activation_source_index_id": (
            work_packet_scope_contract.work_packet_activation_source_index_id
        ),
        "work_packet_activation_non_execution_guardrail_id": (
            work_packet_scope_contract.work_packet_activation_non_execution_guardrail_id
        ),
        "review_id": work_packet_scope_contract.review_id,
        "snapshot_id": work_packet_scope_contract.snapshot_id,
        "source_set_id": work_packet_scope_contract.source_set_id,
        "target_boundary_rows": sorted(
            [
                _target_boundary_row(
                    target_boundary_ref="target-boundary:v84b:fixtures",
                    activation_package_ref=scope_row.activation_package_ref,
                    scope_contract_ref=scope_row.scope_contract_ref,
                    activation_request_ref=activation_request_ref,
                    candidate_ref=scope_row.candidate_ref,
                    source_refs=source_refs,
                    target_surface_kind="fixture_file",
                    target_surface_refs=[
                        "apps/api/fixtures/repo_description/vnext_plus237",
                        "apps/api/fixtures/repo_description/vnext_plus237/repo_work_packet_scope_contract_v237_reference.json",
                        "apps/api/fixtures/repo_description/vnext_plus237/repo_implementation_target_surface_boundary_v237_reference.json",
                        "apps/api/fixtures/repo_description/vnext_plus237/repo_work_packet_validation_evidence_plan_v237_reference.json",
                        "apps/api/fixtures/repo_description/vnext_plus237/repo_work_packet_activation_exception_register_v237_reference.json",
                    ],
                    target_resolution_kind="bounded_directory_with_child_refs",
                    target_access_role="generated_artifact_target",
                    target_mutability_review_posture="generated_artifact_requires_later_lock",
                    in_scope_counting_posture="counts_as_bounded_later_scope",
                ),
                _target_boundary_row(
                    target_boundary_ref="target-boundary:v84b:module",
                    activation_package_ref=scope_row.activation_package_ref,
                    scope_contract_ref=scope_row.scope_contract_ref,
                    activation_request_ref=activation_request_ref,
                    candidate_ref=scope_row.candidate_ref,
                    source_refs=source_refs,
                    target_surface_kind="repo_description_module",
                    target_surface_refs=[
                        "packages/adeu_repo_description/src/adeu_repo_description/work_packet_activation_review.py"
                    ],
                    target_resolution_kind="concrete_file_ref",
                    target_access_role="prospective_write_target_for_later_lock",
                    target_mutability_review_posture="mutation_requires_later_lock",
                    in_scope_counting_posture="counts_as_bounded_later_scope",
                ),
                _target_boundary_row(
                    target_boundary_ref="target-boundary:v84b:schemas",
                    activation_package_ref=scope_row.activation_package_ref,
                    scope_contract_ref=scope_row.scope_contract_ref,
                    activation_request_ref=activation_request_ref,
                    candidate_ref=scope_row.candidate_ref,
                    source_refs=source_refs,
                    target_surface_kind="schema_file",
                    target_surface_refs=[
                        "packages/adeu_repo_description/schema",
                        "packages/adeu_repo_description/schema/repo_work_packet_scope_contract.v1.json",
                        "packages/adeu_repo_description/schema/repo_implementation_target_surface_boundary.v1.json",
                        "packages/adeu_repo_description/schema/repo_work_packet_validation_evidence_plan.v1.json",
                        "packages/adeu_repo_description/schema/repo_work_packet_activation_exception_register.v1.json",
                    ],
                    target_resolution_kind="bounded_directory_with_child_refs",
                    target_access_role="generated_artifact_target",
                    target_mutability_review_posture="generated_artifact_requires_later_lock",
                    in_scope_counting_posture="counts_as_bounded_later_scope",
                ),
                _target_boundary_row(
                    target_boundary_ref="target-boundary:v84b:tests",
                    activation_package_ref=scope_row.activation_package_ref,
                    scope_contract_ref=scope_row.scope_contract_ref,
                    activation_request_ref=activation_request_ref,
                    candidate_ref=scope_row.candidate_ref,
                    source_refs=source_refs,
                    target_surface_kind="test_file",
                    target_surface_refs=[
                        "packages/adeu_repo_description/tests/test_work_packet_activation_review_v84b.py"
                    ],
                    target_resolution_kind="concrete_test_ref",
                    target_access_role="prospective_write_target_for_later_lock",
                    target_mutability_review_posture="mutation_requires_later_lock",
                    in_scope_counting_posture="counts_as_bounded_later_scope",
                ),
                _target_boundary_row(
                    target_boundary_ref="target-boundary:v84b:selector-forbidden",
                    activation_package_ref=scope_row.activation_package_ref,
                    scope_contract_ref=scope_row.scope_contract_ref,
                    activation_request_ref=activation_request_ref,
                    candidate_ref=scope_row.candidate_ref,
                    source_refs=source_refs,
                    target_surface_kind="support_doc",
                    target_surface_refs=["docs/DRAFT_NEXT_ARC_OPTIONS_v74.md"],
                    target_resolution_kind="concrete_doc_ref",
                    target_access_role="forbidden_target",
                    target_mutability_review_posture="mutation_forbidden",
                    in_scope_counting_posture="forbidden_not_counted",
                    boundary_posture="blocked_by_forbidden_target",
                ),
            ],
            key=lambda row: str(row["target_boundary_ref"]),
        ),
        "target_boundary_summary": (
            "V84-B target boundaries classify module, schema, fixture, and test "
            "surfaces for later lock review with no implementation."
        ),
    }
    payload["implementation_target_surface_boundary_id"] = _surface_id(
        "repo_implementation_target_surface_boundary",
        REPO_IMPLEMENTATION_TARGET_SURFACE_BOUNDARY_SCHEMA,
        payload,
        "implementation_target_surface_boundary_id",
    )
    return RepoImplementationTargetSurfaceBoundary.model_validate(payload)


def derive_v84b_repo_work_packet_validation_evidence_plan(
    *,
    repo_root: Path | None = None,
    work_packet_scope_contract: RepoWorkPacketScopeContract | None = None,
    implementation_target_surface_boundary: RepoImplementationTargetSurfaceBoundary | None = None,
) -> RepoWorkPacketValidationEvidencePlan:
    if work_packet_scope_contract is None:
        work_packet_scope_contract = derive_v84b_repo_work_packet_scope_contract(
            repo_root=repo_root
        )
    if implementation_target_surface_boundary is None:
        implementation_target_surface_boundary = (
            derive_v84b_repo_implementation_target_surface_boundary(
                repo_root=repo_root,
                work_packet_scope_contract=work_packet_scope_contract,
            )
        )
    (
        _intent_source_index,
        _contract,
        _intent_guardrail,
        edge_decomposition,
        obligation_map,
        _drift_register,
        _projection_packet,
        _handoff,
        _closeout,
    ) = _v83c_released_bundle(repo_root=repo_root)
    scope_row = work_packet_scope_contract.scope_contract_rows[0]
    semantic_edge_refs = sorted(
        relation.semantic_relation_ref
        for row in edge_decomposition.edge_decomposition_rows
        for relation in row.semantic_relation_rows
    )
    artifact_obligation_refs = sorted(
        obligation.artifact_obligation_ref
        for row in obligation_map.obligation_map_rows
        for obligation in row.artifact_obligation_rows
    )
    target_boundary_refs = sorted(
        row.target_boundary_ref
        for row in implementation_target_surface_boundary.target_boundary_rows
        if row.boundary_posture == "bounded_for_review_only"
    )
    payload = {
        "schema": REPO_WORK_PACKET_VALIDATION_EVIDENCE_PLAN_SCHEMA,
        "work_packet_validation_evidence_plan_id": "",
        "work_packet_scope_contract_id": work_packet_scope_contract.work_packet_scope_contract_id,
        "implementation_target_surface_boundary_id": (
            implementation_target_surface_boundary.implementation_target_surface_boundary_id
        ),
        "work_packet_activation_review_request_id": (
            work_packet_scope_contract.work_packet_activation_review_request_id
        ),
        "work_packet_activation_source_index_id": (
            work_packet_scope_contract.work_packet_activation_source_index_id
        ),
        "work_packet_activation_non_execution_guardrail_id": (
            work_packet_scope_contract.work_packet_activation_non_execution_guardrail_id
        ),
        "review_id": work_packet_scope_contract.review_id,
        "snapshot_id": work_packet_scope_contract.snapshot_id,
        "source_set_id": work_packet_scope_contract.source_set_id,
        "validation_plan_rows": [
            {
                "validation_plan_ref": "validation-plan:v84b:intent-to-spec-lock-review",
                "activation_package_ref": scope_row.activation_package_ref,
                "scope_contract_refs": [scope_row.scope_contract_ref],
                "activation_request_refs": scope_row.activation_request_refs,
                "candidate_ref": scope_row.candidate_ref,
                "source_refs": scope_row.source_refs,
                "semantic_edge_refs": semantic_edge_refs,
                "artifact_obligation_refs": artifact_obligation_refs,
                "implementation_spec_refs": scope_row.implementation_spec_refs,
                "validation_evidence_rows": [
                    {
                        "validation_evidence_ref": "validation-evidence:v84b:positive-fixtures",
                        "semantic_edge_refs": semantic_edge_refs,
                        "artifact_obligation_refs": artifact_obligation_refs,
                        "implementation_spec_refs": scope_row.implementation_spec_refs,
                        "evidence_kind": "fixture_positive_case",
                        "required_artifact_refs": [
                            "apps/api/fixtures/repo_description/vnext_plus237/repo_work_packet_scope_contract_v237_reference.json"
                        ],
                        "required_execution_horizon": "no_execution_required",
                        "evidence_presence_posture": "requirement_recorded_for_review_only",
                        "acceptance_not_truth_guardrail": "Fixture acceptance is not truth.",
                        "limitation_note": (
                            "Positive fixture evidence is recorded for review with "
                            "no implementation."
                        ),
                    },
                    {
                        "validation_evidence_ref": "validation-evidence:v84b:reject-fixtures",
                        "semantic_edge_refs": semantic_edge_refs,
                        "artifact_obligation_refs": artifact_obligation_refs,
                        "implementation_spec_refs": scope_row.implementation_spec_refs,
                        "evidence_kind": "fixture_negative_case",
                        "required_artifact_refs": [
                            "apps/api/fixtures/repo_description/vnext_plus237/repo_work_packet_activation_v237_reject_target_glob_boundary.json"
                        ],
                        "required_execution_horizon": "no_execution_required",
                        "evidence_presence_posture": "requirement_recorded_for_review_only",
                        "acceptance_not_truth_guardrail": "Reject fixtures are not truth.",
                        "limitation_note": (
                            "Reject fixture evidence is recorded for review with no implementation."
                        ),
                    },
                ],
                "validation_matrix_rows": [
                    {
                        "validation_matrix_ref": "validation-matrix:v84b:edge-obligation-coverage",
                        "semantic_edge_refs": semantic_edge_refs,
                        "artifact_obligation_refs": artifact_obligation_refs,
                        "implementation_spec_refs": scope_row.implementation_spec_refs,
                        "target_boundary_refs": target_boundary_refs,
                        "evidence_kind": "validator_acceptance_check",
                        "positive_evidence_requirement": "required_for_later_review",
                        "reject_evidence_requirement": "required_for_later_review",
                        "regression_evidence_requirement": "required_for_later_review",
                        "manual_review_requirement": "manual_review_required_later",
                        "tool_applicability_posture": "tool_applicable_for_later_review",
                        "execution_required_later": False,
                        "acceptance_not_truth_guardrail": "Validation checks are not truth.",
                        "limitation_note": (
                            "Validation matrix covers semantic edges and obligations "
                            "for review with no implementation."
                        ),
                    }
                ],
                "required_positive_evidence_posture": "required_for_later_review",
                "required_reject_evidence_posture": "required_for_later_review",
                "manual_review_posture": "manual_review_required_later",
                "tool_run_posture": "no_tool_run_performed_by_v84",
                "validation_plan_posture": "plan_complete_for_review_only",
                "tests_not_truth_guardrail": "Tests are requirements, not truth.",
                "work_packet_execution_posture": "no_work_packet_execution_performed_by_v84",
                "implementation_execution_posture": "no_implementation_performed_by_v84",
                "guardrail_refs": scope_row.guardrail_refs,
                "limitation_note": (
                    "Validation plan is edge-bound and obligation-bound for review "
                    "with no implementation."
                ),
            }
        ],
        "validation_plan_summary": (
            "V84-B validation evidence plans define edge-bound requirements for "
            "review with no implementation."
        ),
    }
    payload["work_packet_validation_evidence_plan_id"] = _surface_id(
        "repo_work_packet_validation_evidence_plan",
        REPO_WORK_PACKET_VALIDATION_EVIDENCE_PLAN_SCHEMA,
        payload,
        "work_packet_validation_evidence_plan_id",
    )
    return RepoWorkPacketValidationEvidencePlan.model_validate(payload)


def derive_v84b_repo_work_packet_activation_exception_register(
    *,
    repo_root: Path | None = None,
    work_packet_scope_contract: RepoWorkPacketScopeContract | None = None,
    implementation_target_surface_boundary: RepoImplementationTargetSurfaceBoundary | None = None,
    work_packet_validation_evidence_plan: RepoWorkPacketValidationEvidencePlan | None = None,
) -> RepoWorkPacketActivationExceptionRegister:
    if work_packet_scope_contract is None:
        work_packet_scope_contract = derive_v84b_repo_work_packet_scope_contract(
            repo_root=repo_root
        )
    if implementation_target_surface_boundary is None:
        implementation_target_surface_boundary = (
            derive_v84b_repo_implementation_target_surface_boundary(
                repo_root=repo_root,
                work_packet_scope_contract=work_packet_scope_contract,
            )
        )
    if work_packet_validation_evidence_plan is None:
        work_packet_validation_evidence_plan = (
            derive_v84b_repo_work_packet_validation_evidence_plan(
                repo_root=repo_root,
                work_packet_scope_contract=work_packet_scope_contract,
                implementation_target_surface_boundary=implementation_target_surface_boundary,
            )
        )
    scope_row = work_packet_scope_contract.scope_contract_rows[0]
    validation_row = work_packet_validation_evidence_plan.validation_plan_rows[0]
    target_refs = sorted(
        row.target_boundary_ref
        for row in implementation_target_surface_boundary.target_boundary_rows
    )
    payload = {
        "schema": REPO_WORK_PACKET_ACTIVATION_EXCEPTION_REGISTER_SCHEMA,
        "work_packet_activation_exception_register_id": "",
        "work_packet_scope_contract_id": work_packet_scope_contract.work_packet_scope_contract_id,
        "implementation_target_surface_boundary_id": (
            implementation_target_surface_boundary.implementation_target_surface_boundary_id
        ),
        "work_packet_validation_evidence_plan_id": (
            work_packet_validation_evidence_plan.work_packet_validation_evidence_plan_id
        ),
        "work_packet_activation_review_request_id": (
            work_packet_scope_contract.work_packet_activation_review_request_id
        ),
        "work_packet_activation_source_index_id": (
            work_packet_scope_contract.work_packet_activation_source_index_id
        ),
        "work_packet_activation_non_execution_guardrail_id": (
            work_packet_scope_contract.work_packet_activation_non_execution_guardrail_id
        ),
        "review_id": work_packet_scope_contract.review_id,
        "snapshot_id": work_packet_scope_contract.snapshot_id,
        "source_set_id": work_packet_scope_contract.source_set_id,
        "exception_register_rows": [
            {
                "exception_register_ref": "exception-register:v84b:intent-to-spec-lock-review",
                "activation_package_ref": scope_row.activation_package_ref,
                "activation_request_refs": scope_row.activation_request_refs,
                "scope_contract_refs": [scope_row.scope_contract_ref],
                "target_boundary_refs": target_refs,
                "validation_plan_refs": [validation_row.validation_plan_ref],
                "candidate_ref": scope_row.candidate_ref,
                "source_refs": scope_row.source_refs,
                "exception_rows": [
                    {
                        "exception_ref": "exception:v84b:future-family-boundary",
                        "exception_kind": "later_family_boundary_unclear",
                        "source_refs": ["docs/ASSESSMENT_vNEXT_PLUS237_EDGES.md"],
                        "related_scope_refs": [scope_row.scope_contract_ref],
                        "related_target_refs": ["target-boundary:v84b:selector-forbidden"],
                        "related_validation_refs": [validation_row.validation_plan_ref],
                        "related_drift_refs": [],
                        "blocking_posture": "warning",
                        "visibility_posture": "visible_warning",
                        "required_resolution_horizon": "future_family_review",
                        "limitation_note": (
                            "Exception remains visible for review with no implementation."
                        ),
                    }
                ],
                "blocking_posture": "warning",
                "required_next_surface": "later_canonical_lock_review",
                "guardrail_refs": scope_row.guardrail_refs,
                "limitation_note": (
                    "Exception register preserves package warnings for review with "
                    "no implementation."
                ),
            }
        ],
        "exception_register_summary": (
            "V84-B exception register preserves activation package warnings and "
            "blocker posture for review with no implementation."
        ),
    }
    payload["work_packet_activation_exception_register_id"] = _surface_id(
        "repo_work_packet_activation_exception_register",
        REPO_WORK_PACKET_ACTIVATION_EXCEPTION_REGISTER_SCHEMA,
        payload,
        "work_packet_activation_exception_register_id",
    )
    return RepoWorkPacketActivationExceptionRegister.model_validate(payload)


def validate_v84b_work_packet_package_review_bundle(
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
    work_packet_activation_non_execution_guardrail: (RepoWorkPacketActivationNonExecutionGuardrail),
    work_packet_scope_contract: RepoWorkPacketScopeContract,
    implementation_target_surface_boundary: RepoImplementationTargetSurfaceBoundary,
    work_packet_validation_evidence_plan: RepoWorkPacketValidationEvidencePlan,
    work_packet_activation_exception_register: RepoWorkPacketActivationExceptionRegister,
) -> None:
    validate_v84a_work_packet_activation_review_bundle(
        v83_intent_source_index=v83_intent_source_index,
        v83_semantic_intent_contract=v83_semantic_intent_contract,
        v83_intent_non_implementation_guardrail=v83_intent_non_implementation_guardrail,
        v83_intent_edge_decomposition=v83_intent_edge_decomposition,
        v83_artifact_obligation_map=v83_artifact_obligation_map,
        v83_semantic_drift_ambiguity_register=v83_semantic_drift_ambiguity_register,
        v83_implementation_spec_projection_packet=v83_implementation_spec_projection_packet,
        v83_intent_to_work_packet_handoff=v83_intent_to_work_packet_handoff,
        v83_semantic_implementation_spec_family_closeout_alignment=(
            v83_semantic_implementation_spec_family_closeout_alignment
        ),
        work_packet_activation_source_index=work_packet_activation_source_index,
        work_packet_activation_review_request=work_packet_activation_review_request,
        work_packet_activation_non_execution_guardrail=(
            work_packet_activation_non_execution_guardrail
        ),
    )
    if (
        work_packet_scope_contract.work_packet_activation_review_request_id
        != work_packet_activation_review_request.work_packet_activation_review_request_id
    ):
        raise ValueError("V84-B scope contracts must reference released V84-A request")
    if (
        work_packet_scope_contract.work_packet_activation_source_index_id
        != work_packet_activation_source_index.work_packet_activation_source_index_id
    ):
        raise ValueError("V84-B scope contracts must reference released V84-A source index")
    if (
        work_packet_scope_contract.work_packet_activation_non_execution_guardrail_id
        != (
            work_packet_activation_non_execution_guardrail
            .work_packet_activation_non_execution_guardrail_id
        )
    ):
        raise ValueError("V84-B scope contracts must reference released V84-A guardrail")
    if (
        implementation_target_surface_boundary.work_packet_scope_contract_id
        != work_packet_scope_contract.work_packet_scope_contract_id
        or work_packet_validation_evidence_plan.work_packet_scope_contract_id
        != work_packet_scope_contract.work_packet_scope_contract_id
        or work_packet_activation_exception_register.work_packet_scope_contract_id
        != work_packet_scope_contract.work_packet_scope_contract_id
    ):
        raise ValueError("V84-B rows must reference the released scope contract")
    if (
        work_packet_validation_evidence_plan.implementation_target_surface_boundary_id
        != implementation_target_surface_boundary.implementation_target_surface_boundary_id
        or work_packet_activation_exception_register.implementation_target_surface_boundary_id
        != implementation_target_surface_boundary.implementation_target_surface_boundary_id
    ):
        raise ValueError("V84-B validation and exceptions must reference target boundaries")
    if (
        work_packet_activation_exception_register.work_packet_validation_evidence_plan_id
        != work_packet_validation_evidence_plan.work_packet_validation_evidence_plan_id
    ):
        raise ValueError("V84-B exceptions must reference validation plan")

    known_requests = {
        row.activation_request_ref: row
        for row in work_packet_activation_review_request.activation_request_rows
    }
    known_sources = {row.source_ref for row in work_packet_activation_source_index.source_rows}
    known_guardrails = {
        row.guardrail_ref for row in work_packet_activation_non_execution_guardrail.guardrail_rows
    }
    known_projection_packets = {
        row.projection_packet_ref: row
        for row in v83_implementation_spec_projection_packet.projection_packet_rows
    }
    known_specs = {
        spec.implementation_spec_ref
        for packet in known_projection_packets.values()
        for spec in packet.implementation_spec_rows
    }
    known_edges = {
        relation.semantic_relation_ref
        for row in v83_intent_edge_decomposition.edge_decomposition_rows
        for relation in row.semantic_relation_rows
    }
    known_obligations = {
        obligation.artifact_obligation_ref
        for row in v83_artifact_obligation_map.obligation_map_rows
        for obligation in row.artifact_obligation_rows
    }
    scope_rows = {
        row.scope_contract_ref: row for row in work_packet_scope_contract.scope_contract_rows
    }
    target_rows = {
        row.target_boundary_ref: row
        for row in implementation_target_surface_boundary.target_boundary_rows
    }
    validation_rows = {
        row.validation_plan_ref: row
        for row in work_packet_validation_evidence_plan.validation_plan_rows
    }
    scope_in_scope_sets = {
        row.scope_contract_ref: set(row.in_scope_artifact_refs)
        for row in work_packet_scope_contract.scope_contract_rows
    }

    for scope_row in work_packet_scope_contract.scope_contract_rows:
        if any(ref not in known_requests for ref in scope_row.activation_request_refs):
            raise ValueError("scope contracts must reference released V84-A requests")
        request_packages = {
            known_requests[ref].activation_package_ref for ref in scope_row.activation_request_refs
        }
        request_candidates = {
            known_requests[ref].candidate_ref for ref in scope_row.activation_request_refs
        }
        if request_packages != {scope_row.activation_package_ref}:
            raise ValueError("scope contract package must match activation request")
        if request_candidates != {scope_row.candidate_ref}:
            raise ValueError("scope contract candidate must match activation request")
        if any(ref not in known_sources for ref in scope_row.source_refs):
            raise ValueError("scope contract source refs must be indexed V84-A sources")
        if any(ref not in known_projection_packets for ref in scope_row.projection_packet_refs):
            raise ValueError("scope contract projection refs must be released V83-C packets")
        if any(ref not in known_specs for ref in scope_row.implementation_spec_refs):
            raise ValueError("scope contract implementation specs must be released V83-C specs")
        if any(ref not in known_guardrails for ref in scope_row.guardrail_refs):
            raise ValueError("scope contract guardrail refs must be released V84-A guardrails")
        in_scope_set = scope_in_scope_sets[scope_row.scope_contract_ref]
        for forbidden_ref in scope_row.out_of_scope_artifact_refs:
            if forbidden_ref in in_scope_set:
                raise ValueError("forbidden targets cannot be included in scope")

    for target_row in implementation_target_surface_boundary.target_boundary_rows:
        if any(ref not in scope_rows for ref in target_row.scope_contract_refs):
            raise ValueError("target boundaries must reference released V84-B scope contracts")
        if any(ref not in known_requests for ref in target_row.activation_request_refs):
            raise ValueError("target boundaries must reference released V84-A requests")
        scope_packages = {
            scope_rows[ref].activation_package_ref for ref in target_row.scope_contract_refs
        }
        if scope_packages != {target_row.activation_package_ref}:
            raise ValueError("target boundary package must match scope contract")
        if target_row.boundary_posture == "blocked_by_forbidden_target":
            for scope_ref in target_row.scope_contract_refs:
                in_scope_set = scope_in_scope_sets[scope_ref]
                if any(target_ref in in_scope_set for target_ref in target_row.target_surface_refs):
                    raise ValueError("forbidden targets cannot be included in scope")

    for validation_row in work_packet_validation_evidence_plan.validation_plan_rows:
        if any(ref not in scope_rows for ref in validation_row.scope_contract_refs):
            raise ValueError("validation plans must reference released V84-B scope contracts")
        if any(ref not in known_requests for ref in validation_row.activation_request_refs):
            raise ValueError("validation plans must reference released V84-A requests")
        scope_request_refs = {
            request_ref
            for scope_ref in validation_row.scope_contract_refs
            for request_ref in scope_rows[scope_ref].activation_request_refs
        }
        if set(validation_row.activation_request_refs) != scope_request_refs:
            raise ValueError("validation plan requests must match scope contracts")
        if any(ref not in known_edges for ref in validation_row.semantic_edge_refs):
            raise ValueError("validation plans must reference released V83-B semantic edges")
        if any(ref not in known_obligations for ref in validation_row.artifact_obligation_refs):
            raise ValueError("validation plans must reference released V83-B artifact obligations")
        if any(ref not in known_specs for ref in validation_row.implementation_spec_refs):
            raise ValueError("validation plans must reference released V83-C specs")
        for matrix_row in validation_row.validation_matrix_rows:
            if any(ref not in target_rows for ref in matrix_row.target_boundary_refs):
                raise ValueError("validation matrix refs must resolve to target boundaries")
        covered_edges = {
            ref
            for matrix_row in validation_row.validation_matrix_rows
            for ref in matrix_row.semantic_edge_refs
        }
        if not known_edges.issubset(covered_edges):
            raise ValueError("validation plan not edge complete")
        covered_obligations = {
            ref
            for matrix_row in validation_row.validation_matrix_rows
            for ref in matrix_row.artifact_obligation_refs
        }
        if not known_obligations.issubset(covered_obligations):
            raise ValueError("validation plan not obligation complete")

    for exception_register_row in work_packet_activation_exception_register.exception_register_rows:
        if any(ref not in scope_rows for ref in exception_register_row.scope_contract_refs):
            raise ValueError("exception registers must reference scope contracts")
        if any(ref not in known_requests for ref in exception_register_row.activation_request_refs):
            raise ValueError("exception registers must reference released V84-A requests")
        scope_request_refs = {
            request_ref
            for scope_ref in exception_register_row.scope_contract_refs
            for request_ref in scope_rows[scope_ref].activation_request_refs
        }
        if set(exception_register_row.activation_request_refs) != scope_request_refs:
            raise ValueError("exception register requests must match scope contracts")
        if any(ref not in target_rows for ref in exception_register_row.target_boundary_refs):
            raise ValueError("exception registers must reference target boundaries")
        if any(ref not in validation_rows for ref in exception_register_row.validation_plan_refs):
            raise ValueError("exception registers must reference validation plans")
        scope_packages = {
            scope_rows[ref].activation_package_ref
            for ref in exception_register_row.scope_contract_refs
        }
        if scope_packages != {exception_register_row.activation_package_ref}:
            raise ValueError("exception register package must match scope contract")


def derive_v84b_work_packet_package_review_bundle(
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
    RepoWorkPacketScopeContract,
    RepoImplementationTargetSurfaceBoundary,
    RepoWorkPacketValidationEvidencePlan,
    RepoWorkPacketActivationExceptionRegister,
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
        source_index,
        request,
        guardrail,
    ) = _v84a_released_bundle(repo_root=repo_root)
    scope_contract = derive_v84b_repo_work_packet_scope_contract(
        repo_root=repo_root,
        work_packet_activation_source_index=source_index,
        work_packet_activation_review_request=request,
        work_packet_activation_non_execution_guardrail=guardrail,
    )
    target_boundary = derive_v84b_repo_implementation_target_surface_boundary(
        repo_root=repo_root,
        work_packet_scope_contract=scope_contract,
    )
    validation_plan = derive_v84b_repo_work_packet_validation_evidence_plan(
        repo_root=repo_root,
        work_packet_scope_contract=scope_contract,
        implementation_target_surface_boundary=target_boundary,
    )
    exception_register = derive_v84b_repo_work_packet_activation_exception_register(
        repo_root=repo_root,
        work_packet_scope_contract=scope_contract,
        implementation_target_surface_boundary=target_boundary,
        work_packet_validation_evidence_plan=validation_plan,
    )
    validate_v84b_work_packet_package_review_bundle(
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
        work_packet_scope_contract=scope_contract,
        implementation_target_surface_boundary=target_boundary,
        work_packet_validation_evidence_plan=validation_plan,
        work_packet_activation_exception_register=exception_register,
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
        scope_contract,
        target_boundary,
        validation_plan,
        exception_register,
    )


_V84C_BLOCKING_WARNING_KINDS = {
    "carried_semantic_drift_blocker",
    "generated_spec_provenance_gap",
    "graph_memory_authority_gap",
    "implementation_authority_gap",
    "missing_positive_evidence_requirement",
    "missing_reject_evidence_requirement",
    "missing_validation_plan",
    "product_authority_gap",
    "release_authority_gap",
    "runtime_authority_gap",
    "unbounded_target_surface",
    "validation_plan_not_edge_complete",
    "validation_plan_not_obligation_complete",
}


def _require_v84c_no_action_postures(
    *,
    activation_authority_posture: ActivationAuthorityPosture,
    implementation_lock_status: ImplementationLockStatus,
    activation_execution_posture: ActivationExecutionPosture,
    work_packet_execution_posture: WorkPacketExecutionPosture,
    implementation_execution_posture: ImplementationExecutionPosture,
    target_mutation_posture: TargetMutationPosture,
    pr_commit_release_posture: PrCommitReleasePosture,
    surface: str,
) -> None:
    if activation_authority_posture != "no_activation_authority_granted_by_v84":
        raise ValueError(f"{surface} cannot grant activation authority")
    if implementation_lock_status != "no_implementation_lock_created_by_v84":
        raise ValueError(f"{surface} cannot create implementation locks")
    if activation_execution_posture != "no_activation_performed_by_v84":
        raise ValueError(f"{surface} cannot perform activation")
    if work_packet_execution_posture != "no_work_packet_execution_performed_by_v84":
        raise ValueError(f"{surface} cannot execute work packets")
    if implementation_execution_posture != "no_implementation_performed_by_v84":
        raise ValueError(f"{surface} cannot perform implementation")
    if target_mutation_posture != "no_target_mutation_performed_by_v84":
        raise ValueError(f"{surface} cannot mutate targets")
    if pr_commit_release_posture != "no_pr_commit_merge_release_performed_by_v84":
        raise ValueError(f"{surface} cannot create PR, merge, or release authority")


class RepoWorkPacketActivationReadinessSummaryRow(_CartographyBase):
    summary_ref: str
    activation_package_ref: str
    activation_request_refs: list[str] = Field(min_length=1)
    scope_contract_refs: list[str] = Field(default_factory=list)
    target_boundary_refs: list[str] = Field(default_factory=list)
    validation_plan_refs: list[str] = Field(default_factory=list)
    exception_register_refs: list[str] = Field(default_factory=list)
    projection_packet_refs: list[str] = Field(min_length=1)
    quality_gate_refs: list[str] = Field(min_length=1)
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    summary_posture: ActivationReadinessSummaryPosture
    ready_basis_posture: ActivationReadyBasisPosture
    carried_blocker_refs: list[str] = Field(default_factory=list)
    carried_warning_refs: list[str] = Field(default_factory=list)
    required_later_authority_refs: list[str] = Field(default_factory=list)
    coverage_summary_refs: list[str] = Field(default_factory=list)
    coverage_posture: ActivationCoveragePosture
    canonical_lock_requirement_refs: list[str] = Field(default_factory=list)
    activation_authority_posture: ActivationAuthorityPosture
    implementation_lock_status: ImplementationLockStatus
    activation_execution_posture: ActivationExecutionPosture
    work_packet_execution_posture: WorkPacketExecutionPosture
    implementation_execution_posture: ImplementationExecutionPosture
    target_mutation_posture: TargetMutationPosture
    pr_commit_release_posture: PrCommitReleasePosture
    guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_summary_row(self) -> "RepoWorkPacketActivationReadinessSummaryRow":
        for attr in ("summary_ref", "activation_package_ref", "candidate_ref"):
            _non_empty(getattr(self, attr), field_name=attr)
        for attr in (
            "activation_request_refs",
            "scope_contract_refs",
            "target_boundary_refs",
            "validation_plan_refs",
            "exception_register_refs",
            "projection_packet_refs",
            "quality_gate_refs",
            "source_refs",
            "carried_blocker_refs",
            "carried_warning_refs",
            "required_later_authority_refs",
            "coverage_summary_refs",
            "canonical_lock_requirement_refs",
            "guardrail_refs",
        ):
            _validate_sorted_refs(getattr(self, attr), field_name=attr)
        _require_v84c_no_action_postures(
            activation_authority_posture=self.activation_authority_posture,
            implementation_lock_status=self.implementation_lock_status,
            activation_execution_posture=self.activation_execution_posture,
            work_packet_execution_posture=self.work_packet_execution_posture,
            implementation_execution_posture=self.implementation_execution_posture,
            target_mutation_posture=self.target_mutation_posture,
            pr_commit_release_posture=self.pr_commit_release_posture,
            surface="V84-C summaries",
        )
        if self.summary_posture == "ready_for_later_implementation_lock_review":
            if self.ready_basis_posture != "ready_no_blockers":
                raise ValueError("ready summaries require ready_no_blockers")
            if self.carried_blocker_refs or self.carried_warning_refs:
                raise ValueError("ready summaries cannot carry blockers or warnings")
            if self.coverage_posture != "edge_and_obligation_complete_for_review":
                raise ValueError("ready summaries require complete coverage")
            for attr in (
                "scope_contract_refs",
                "target_boundary_refs",
                "validation_plan_refs",
                "canonical_lock_requirement_refs",
                "coverage_summary_refs",
            ):
                if not getattr(self, attr):
                    raise ValueError("ready summaries require package and coverage refs")
        if self.summary_posture == "ready_with_nonblocking_warnings":
            if self.ready_basis_posture != "ready_with_nonblocking_warnings":
                raise ValueError("warning-ready summaries require warning basis")
            if self.carried_blocker_refs:
                raise ValueError("warning-ready summaries cannot carry blockers")
            if not self.carried_warning_refs:
                raise ValueError("warning-ready summaries must carry warnings")
            if self.coverage_posture != "edge_and_obligation_complete_for_review":
                raise ValueError("warning-ready summaries require complete coverage")
        if self.summary_posture.startswith("blocked_by_"):
            if self.ready_basis_posture not in {
                "not_ready_blockers_remain",
                "authority_review_requested_for_blockers",
                "blocker_settlement_review_requested",
            }:
                raise ValueError("blocked readiness summaries must preserve blocker basis")
            if not self.carried_blocker_refs:
                raise ValueError("blocked readiness summaries must carry blockers")
        if self.summary_posture == "future_family_only":
            if self.ready_basis_posture != "future_family_only":
                raise ValueError("future-family summaries require future-family basis")
        if self.summary_posture == "rejected_out_of_scope":
            if self.ready_basis_posture != "rejected_out_of_scope":
                raise ValueError("rejected summaries require rejected basis")
        _reject_v84_action_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("review", "later lock", "no implementation"),
            ),
            field_name="limitation_note",
        )
        return self


class RepoWorkPacketActivationReadinessSummary(_CartographyBase):
    schema: Literal[REPO_WORK_PACKET_ACTIVATION_READINESS_SUMMARY_SCHEMA]
    work_packet_activation_readiness_summary_id: str
    work_packet_activation_review_request_id: str
    work_packet_activation_source_index_id: str
    work_packet_activation_non_execution_guardrail_id: str
    work_packet_scope_contract_id: str
    implementation_target_surface_boundary_id: str
    work_packet_validation_evidence_plan_id: str
    work_packet_activation_exception_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    summary_rows: list[RepoWorkPacketActivationReadinessSummaryRow] = Field(min_length=1)
    readiness_summary: str

    @model_validator(mode="after")
    def _validate_readiness_summary(self) -> "RepoWorkPacketActivationReadinessSummary":
        for attr in (
            "work_packet_activation_readiness_summary_id",
            "work_packet_activation_review_request_id",
            "work_packet_activation_source_index_id",
            "work_packet_activation_non_execution_guardrail_id",
            "work_packet_scope_contract_id",
            "implementation_target_surface_boundary_id",
            "work_packet_validation_evidence_plan_id",
            "work_packet_activation_exception_register_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
        ):
            _non_empty(getattr(self, attr), field_name=attr)
        _sorted_unique_by_ref(
            self.summary_rows,
            attr="summary_ref",
            field_name="summary_rows",
        )
        _reject_v84_action_claim(
            _require_terms(
                self.readiness_summary,
                field_name="readiness_summary",
                terms=("readiness", "review", "no implementation"),
            ),
            field_name="readiness_summary",
        )
        _assert_surface_id(
            surface_name="repo_work_packet_activation_readiness_summary",
            schema=REPO_WORK_PACKET_ACTIVATION_READINESS_SUMMARY_SCHEMA,
            payload=self.model_dump(mode="json"),
            id_key="work_packet_activation_readiness_summary_id",
            actual=self.work_packet_activation_readiness_summary_id,
        )
        return self


class RepoPostWorkPacketActivationReviewHandoffRow(_CartographyBase):
    handoff_ref: str
    activation_package_ref: str
    summary_refs: list[str] = Field(min_length=1)
    activation_request_refs: list[str] = Field(min_length=1)
    scope_contract_refs: list[str] = Field(default_factory=list)
    target_boundary_refs: list[str] = Field(default_factory=list)
    validation_plan_refs: list[str] = Field(default_factory=list)
    carried_exception_refs: list[str] = Field(default_factory=list)
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    handoff_target: ActivationHandoffTarget
    handoff_subject_horizon: ActivationHandoffSubjectHorizon
    handoff_posture: ActivationHandoffPosture
    handoff_authority_horizon: ActivationHandoffAuthorityHorizon
    handoff_activation_status: ActivationHandoffStatus
    implementation_lock_status: ImplementationLockStatus
    canonical_lock_requirement_refs: list[str] = Field(default_factory=list)
    required_later_authority_refs: list[str] = Field(default_factory=list)
    activation_execution_posture: ActivationExecutionPosture
    work_packet_execution_posture: WorkPacketExecutionPosture
    implementation_execution_posture: ImplementationExecutionPosture
    target_mutation_posture: TargetMutationPosture
    pr_commit_release_posture: PrCommitReleasePosture
    guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_handoff_row(self) -> "RepoPostWorkPacketActivationReviewHandoffRow":
        for attr in ("handoff_ref", "activation_package_ref", "candidate_ref"):
            _non_empty(getattr(self, attr), field_name=attr)
        for attr in (
            "summary_refs",
            "activation_request_refs",
            "scope_contract_refs",
            "target_boundary_refs",
            "validation_plan_refs",
            "carried_exception_refs",
            "source_refs",
            "canonical_lock_requirement_refs",
            "required_later_authority_refs",
            "guardrail_refs",
        ):
            _validate_sorted_refs(getattr(self, attr), field_name=attr)
        _require_v84c_no_action_postures(
            activation_authority_posture="no_activation_authority_granted_by_v84",
            implementation_lock_status=self.implementation_lock_status,
            activation_execution_posture=self.activation_execution_posture,
            work_packet_execution_posture=self.work_packet_execution_posture,
            implementation_execution_posture=self.implementation_execution_posture,
            target_mutation_posture=self.target_mutation_posture,
            pr_commit_release_posture=self.pr_commit_release_posture,
            surface="V84-C handoffs",
        )
        if self.handoff_target == "future_canonical_implementation_lock_review":
            if self.handoff_activation_status != "later_lock_review_requested":
                raise ValueError("canonical lock handoffs require later-lock review status")
            if not self.canonical_lock_requirement_refs:
                raise ValueError("canonical lock handoffs require canonical lock refs")
            if self.handoff_authority_horizon != "canonical_implementation_lock_review":
                raise ValueError("canonical lock handoffs require canonical authority horizon")
        if self.handoff_posture == "ready_for_later_review":
            if self.carried_exception_refs:
                raise ValueError("ready handoffs cannot carry exceptions")
        if self.handoff_posture == "ready_with_nonblocking_warnings":
            if not self.carried_exception_refs:
                raise ValueError("warning-ready handoffs must carry warnings")
        if self.handoff_posture == "blocked_by_carried_exceptions":
            if not self.carried_exception_refs:
                raise ValueError("blocked handoffs must carry exceptions")
            if self.handoff_activation_status != "blocker_settlement_requested":
                raise ValueError("blocked handoffs require blocker settlement status")
        if self.handoff_posture == "future_family_only":
            if self.handoff_activation_status != "future_family_only":
                raise ValueError("future-family handoffs require future-family status")
        _reject_v84_action_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("later review", "no implementation", "no activation"),
            ),
            field_name="limitation_note",
        )
        return self


class RepoPostWorkPacketActivationReviewHandoff(_CartographyBase):
    schema: Literal[REPO_POST_WORK_PACKET_ACTIVATION_REVIEW_HANDOFF_SCHEMA]
    post_work_packet_activation_review_handoff_id: str
    work_packet_activation_readiness_summary_id: str
    work_packet_activation_review_request_id: str
    work_packet_activation_source_index_id: str
    work_packet_activation_non_execution_guardrail_id: str
    work_packet_scope_contract_id: str
    implementation_target_surface_boundary_id: str
    work_packet_validation_evidence_plan_id: str
    work_packet_activation_exception_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    handoff_rows: list[RepoPostWorkPacketActivationReviewHandoffRow] = Field(min_length=1)
    handoff_summary: str

    @model_validator(mode="after")
    def _validate_handoff(self) -> "RepoPostWorkPacketActivationReviewHandoff":
        for attr in (
            "post_work_packet_activation_review_handoff_id",
            "work_packet_activation_readiness_summary_id",
            "work_packet_activation_review_request_id",
            "work_packet_activation_source_index_id",
            "work_packet_activation_non_execution_guardrail_id",
            "work_packet_scope_contract_id",
            "implementation_target_surface_boundary_id",
            "work_packet_validation_evidence_plan_id",
            "work_packet_activation_exception_register_id",
            "review_id",
            "snapshot_id",
            "source_set_id",
        ):
            _non_empty(getattr(self, attr), field_name=attr)
        _sorted_unique_by_ref(
            self.handoff_rows,
            attr="handoff_ref",
            field_name="handoff_rows",
        )
        _reject_v84_action_claim(
            _require_terms(
                self.handoff_summary,
                field_name="handoff_summary",
                terms=("later review", "no implementation", "no activation"),
            ),
            field_name="handoff_summary",
        )
        _assert_surface_id(
            surface_name="repo_post_work_packet_activation_review_handoff",
            schema=REPO_POST_WORK_PACKET_ACTIVATION_REVIEW_HANDOFF_SCHEMA,
            payload=self.model_dump(mode="json"),
            id_key="post_work_packet_activation_review_handoff_id",
            actual=self.post_work_packet_activation_review_handoff_id,
        )
        return self


class RepoWorkPacketActivationFamilyCloseoutAlignment(_CartographyBase):
    schema: Literal[REPO_WORK_PACKET_ACTIVATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA]
    work_packet_activation_family_closeout_alignment_id: str
    work_packet_activation_readiness_summary_id: str
    post_work_packet_activation_review_handoff_id: str
    family: Literal["V84"]
    closed_by_arc: Literal["vNext+238"]
    closed_slice_ladder: list[WorkPacketActivationClosedSlice] = Field(min_length=3)
    shipped_record_shapes: list[WorkPacketActivationShippedRecordShape] = Field(min_length=1)
    consumed_source_families: list[WorkPacketActivationConsumedFamily] = Field(min_length=1)
    family_closed_on_main: Literal["closed_after_v84c_merge"]
    future_family_authority: Literal["next_selector_required"]
    unselected_future_surfaces: list[WorkPacketActivationUnselectedFutureSurface] = Field(
        min_length=1
    )
    work_packet_activation_review_boundary: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_family_closeout(self) -> "RepoWorkPacketActivationFamilyCloseoutAlignment":
        for attr in (
            "closed_slice_ladder",
            "shipped_record_shapes",
            "consumed_source_families",
            "unselected_future_surfaces",
        ):
            _validate_sorted_refs(getattr(self, attr), field_name=attr)
        if self.closed_slice_ladder != ["V84-A", "V84-B", "V84-C"]:
            raise ValueError("work-packet activation closeout must close V84-A/B/C")
        if "v85_selection" not in self.unselected_future_surfaces:
            raise ValueError("work-packet activation closeout must not select V85")
        if REPO_WORK_PACKET_ACTIVATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA not in (
            self.shipped_record_shapes
        ):
            raise ValueError("V84 closeout must include its family closeout record shape")
        _reject_v84_action_claim(
            _require_terms(
                self.work_packet_activation_review_boundary,
                field_name="work_packet_activation_review_boundary",
                terms=("no activation", "no implementation", "no v85 selection"),
            ),
            field_name="work_packet_activation_review_boundary",
        )
        _reject_v84_action_claim(
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("review", "no activation", "no implementation"),
            ),
            field_name="limitation_note",
        )
        _assert_surface_id(
            surface_name="repo_work_packet_activation_family_closeout_alignment",
            schema=REPO_WORK_PACKET_ACTIVATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            payload=self.model_dump(mode="json"),
            id_key="work_packet_activation_family_closeout_alignment_id",
            actual=self.work_packet_activation_family_closeout_alignment_id,
        )
        return self


def _v84b_released_bundle(
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
    RepoWorkPacketActivationSourceIndex,
    RepoWorkPacketActivationReviewRequest,
    RepoWorkPacketActivationNonExecutionGuardrail,
    RepoWorkPacketScopeContract,
    RepoImplementationTargetSurfaceBoundary,
    RepoWorkPacketValidationEvidencePlan,
    RepoWorkPacketActivationExceptionRegister,
]:
    return derive_v84b_work_packet_package_review_bundle(repo_root=repo_root)


def derive_v84c_repo_work_packet_activation_readiness_summary(
    *,
    repo_root: Path | None = None,
    work_packet_activation_source_index: RepoWorkPacketActivationSourceIndex | None = None,
    work_packet_activation_review_request: RepoWorkPacketActivationReviewRequest | None = None,
    work_packet_activation_non_execution_guardrail: (
        RepoWorkPacketActivationNonExecutionGuardrail | None
    ) = None,
    work_packet_scope_contract: RepoWorkPacketScopeContract | None = None,
    implementation_target_surface_boundary: RepoImplementationTargetSurfaceBoundary | None = None,
    work_packet_validation_evidence_plan: RepoWorkPacketValidationEvidencePlan | None = None,
    work_packet_activation_exception_register: (
        RepoWorkPacketActivationExceptionRegister | None
    ) = None,
) -> RepoWorkPacketActivationReadinessSummary:
    if any(
        item is None
        for item in (
            work_packet_activation_source_index,
            work_packet_activation_review_request,
            work_packet_activation_non_execution_guardrail,
            work_packet_scope_contract,
            implementation_target_surface_boundary,
            work_packet_validation_evidence_plan,
            work_packet_activation_exception_register,
        )
    ):
        (
            _intent_source_index,
            _semantic_intent_contract,
            _intent_non_implementation_guardrail,
            _intent_edge_decomposition,
            _artifact_obligation_map,
            _semantic_drift_ambiguity_register,
            _implementation_spec_projection_packet,
            _intent_to_work_packet_handoff,
            _semantic_implementation_spec_family_closeout_alignment,
            work_packet_activation_source_index,
            work_packet_activation_review_request,
            work_packet_activation_non_execution_guardrail,
            work_packet_scope_contract,
            implementation_target_surface_boundary,
            work_packet_validation_evidence_plan,
            work_packet_activation_exception_register,
        ) = _v84b_released_bundle(repo_root=repo_root)
    assert work_packet_activation_source_index is not None
    assert work_packet_activation_review_request is not None
    assert work_packet_activation_non_execution_guardrail is not None
    assert work_packet_scope_contract is not None
    assert implementation_target_surface_boundary is not None
    assert work_packet_validation_evidence_plan is not None
    assert work_packet_activation_exception_register is not None
    scope_row = work_packet_scope_contract.scope_contract_rows[0]
    validation_row = work_packet_validation_evidence_plan.validation_plan_rows[0]
    exception_register_row = work_packet_activation_exception_register.exception_register_rows[0]
    warning_refs = sorted(
        row.exception_ref
        for row in exception_register_row.exception_rows
        if row.blocking_posture == "warning"
    )
    payload = {
        "schema": REPO_WORK_PACKET_ACTIVATION_READINESS_SUMMARY_SCHEMA,
        "work_packet_activation_readiness_summary_id": "",
        "work_packet_activation_review_request_id": (
            work_packet_activation_review_request.work_packet_activation_review_request_id
        ),
        "work_packet_activation_source_index_id": (
            work_packet_activation_source_index.work_packet_activation_source_index_id
        ),
        "work_packet_activation_non_execution_guardrail_id": (
            work_packet_activation_non_execution_guardrail.work_packet_activation_non_execution_guardrail_id
        ),
        "work_packet_scope_contract_id": work_packet_scope_contract.work_packet_scope_contract_id,
        "implementation_target_surface_boundary_id": (
            implementation_target_surface_boundary.implementation_target_surface_boundary_id
        ),
        "work_packet_validation_evidence_plan_id": (
            work_packet_validation_evidence_plan.work_packet_validation_evidence_plan_id
        ),
        "work_packet_activation_exception_register_id": (
            work_packet_activation_exception_register.work_packet_activation_exception_register_id
        ),
        "review_id": "vNext+238",
        "snapshot_id": "vNext+238-work-packet-activation-readiness-start",
        "source_set_id": "source-set:v84c:work-packet-activation-readiness",
        "summary_rows": [
            {
                "summary_ref": "readiness-summary:v84c:intent-to-spec-lock-review",
                "activation_package_ref": scope_row.activation_package_ref,
                "activation_request_refs": scope_row.activation_request_refs,
                "scope_contract_refs": [scope_row.scope_contract_ref],
                "target_boundary_refs": scope_row.target_boundary_refs,
                "validation_plan_refs": [validation_row.validation_plan_ref],
                "exception_register_refs": [exception_register_row.exception_register_ref],
                "projection_packet_refs": scope_row.projection_packet_refs,
                "quality_gate_refs": scope_row.activation_package_lineage_rows[0].quality_gate_refs,
                "candidate_ref": scope_row.candidate_ref,
                "source_refs": sorted(
                    [
                        _V84A_REQUEST_FIXTURE,
                        _V84A_SOURCE_INDEX_FIXTURE,
                        _V84A_GUARDRAIL_FIXTURE,
                        _V84B_SCOPE_FIXTURE,
                        _V84B_TARGET_FIXTURE,
                        _V84B_VALIDATION_FIXTURE,
                        _V84B_EXCEPTION_FIXTURE,
                    ]
                ),
                "summary_posture": "ready_with_nonblocking_warnings",
                "ready_basis_posture": "ready_with_nonblocking_warnings",
                "carried_blocker_refs": [],
                "carried_warning_refs": warning_refs,
                "required_later_authority_refs": scope_row.canonical_lock_requirement_refs,
                "coverage_summary_refs": [
                    row.validation_matrix_ref for row in validation_row.validation_matrix_rows
                ],
                "coverage_posture": "edge_and_obligation_complete_for_review",
                "canonical_lock_requirement_refs": scope_row.canonical_lock_requirement_refs,
                "activation_authority_posture": "no_activation_authority_granted_by_v84",
                "implementation_lock_status": "no_implementation_lock_created_by_v84",
                "activation_execution_posture": "no_activation_performed_by_v84",
                "work_packet_execution_posture": "no_work_packet_execution_performed_by_v84",
                "implementation_execution_posture": "no_implementation_performed_by_v84",
                "target_mutation_posture": "no_target_mutation_performed_by_v84",
                "pr_commit_release_posture": "no_pr_commit_merge_release_performed_by_v84",
                "guardrail_refs": scope_row.guardrail_refs,
                "limitation_note": (
                    "Readiness summary is warning-ready for later lock review with "
                    "no implementation and no activation."
                ),
            }
        ],
        "readiness_summary": (
            "V84-C summarizes work-packet activation readiness for later lock "
            "review with no implementation, no activation, no target mutation, "
            "and no release."
        ),
    }
    payload["work_packet_activation_readiness_summary_id"] = _surface_id(
        "repo_work_packet_activation_readiness_summary",
        REPO_WORK_PACKET_ACTIVATION_READINESS_SUMMARY_SCHEMA,
        payload,
        "work_packet_activation_readiness_summary_id",
    )
    return RepoWorkPacketActivationReadinessSummary.model_validate(payload)


def derive_v84c_repo_post_work_packet_activation_review_handoff(
    *,
    repo_root: Path | None = None,
    work_packet_activation_readiness_summary: (
        RepoWorkPacketActivationReadinessSummary | None
    ) = None,
) -> RepoPostWorkPacketActivationReviewHandoff:
    if work_packet_activation_readiness_summary is None:
        summary = derive_v84c_repo_work_packet_activation_readiness_summary(repo_root=repo_root)
    else:
        summary = work_packet_activation_readiness_summary
    summary_row = summary.summary_rows[0]
    payload = {
        "schema": REPO_POST_WORK_PACKET_ACTIVATION_REVIEW_HANDOFF_SCHEMA,
        "post_work_packet_activation_review_handoff_id": "",
        "work_packet_activation_readiness_summary_id": (
            summary.work_packet_activation_readiness_summary_id
        ),
        "work_packet_activation_review_request_id": (
            summary.work_packet_activation_review_request_id
        ),
        "work_packet_activation_source_index_id": (summary.work_packet_activation_source_index_id),
        "work_packet_activation_non_execution_guardrail_id": (
            summary.work_packet_activation_non_execution_guardrail_id
        ),
        "work_packet_scope_contract_id": summary.work_packet_scope_contract_id,
        "implementation_target_surface_boundary_id": (
            summary.implementation_target_surface_boundary_id
        ),
        "work_packet_validation_evidence_plan_id": (
            summary.work_packet_validation_evidence_plan_id
        ),
        "work_packet_activation_exception_register_id": (
            summary.work_packet_activation_exception_register_id
        ),
        "review_id": summary.review_id,
        "snapshot_id": summary.snapshot_id,
        "source_set_id": summary.source_set_id,
        "handoff_rows": [
            {
                "handoff_ref": "post-activation-review-handoff:v84c:intent-to-spec-lock-review",
                "activation_package_ref": summary_row.activation_package_ref,
                "summary_refs": [summary_row.summary_ref],
                "activation_request_refs": summary_row.activation_request_refs,
                "scope_contract_refs": summary_row.scope_contract_refs,
                "target_boundary_refs": summary_row.target_boundary_refs,
                "validation_plan_refs": summary_row.validation_plan_refs,
                "carried_exception_refs": summary_row.carried_warning_refs,
                "candidate_ref": summary_row.candidate_ref,
                "source_refs": summary_row.source_refs,
                "handoff_target": "future_canonical_implementation_lock_review",
                "handoff_subject_horizon": "implementation_lock_review_package",
                "handoff_posture": "ready_with_nonblocking_warnings",
                "handoff_authority_horizon": "canonical_implementation_lock_review",
                "handoff_activation_status": "later_lock_review_requested",
                "implementation_lock_status": "no_implementation_lock_created_by_v84",
                "canonical_lock_requirement_refs": (summary_row.canonical_lock_requirement_refs),
                "required_later_authority_refs": summary_row.required_later_authority_refs,
                "activation_execution_posture": "no_activation_performed_by_v84",
                "work_packet_execution_posture": "no_work_packet_execution_performed_by_v84",
                "implementation_execution_posture": "no_implementation_performed_by_v84",
                "target_mutation_posture": "no_target_mutation_performed_by_v84",
                "pr_commit_release_posture": "no_pr_commit_merge_release_performed_by_v84",
                "guardrail_refs": summary_row.guardrail_refs,
                "limitation_note": (
                    "Handoff requests later review with no implementation, no activation, "
                    "and no implementation lock created."
                ),
            }
        ],
        "handoff_summary": (
            "V84-C handoffs request later review with no implementation, "
            "no activation, no target mutation, and no release."
        ),
    }
    payload["post_work_packet_activation_review_handoff_id"] = _surface_id(
        "repo_post_work_packet_activation_review_handoff",
        REPO_POST_WORK_PACKET_ACTIVATION_REVIEW_HANDOFF_SCHEMA,
        payload,
        "post_work_packet_activation_review_handoff_id",
    )
    return RepoPostWorkPacketActivationReviewHandoff.model_validate(payload)


def derive_v84c_repo_work_packet_activation_family_closeout_alignment(
    *,
    repo_root: Path | None = None,
    work_packet_activation_readiness_summary: (
        RepoWorkPacketActivationReadinessSummary | None
    ) = None,
    post_work_packet_activation_review_handoff: (
        RepoPostWorkPacketActivationReviewHandoff | None
    ) = None,
) -> RepoWorkPacketActivationFamilyCloseoutAlignment:
    summary = (
        work_packet_activation_readiness_summary
        or derive_v84c_repo_work_packet_activation_readiness_summary(repo_root=repo_root)
    )
    handoff = (
        post_work_packet_activation_review_handoff
        or derive_v84c_repo_post_work_packet_activation_review_handoff(
            repo_root=repo_root,
            work_packet_activation_readiness_summary=summary,
        )
    )
    payload = {
        "schema": REPO_WORK_PACKET_ACTIVATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
        "work_packet_activation_family_closeout_alignment_id": "",
        "work_packet_activation_readiness_summary_id": (
            summary.work_packet_activation_readiness_summary_id
        ),
        "post_work_packet_activation_review_handoff_id": (
            handoff.post_work_packet_activation_review_handoff_id
        ),
        "family": "V84",
        "closed_by_arc": "vNext+238",
        "closed_slice_ladder": ["V84-A", "V84-B", "V84-C"],
        "shipped_record_shapes": sorted(
            [
                REPO_WORK_PACKET_ACTIVATION_SOURCE_INDEX_SCHEMA,
                REPO_WORK_PACKET_ACTIVATION_REVIEW_REQUEST_SCHEMA,
                REPO_WORK_PACKET_ACTIVATION_NON_EXECUTION_GUARDRAIL_SCHEMA,
                REPO_WORK_PACKET_SCOPE_CONTRACT_SCHEMA,
                REPO_IMPLEMENTATION_TARGET_SURFACE_BOUNDARY_SCHEMA,
                REPO_WORK_PACKET_VALIDATION_EVIDENCE_PLAN_SCHEMA,
                REPO_WORK_PACKET_ACTIVATION_EXCEPTION_REGISTER_SCHEMA,
                REPO_WORK_PACKET_ACTIVATION_READINESS_SUMMARY_SCHEMA,
                REPO_POST_WORK_PACKET_ACTIVATION_REVIEW_HANDOFF_SCHEMA,
                REPO_WORK_PACKET_ACTIVATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
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
            "V84",
        ],
        "family_closed_on_main": "closed_after_v84c_merge",
        "future_family_authority": "next_selector_required",
        "unselected_future_surfaces": [
            "command_execution",
            "direct_oai_runtime_behavior",
            "graph_memory_authority",
            "implementation_execution",
            "implementation_lock_creation",
            "meta_orchestrator_runtime_transition",
            "morphic_ux_runtime_change",
            "pr_commit_merge_release",
            "product_authorization",
            "recursive_policy_amendment",
            "target_mutation",
            "tool_invocation",
            "v85_selection",
            "work_packet_activation",
            "work_packet_execution",
        ],
        "work_packet_activation_review_boundary": (
            "V84 closes work-packet activation review with no activation, "
            "no implementation, no implementation lock created, and no v85 selection."
        ),
        "limitation_note": (
            "V84 closes as review only with no activation, no implementation, "
            "no target mutation, no PR, no release, and no downstream authority."
        ),
    }
    payload["work_packet_activation_family_closeout_alignment_id"] = _surface_id(
        "repo_work_packet_activation_family_closeout_alignment",
        REPO_WORK_PACKET_ACTIVATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
        payload,
        "work_packet_activation_family_closeout_alignment_id",
    )
    return RepoWorkPacketActivationFamilyCloseoutAlignment.model_validate(payload)


def validate_v84c_work_packet_activation_closeout_bundle(
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
    work_packet_activation_non_execution_guardrail: (RepoWorkPacketActivationNonExecutionGuardrail),
    work_packet_scope_contract: RepoWorkPacketScopeContract,
    implementation_target_surface_boundary: RepoImplementationTargetSurfaceBoundary,
    work_packet_validation_evidence_plan: RepoWorkPacketValidationEvidencePlan,
    work_packet_activation_exception_register: RepoWorkPacketActivationExceptionRegister,
    work_packet_activation_readiness_summary: RepoWorkPacketActivationReadinessSummary,
    post_work_packet_activation_review_handoff: RepoPostWorkPacketActivationReviewHandoff,
    work_packet_activation_family_closeout_alignment: (
        RepoWorkPacketActivationFamilyCloseoutAlignment
    ),
) -> None:
    validate_v84b_work_packet_package_review_bundle(
        v83_intent_source_index=v83_intent_source_index,
        v83_semantic_intent_contract=v83_semantic_intent_contract,
        v83_intent_non_implementation_guardrail=v83_intent_non_implementation_guardrail,
        v83_intent_edge_decomposition=v83_intent_edge_decomposition,
        v83_artifact_obligation_map=v83_artifact_obligation_map,
        v83_semantic_drift_ambiguity_register=v83_semantic_drift_ambiguity_register,
        v83_implementation_spec_projection_packet=v83_implementation_spec_projection_packet,
        v83_intent_to_work_packet_handoff=v83_intent_to_work_packet_handoff,
        v83_semantic_implementation_spec_family_closeout_alignment=(
            v83_semantic_implementation_spec_family_closeout_alignment
        ),
        work_packet_activation_source_index=work_packet_activation_source_index,
        work_packet_activation_review_request=work_packet_activation_review_request,
        work_packet_activation_non_execution_guardrail=(
            work_packet_activation_non_execution_guardrail
        ),
        work_packet_scope_contract=work_packet_scope_contract,
        implementation_target_surface_boundary=implementation_target_surface_boundary,
        work_packet_validation_evidence_plan=work_packet_validation_evidence_plan,
        work_packet_activation_exception_register=work_packet_activation_exception_register,
    )
    expected_ids = (
        work_packet_activation_review_request.work_packet_activation_review_request_id,
        work_packet_activation_source_index.work_packet_activation_source_index_id,
        work_packet_activation_non_execution_guardrail.work_packet_activation_non_execution_guardrail_id,
        work_packet_scope_contract.work_packet_scope_contract_id,
        implementation_target_surface_boundary.implementation_target_surface_boundary_id,
        work_packet_validation_evidence_plan.work_packet_validation_evidence_plan_id,
        work_packet_activation_exception_register.work_packet_activation_exception_register_id,
    )
    if (
        work_packet_activation_readiness_summary.work_packet_activation_review_request_id,
        work_packet_activation_readiness_summary.work_packet_activation_source_index_id,
        work_packet_activation_readiness_summary.work_packet_activation_non_execution_guardrail_id,
        work_packet_activation_readiness_summary.work_packet_scope_contract_id,
        work_packet_activation_readiness_summary.implementation_target_surface_boundary_id,
        work_packet_activation_readiness_summary.work_packet_validation_evidence_plan_id,
        work_packet_activation_readiness_summary.work_packet_activation_exception_register_id,
    ) != expected_ids:
        raise ValueError("V84-C readiness summary must reference released V84-A/B surfaces")
    if (
        post_work_packet_activation_review_handoff.work_packet_activation_readiness_summary_id
        != work_packet_activation_readiness_summary.work_packet_activation_readiness_summary_id
    ):
        raise ValueError("V84-C handoff must reference released readiness summary")
    if (
        post_work_packet_activation_review_handoff.work_packet_activation_review_request_id,
        post_work_packet_activation_review_handoff.work_packet_activation_source_index_id,
        post_work_packet_activation_review_handoff.work_packet_activation_non_execution_guardrail_id,
        post_work_packet_activation_review_handoff.work_packet_scope_contract_id,
        post_work_packet_activation_review_handoff.implementation_target_surface_boundary_id,
        post_work_packet_activation_review_handoff.work_packet_validation_evidence_plan_id,
        post_work_packet_activation_review_handoff.work_packet_activation_exception_register_id,
    ) != expected_ids:
        raise ValueError("V84-C handoff must reference released V84-A/B surfaces")
    if (
        work_packet_activation_family_closeout_alignment.work_packet_activation_readiness_summary_id
        != work_packet_activation_readiness_summary.work_packet_activation_readiness_summary_id
        or (
            work_packet_activation_family_closeout_alignment
            .post_work_packet_activation_review_handoff_id
        )
        != post_work_packet_activation_review_handoff.post_work_packet_activation_review_handoff_id
    ):
        raise ValueError("V84-C closeout must reference released summary and handoff")

    request_rows = {
        row.activation_request_ref: row
        for row in work_packet_activation_review_request.activation_request_rows
    }
    guardrail_rows = {
        row.guardrail_ref: row
        for row in work_packet_activation_non_execution_guardrail.guardrail_rows
    }
    scope_rows = {
        row.scope_contract_ref: row for row in work_packet_scope_contract.scope_contract_rows
    }
    target_rows = {
        row.target_boundary_ref: row
        for row in implementation_target_surface_boundary.target_boundary_rows
    }
    validation_rows = {
        row.validation_plan_ref: row
        for row in work_packet_validation_evidence_plan.validation_plan_rows
    }
    exception_register_rows = {
        row.exception_register_ref: row
        for row in work_packet_activation_exception_register.exception_register_rows
    }
    exception_rows = {
        exception.exception_ref: exception
        for register in exception_register_rows.values()
        for exception in register.exception_rows
    }
    summary_rows = {
        row.summary_ref: row for row in work_packet_activation_readiness_summary.summary_rows
    }
    known_projection_packets = {
        row.projection_packet_ref
        for row in v83_implementation_spec_projection_packet.projection_packet_rows
    }
    known_quality_gates = {
        gate.quality_gate_ref
        for packet in v83_implementation_spec_projection_packet.projection_packet_rows
        for gate in packet.implementation_spec_quality_gate_rows
    }

    def _require_known_refs(refs: list[str], known: set[str], message: str) -> None:
        if any(ref not in known for ref in refs):
            raise ValueError(message)

    def _require_row_identity(
        refs: list[str],
        rows_by_ref: dict[str, _CartographyBase],
        *,
        activation_package_ref: str,
        candidate_ref: str,
        message: str,
    ) -> None:
        for ref in refs:
            row = rows_by_ref[ref]
            if (
                row.activation_package_ref != activation_package_ref
                or row.candidate_ref != candidate_ref
            ):
                raise ValueError(message)

    for row in work_packet_activation_readiness_summary.summary_rows:
        _require_known_refs(
            row.activation_request_refs, set(request_rows), "summary request refs must be known"
        )
        _require_known_refs(
            row.scope_contract_refs, set(scope_rows), "summary scope refs must be known"
        )
        _require_known_refs(
            row.target_boundary_refs, set(target_rows), "summary target refs must be known"
        )
        _require_known_refs(
            row.validation_plan_refs, set(validation_rows), "summary validation refs must be known"
        )
        _require_known_refs(
            row.exception_register_refs,
            set(exception_register_rows),
            "summary exception register refs must be known",
        )
        _require_known_refs(
            row.carried_blocker_refs, set(exception_rows), "summary blocker refs must be known"
        )
        _require_known_refs(
            row.carried_warning_refs, set(exception_rows), "summary warning refs must be known"
        )
        _require_known_refs(
            row.guardrail_refs, set(guardrail_rows), "summary guardrail refs must be known"
        )
        _require_known_refs(
            row.projection_packet_refs,
            known_projection_packets,
            "summary projection refs must be released V83-C refs",
        )
        _require_known_refs(
            row.quality_gate_refs,
            known_quality_gates,
            "summary quality gate refs must be released V83-C refs",
        )
        _require_row_identity(
            row.scope_contract_refs,
            scope_rows,
            activation_package_ref=row.activation_package_ref,
            candidate_ref=row.candidate_ref,
            message="summary scope refs must match activation package and candidate",
        )
        _require_row_identity(
            row.target_boundary_refs,
            target_rows,
            activation_package_ref=row.activation_package_ref,
            candidate_ref=row.candidate_ref,
            message="summary target refs must match activation package and candidate",
        )
        _require_row_identity(
            row.validation_plan_refs,
            validation_rows,
            activation_package_ref=row.activation_package_ref,
            candidate_ref=row.candidate_ref,
            message="summary validation refs must match activation package and candidate",
        )
        _require_row_identity(
            row.exception_register_refs,
            exception_register_rows,
            activation_package_ref=row.activation_package_ref,
            candidate_ref=row.candidate_ref,
            message="summary exception refs must match activation package and candidate",
        )
        for request_ref in row.activation_request_refs:
            request_row = request_rows[request_ref]
            if (
                request_row.activation_package_ref != row.activation_package_ref
                or request_row.candidate_ref != row.candidate_ref
            ):
                raise ValueError("summary request refs must match activation package and candidate")
        for guardrail_ref in row.guardrail_refs:
            guardrail_row = guardrail_rows[guardrail_ref]
            if (
                guardrail_row.activation_package_ref != row.activation_package_ref
                or guardrail_row.candidate_ref != row.candidate_ref
            ):
                raise ValueError(
                    "summary guardrail refs must match activation package and candidate"
                )
        blocking_refs = {
            ref
            for ref in row.carried_blocker_refs
            if exception_rows[ref].blocking_posture == "blocking"
        }
        if (
            row.summary_posture
            in {
                "ready_for_later_implementation_lock_review",
                "ready_with_nonblocking_warnings",
            }
            and blocking_refs
        ):
            raise ValueError("ready summaries cannot hide blocking exceptions")
        for warning_ref in row.carried_warning_refs:
            warning = exception_rows[warning_ref]
            if warning.blocking_posture != "warning":
                raise ValueError("carried warning refs must point to warnings")
            if warning.exception_kind in _V84C_BLOCKING_WARNING_KINDS:
                raise ValueError("warning-ready summaries cannot carry blocker-grade warnings")
        for validation_ref in row.validation_plan_refs:
            validation_row = validation_rows[validation_ref]
            covered_edges = {
                ref
                for matrix_row in validation_row.validation_matrix_rows
                for ref in matrix_row.semantic_edge_refs
            }
            if not set(validation_row.semantic_edge_refs).issubset(covered_edges):
                raise ValueError("summary validation plan is not edge complete")
            covered_obligations = {
                ref
                for matrix_row in validation_row.validation_matrix_rows
                for ref in matrix_row.artifact_obligation_refs
            }
            if not set(validation_row.artifact_obligation_refs).issubset(covered_obligations):
                raise ValueError("summary validation plan is not obligation complete")
            known_matrix_refs = {
                r.validation_matrix_ref for r in validation_row.validation_matrix_rows
            }
            if not set(row.coverage_summary_refs).issubset(known_matrix_refs):
                raise ValueError("summary coverage refs must resolve to validation matrix rows")
        for scope_ref in row.scope_contract_refs:
            scope = scope_rows[scope_ref]
            if not set(row.canonical_lock_requirement_refs).issubset(
                set(scope.canonical_lock_requirement_refs)
            ):
                raise ValueError("summary canonical lock refs must resolve to scope rows")
        if row.summary_posture in {
            "ready_for_later_implementation_lock_review",
            "ready_with_nonblocking_warnings",
        }:
            if row.coverage_posture != "edge_and_obligation_complete_for_review":
                raise ValueError("ready summaries require complete coverage posture")
            if not row.canonical_lock_requirement_refs:
                raise ValueError("ready summaries require canonical lock refs")

    for row in post_work_packet_activation_review_handoff.handoff_rows:
        _require_known_refs(
            row.summary_refs, set(summary_rows), "handoff summary refs must be known"
        )
        _require_known_refs(
            row.activation_request_refs, set(request_rows), "handoff request refs must be known"
        )
        _require_known_refs(
            row.scope_contract_refs, set(scope_rows), "handoff scope refs must be known"
        )
        _require_known_refs(
            row.target_boundary_refs, set(target_rows), "handoff target refs must be known"
        )
        _require_known_refs(
            row.validation_plan_refs, set(validation_rows), "handoff validation refs must be known"
        )
        _require_known_refs(
            row.carried_exception_refs, set(exception_rows), "handoff exception refs must be known"
        )
        _require_known_refs(
            row.guardrail_refs, set(guardrail_rows), "handoff guardrail refs must be known"
        )
        _require_row_identity(
            row.scope_contract_refs,
            scope_rows,
            activation_package_ref=row.activation_package_ref,
            candidate_ref=row.candidate_ref,
            message="handoff scope refs must match activation package and candidate",
        )
        for summary_ref in row.summary_refs:
            summary_row = summary_rows[summary_ref]
            if (
                summary_row.activation_package_ref != row.activation_package_ref
                or summary_row.candidate_ref != row.candidate_ref
            ):
                raise ValueError("handoff summary refs must match activation package and candidate")
            if not set(row.carried_exception_refs).issubset(
                set(summary_row.carried_blocker_refs) | set(summary_row.carried_warning_refs)
            ):
                raise ValueError("handoff carried exceptions must be visible in summaries")
        if row.handoff_target == "future_canonical_implementation_lock_review":
            if not row.canonical_lock_requirement_refs:
                raise ValueError("canonical implementation handoffs require lock refs")
            if set(row.canonical_lock_requirement_refs) != set(row.required_later_authority_refs):
                raise ValueError("canonical handoff authority refs must equal lock refs")
        if row.handoff_posture == "ready_with_nonblocking_warnings":
            for exception_ref in row.carried_exception_refs:
                exception = exception_rows[exception_ref]
                if exception.blocking_posture != "warning":
                    raise ValueError("warning-ready handoffs may carry warnings only")


def derive_v84c_work_packet_activation_closeout_bundle(
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
    RepoWorkPacketScopeContract,
    RepoImplementationTargetSurfaceBoundary,
    RepoWorkPacketValidationEvidencePlan,
    RepoWorkPacketActivationExceptionRegister,
    RepoWorkPacketActivationReadinessSummary,
    RepoPostWorkPacketActivationReviewHandoff,
    RepoWorkPacketActivationFamilyCloseoutAlignment,
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
        source_index,
        request,
        guardrail,
        scope_contract,
        target_boundary,
        validation_plan,
        exception_register,
    ) = _v84b_released_bundle(repo_root=repo_root)
    readiness_summary = derive_v84c_repo_work_packet_activation_readiness_summary(
        repo_root=repo_root,
        work_packet_activation_source_index=source_index,
        work_packet_activation_review_request=request,
        work_packet_activation_non_execution_guardrail=guardrail,
        work_packet_scope_contract=scope_contract,
        implementation_target_surface_boundary=target_boundary,
        work_packet_validation_evidence_plan=validation_plan,
        work_packet_activation_exception_register=exception_register,
    )
    handoff = derive_v84c_repo_post_work_packet_activation_review_handoff(
        repo_root=repo_root,
        work_packet_activation_readiness_summary=readiness_summary,
    )
    closeout = derive_v84c_repo_work_packet_activation_family_closeout_alignment(
        repo_root=repo_root,
        work_packet_activation_readiness_summary=readiness_summary,
        post_work_packet_activation_review_handoff=handoff,
    )
    validate_v84c_work_packet_activation_closeout_bundle(
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
        work_packet_scope_contract=scope_contract,
        implementation_target_surface_boundary=target_boundary,
        work_packet_validation_evidence_plan=validation_plan,
        work_packet_activation_exception_register=exception_register,
        work_packet_activation_readiness_summary=readiness_summary,
        post_work_packet_activation_review_handoff=handoff,
        work_packet_activation_family_closeout_alignment=closeout,
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
        scope_contract,
        target_boundary,
        validation_plan,
        exception_register,
        readiness_summary,
        handoff,
        closeout,
    )
