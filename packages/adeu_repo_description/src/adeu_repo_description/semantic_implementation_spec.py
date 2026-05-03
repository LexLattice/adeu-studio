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
REPO_INTENT_NON_IMPLEMENTATION_GUARDRAIL_SCHEMA = (
    "repo_intent_non_implementation_guardrail@1"
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
        if (
            self.intent_source_role in _SUPPORT_ONLY_SOURCE_ROLES
            and self.authority_layer == "lock"
        ):
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
    forbidden_downstream_authority: list[ForbiddenSemanticDownstreamAuthority] = Field(
        min_length=1
    )
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
            raise ValueError(
                "intent_non_implementation_guardrail_id does not match canonical hash"
            )
        return self


def derive_v83a_repo_intent_source_index(
    *, repo_root: Path | None = None
) -> RepoIntentSourceIndex:
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
        row.source_ref: row.model_agent_authority_posture
        for row in intent_source_index.source_rows
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
