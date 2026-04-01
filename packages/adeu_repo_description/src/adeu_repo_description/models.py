from __future__ import annotations

import re
from copy import deepcopy
from pathlib import PurePosixPath
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import canonical_json, sha256_canonical_json

REPO_SCHEMA_FAMILY_REGISTRY_SCHEMA = "repo_schema_family_registry@1"
REPO_ENTITY_CATALOG_SCHEMA = "repo_entity_catalog@1"
REPO_SYMBOL_CATALOG_SCHEMA = "repo_symbol_catalog@1"
REPO_DEPENDENCY_GRAPH_SCHEMA = "repo_dependency_graph@1"
REPO_TEST_INTENT_MATRIX_SCHEMA = "repo_test_intent_matrix@1"
REPO_OPTIMIZATION_REGISTER_SCHEMA = "repo_optimization_register@1"
REPO_ARC_DEPENDENCY_REGISTER_V1_SCHEMA = "repo_arc_dependency_register@1"
REPO_ARC_DEPENDENCY_REGISTER_SCHEMA = "repo_arc_dependency_register@2"
V45A_V99_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS99.md#v99-continuation-contract-machine-checkable"
)
V45A_CLASSIFICATION_POLICY_REF = (
    "docs/DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md#v45a-role-form-classification-policy"
)
V45B_V101_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS101.md#v101-continuation-contract-machine-checkable"
)
V45C_V100_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS100.md#v100-continuation-contract-machine-checkable"
)
V45C_V102_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS102.md#v102-continuation-contract-machine-checkable"
)
V45D_V103_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS103.md#v103-continuation-contract-machine-checkable"
)
V45E_V104_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS104.md#v104-continuation-contract-machine-checkable"
)
V45C_DEPENDENCY_POLICY_REF = (
    "docs/DRAFT_V45_REPO_SELF_DESCRIPTION_DECOMPOSITION_v0.md"
    "#v45c-open-arc-dependency-register-policy"
)
RECONSTRUCTION_EQUIVALENCE_MODE = "canonical_normalized_semantic_equivalence"
SCHEMA_VISIBLE_ENTITY_COVERAGE_MODE = "bounded_schema_visible_slice"
_RECONSTRUCTION_REPRESENTATIVE_SCHEMA_KEYS: tuple[str, ...] = (
    "adeu_arc_task_packet",
    "adeu_architecture_analysis_request",
    "meta_loop_sequence_contract",
    "ux_interaction_contract",
    "adeu_core_ir",
    "policy_registry",
    "adeu.validator_result",
)

ClassificationPosture = Literal[
    "observed",
    "derived_deterministically",
    "inferred_heuristically",
    "adjudicated",
    "settled",
]
ClassificationMethod = Literal[
    "structural_signature",
    "semantic_function",
    "governance_role",
    "lexical_naming",
    "adjudicated_policy",
]
SymbolKind = Literal["module", "class", "function", "method", "attribute"]
SymbolRoleClassificationMethod = Literal[
    "ast_signature",
    "decorator_or_baseclass_rule",
    "bounded_inference_rule",
    "adjudicated_policy",
]
TestKind = Literal["pytest_function", "pytest_method"]
InvariantDomain = Literal["ontology", "epistemics", "deontics", "utility", "mixed"]
GatingPosture = Literal["release_gating", "advisory", "informational"]
TestIntentDerivationMethod = Literal[
    "assertion_ast",
    "fixture_or_helper_binding",
    "test_name_convention",
    "bounded_inference_rule",
    "adjudicated_policy",
]
ConfidencePosture = Literal["low", "medium", "high", "adjudicated", "settled"]
GuardedSurfaceRefKind = Literal[
    "internal_symbol",
    "internal_module_boundary",
    "external_boundary",
]
AssertionSurfaceKind = Literal[
    "assert_statement",
    "pytest_raises",
    "equality_assertion",
    "predicate_call_assertion",
    "response_or_status_assertion",
]
CompressionAxis = Literal[
    "structural_compression",
    "semantic_compression",
    "governance_compression",
    "surface_compression",
]
OptimizationPosture = Literal[
    "hotspot",
    "consolidation_candidate",
    "justified_monolith",
    "temporary_concentration",
    "forbidden_drift_zone",
]
SupportBasis = Literal[
    "duplicate_abstraction_signal",
    "repeated_law_expression",
    "cross_surface_invariant_restated",
    "long_file_or_concentrated_surface",
    "test_and_dependency_concentration",
]
PriorityPosture = Literal["informational_only", "planning_candidate", "adjudication_required"]
AmendmentEntitlement = Literal["not_authorized_by_this_artifact"]
OptimizationDerivationMethod = Literal[
    "descriptive_projection",
    "bounded_signal_rule",
    "cross_artifact_join",
    "adjudicated_policy",
]
FindingScopeKind = Literal[
    "file_surface",
    "module_surface",
    "schema_surface",
    "test_surface",
    "cross_surface_cluster",
]
ClusterMemberRefKind = Literal[
    "file_surface",
    "module_surface",
    "schema_surface",
    "test_surface",
]
SnapshotValidityPosture = Literal["snapshot_bound_current", "snapshot_bound_historical"]
PrimaryCarrierClass = Literal[
    "IntakeFrame",
    "TraceRecord",
    "CuratedSet",
    "Adjudication",
    "ContractGate",
    "StructuralModel",
]
EvidenceKind = Literal[
    "observed_anchor_tuple_evidence",
    "structural_signature_evidence",
    "semantic_function_cue_evidence",
    "governance_cue_evidence",
    "lexical_cue_evidence",
    "adjudication_artifact_evidence",
    "reconstruction_subset_evidence",
    "planning_table_row_evidence",
    "planning_selection_evidence",
    "lock_contract_evidence",
    "dependency_policy_evidence",
]
EntityCoverageMode = Literal["bounded_schema_visible_slice"]
ReconstructionEquivalenceMode = Literal["canonical_normalized_semantic_equivalence"]
ArcPhaseStatus = Literal[
    "planned",
    "planned_not_selected_yet",
    "planned_later_not_selected_here",
    "selected_next_branch_local",
    "locked_start_bundle",
    "closed_on_main",
]
AuthorityLayer = Literal["planning", "lock", "closeout", "support"]
ReadinessPosture = Literal["ready", "blocked", "deferred"]
DependencyKind = Literal["family_progression", "descriptive_prerequisite"]
DependencyStrength = Literal["hard", "soft"]
DependencyStatus = Literal["resolved", "unresolved", "informational"]
DependencyRegisterMethod = Literal[
    "direct_source_parse",
    "deterministic_projection",
    "bounded_inference_rule",
    "adjudicated_policy",
]
DependencyGraphKind = Literal["module_import", "symbol_reference", "inheritance"]
DependencyGraphPosture = Literal[
    "internal_resolved",
    "boundary_external",
    "boundary_out_of_scope",
]
DependencyGraphMethod = Literal[
    "ast_parse",
    "deterministic_projection",
    "bounded_inference_rule",
    "adjudicated_policy",
]
EndpointKind = Literal["internal_symbol", "internal_module_boundary", "external_dependency"]
CyclePosture = Literal["cycles_forbidden", "cycles_present_with_explicit_binding"]
CycleDetectionScope = Literal["hard_unresolved_edges_only", "all_declared_edges"]
PendingListPosture = Literal["machine_enforced_open_arc_register"]

_STRONGER_PRECEDENCE_EVIDENCE_KINDS: tuple[EvidenceKind, ...] = (
    "structural_signature_evidence",
    "semantic_function_cue_evidence",
    "governance_cue_evidence",
)
_FORBIDDEN_AUTHORITY_TERMS: tuple[str, ...] = (
    "scheduler_authority",
    "scheduling_entitlement",
    "mutation_entitlement",
    "automatic_priority",
    "planning_resolution_authority",
)
_FORBIDDEN_V45B_GRAPH_SCOPE_TERMS: tuple[str, ...] = (
    "refactor_entitlement",
    "automatic_refactor",
    "automatic_refactor_entitlement",
)
_FORBIDDEN_V45D_MATRIX_SCOPE_TERMS: tuple[str, ...] = (
    "optimization_entitlement",
    "automatic_release_gating",
    "automatic_release_authority",
    "automatic_merge_block",
)
_FORBIDDEN_V45E_REGISTER_SCOPE_TERMS: tuple[str, ...] = (
    "refactor_entitlement",
    "automatic_refactor",
    "automatic_release_gating",
    "automatic_release_authority",
    "automatic_priority",
    "priority_entitlement",
)


def _v45a_classification_policy_payload() -> dict[str, Any]:
    return {
        "policy_ref": V45A_CLASSIFICATION_POLICY_REF,
        "precedence_order": [
            "structural_signature",
            "semantic_function",
            "governance_role",
            "lexical_naming",
        ],
        "coverage_mode": SCHEMA_VISIBLE_ENTITY_COVERAGE_MODE,
        "allowed_postures": [
            "observed",
            "derived_deterministically",
            "inferred_heuristically",
            "adjudicated",
            "settled",
        ],
        "allowed_methods": [
            "structural_signature",
            "semantic_function",
            "governance_role",
            "lexical_naming",
            "adjudicated_policy",
        ],
        "allowed_evidence_kinds": [
            "observed_anchor_tuple_evidence",
            "structural_signature_evidence",
            "semantic_function_cue_evidence",
            "governance_cue_evidence",
            "lexical_cue_evidence",
            "adjudication_artifact_evidence",
            "reconstruction_subset_evidence",
        ],
    }


def compute_v45a_classification_policy_hash() -> str:
    return sha256_canonical_json(_v45a_classification_policy_payload())


def _v45c_v100_dependency_policy_payload() -> dict[str, Any]:
    return {
        "policy_ref": V45C_DEPENDENCY_POLICY_REF,
        "allowed_phase_statuses": [
            "planned",
            "planned_not_selected_yet",
            "planned_later_not_selected_here",
            "selected_next_branch_local",
            "locked_start_bundle",
            "closed_on_main",
        ],
        "allowed_authority_layers": ["planning", "lock", "closeout", "support"],
        "allowed_readiness_postures": ["ready", "blocked", "deferred"],
        "allowed_dependency_kinds": ["family_progression", "descriptive_prerequisite"],
        "allowed_dependency_strengths": ["hard", "soft"],
        "allowed_dependency_statuses": ["resolved", "unresolved", "informational"],
        "cycle_policy": "reject_unflagged_cycles",
        "blocked_posture_rule": "blocked_entries_must_match_unresolved_hard_incoming_edges",
        "forbidden_authority_terms": list(_FORBIDDEN_AUTHORITY_TERMS),
    }


def compute_v45c_v100_dependency_policy_hash() -> str:
    return sha256_canonical_json(_v45c_v100_dependency_policy_payload())


def _v45c_v102_dependency_policy_payload() -> dict[str, Any]:
    return {
        "policy_ref": V45C_DEPENDENCY_POLICY_REF,
        "allowed_phase_statuses": [
            "planned",
            "planned_not_selected_yet",
            "planned_later_not_selected_here",
            "selected_next_branch_local",
            "locked_start_bundle",
            "closed_on_main",
        ],
        "allowed_authority_layers": ["planning", "lock", "closeout", "support"],
        "allowed_readiness_postures": ["ready", "blocked", "deferred"],
        "allowed_dependency_kinds": ["family_progression", "descriptive_prerequisite"],
        "allowed_dependency_strengths": ["hard", "soft"],
        "allowed_dependency_statuses": ["resolved", "unresolved", "informational"],
        "allowed_postures": [
            "observed",
            "derived_deterministically",
            "inferred_heuristically",
            "adjudicated",
            "settled",
        ],
        "allowed_methods": [
            "direct_source_parse",
            "deterministic_projection",
            "bounded_inference_rule",
            "adjudicated_policy",
        ],
        "allowed_cycle_postures": [
            "cycles_forbidden",
            "cycles_present_with_explicit_binding",
        ],
        "allowed_cycle_detection_scopes": [
            "hard_unresolved_edges_only",
            "all_declared_edges",
        ],
        "allowed_pending_list_postures": [
            "machine_enforced_open_arc_register",
        ],
        "source_artifact_membership_rule": (
            "entry_and_edge_source_artifact_refs_must_resolve_inside_source_set"
        ),
        "blocked_posture_rule": "blocked_entries_must_match_unresolved_hard_incoming_edges",
        "cycle_policy": "explicit_cycle_posture_and_scope_required",
        "forbidden_authority_terms": list(_FORBIDDEN_AUTHORITY_TERMS),
        "forbidden_undefined_vocabulary": ["supports_all_three_way_claim"],
    }


def compute_v45c_v102_dependency_policy_hash() -> str:
    return sha256_canonical_json(_v45c_v102_dependency_policy_payload())


def _assert_non_empty_text(value: str, *, field_name: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{field_name} must be a string")
    normalized = value.strip()
    if not normalized:
        raise ValueError(f"{field_name} must not be empty")
    return normalized


def _assert_repo_rel_path(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name).replace("\\", "/")
    if normalized.startswith("/"):
        raise ValueError(f"{field_name} must be repository-relative")
    if ".." in PurePosixPath(normalized).parts:
        raise ValueError(f"{field_name} must not include parent traversal")
    return str(PurePosixPath(normalized))


def _assert_hash(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    if len(normalized) != 64:
        raise ValueError(f"{field_name} must be a 64-character lowercase hex digest")
    for ch in normalized:
        if ch not in "0123456789abcdef":
            raise ValueError(f"{field_name} must be a 64-character lowercase hex digest")
    return normalized


def _assert_sorted_unique(values: list[str], *, field_name: str) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must not contain duplicates")
    if normalized != sorted(normalized):
        raise ValueError(f"{field_name} must be sorted lexicographically")
    return normalized


def _normalize_for_equality(value: str) -> str:
    lowered = value.lower()
    return re.sub(r"[^a-z0-9]+", "_", lowered).strip("_")


def _assert_no_forbidden_authority_terms(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    normalized_tokens = _normalize_for_equality(normalized)
    for forbidden_term in _FORBIDDEN_AUTHORITY_TERMS:
        if _normalize_for_equality(forbidden_term) in normalized_tokens:
            raise ValueError(
                f"{field_name} may not carry scheduling or mutation entitlement claims"
            )
    return normalized


def _assert_no_forbidden_v45b_graph_scope_terms(value: str, *, field_name: str) -> str:
    normalized = _assert_no_forbidden_authority_terms(value, field_name=field_name)
    normalized_tokens = _normalize_for_equality(normalized)
    for forbidden_term in _FORBIDDEN_V45B_GRAPH_SCOPE_TERMS:
        if _normalize_for_equality(forbidden_term) in normalized_tokens:
            raise ValueError(
                f"{field_name} may not carry refactor, scheduling, or mutation entitlement claims"
            )
    return normalized


def _assert_no_forbidden_v45d_matrix_scope_terms(value: str, *, field_name: str) -> str:
    normalized = _assert_no_forbidden_authority_terms(value, field_name=field_name)
    normalized_tokens = _normalize_for_equality(normalized)
    for forbidden_term in _FORBIDDEN_V45D_MATRIX_SCOPE_TERMS:
        if _normalize_for_equality(forbidden_term) in normalized_tokens:
            raise ValueError(
                f"{field_name} may not carry release-gating, optimization, scheduling, or "
                "mutation entitlement claims"
            )
    return normalized


def _assert_no_forbidden_v45e_register_scope_terms(value: str, *, field_name: str) -> str:
    normalized = _assert_no_forbidden_authority_terms(value, field_name=field_name)
    normalized_tokens = _normalize_for_equality(normalized)
    for forbidden_term in _FORBIDDEN_V45E_REGISTER_SCOPE_TERMS:
        if _normalize_for_equality(forbidden_term) in normalized_tokens:
            raise ValueError(
                f"{field_name} may not carry refactor, release-gating, priority, scheduling, "
                "or mutation entitlement claims"
            )
    return normalized


def compute_symbol_id(*, module_path: str, qualname: str, symbol_kind: SymbolKind) -> str:
    normalized_module_path = _assert_repo_rel_path(module_path, field_name="module_path")
    normalized_qualname = _assert_non_empty_text(qualname, field_name="qualname")
    return f"symbol:{normalized_module_path}:{normalized_qualname}:{symbol_kind}"


def compute_internal_module_boundary_ref(*, module_path: str) -> str:
    normalized_module_path = _assert_repo_rel_path(module_path, field_name="module_path")
    return f"module:{normalized_module_path}"


def compute_repo_test_ref(*, source_path: str, qualname: str) -> str:
    normalized_source_path = _assert_repo_rel_path(source_path, field_name="source_path")
    normalized_qualname = _assert_non_empty_text(qualname, field_name="qualname")
    return f"test:{normalized_source_path}#{normalized_qualname}"


def compute_claimed_invariant_binding_id(*, binding_statement: str) -> str:
    payload = {
        "binding_statement": _assert_non_empty_text(
            binding_statement, field_name="binding_statement"
        ),
    }
    digest = sha256_canonical_json(payload)
    return f"binding_{digest[:24]}"


def _assert_test_ref(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    prefix = "test:"
    if not normalized.startswith(prefix):
        raise ValueError(f"{field_name} must use the test: prefix")
    remainder = normalized[len(prefix) :]
    if "#" not in remainder:
        raise ValueError(f"{field_name} must include a #qualified-name suffix")
    source_path, qualname = remainder.split("#", 1)
    _assert_repo_rel_path(source_path, field_name=field_name)
    _assert_non_empty_text(qualname, field_name=field_name)
    return f"{prefix}{source_path}#{qualname}"


def _test_source_path_from_test_ref(test_ref: str) -> str:
    normalized = _assert_test_ref(test_ref, field_name="test_ref")
    return normalized[len("test:") :].split("#", 1)[0]


def _assert_assertion_source_ref(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    prefix = "assertion:"
    if not normalized.startswith(prefix):
        raise ValueError(f"{field_name} must use the assertion: prefix")
    remainder = normalized[len(prefix) :]
    if "#L" not in remainder:
        raise ValueError(f"{field_name} must include a #L<line> suffix")
    source_path, line_suffix = remainder.split("#L", 1)
    _assert_repo_rel_path(source_path, field_name=field_name)
    if not line_suffix.isdigit():
        raise ValueError(f"{field_name} line suffix must be numeric")
    return f"{prefix}{source_path}#L{line_suffix}"


def _assert_guarded_surface_ref(
    value: str,
    *,
    field_name: str,
    guarded_surface_ref_kind: GuardedSurfaceRefKind,
) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    if guarded_surface_ref_kind == "internal_symbol":
        if not normalized.startswith("symbol:"):
            raise ValueError(f"{field_name} must use the symbol: prefix")
        return normalized
    if guarded_surface_ref_kind == "internal_module_boundary":
        return _assert_internal_module_boundary_ref(normalized, field_name=field_name)
    if guarded_surface_ref_kind == "external_boundary":
        if normalized.startswith("external:") or normalized.startswith("out_of_scope:"):
            return normalized
        raise ValueError(
            f"{field_name} must use the external: or out_of_scope: prefix for external_boundary"
        )
    raise ValueError(f"unsupported guarded_surface_ref_kind: {guarded_surface_ref_kind}")


def _assert_internal_module_boundary_ref(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    prefix = "module:"
    if not normalized.startswith(prefix):
        raise ValueError(f"{field_name} must use the module: prefix")
    module_path = normalized[len(prefix) :]
    _assert_repo_rel_path(module_path, field_name=field_name)
    return f"{prefix}{module_path}"


def _assert_external_dependency_ref(
    value: str,
    *,
    field_name: str,
    dependency_posture: DependencyGraphPosture,
) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    required_prefix = "external:" if dependency_posture == "boundary_external" else "out_of_scope:"
    if not normalized.startswith(required_prefix):
        raise ValueError(
            f"{field_name} must use the {required_prefix} prefix "
            "for the declared dependency_posture"
        )
    suffix = normalized[len(required_prefix) :]
    if not suffix.strip():
        raise ValueError(f"{field_name} must not be empty after the prefix")
    return normalized


def _assert_finding_scope_ref(
    value: str,
    *,
    field_name: str,
    finding_scope_kind: FindingScopeKind,
) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    if finding_scope_kind in {"file_surface", "schema_surface", "test_surface"}:
        return _assert_repo_rel_path(normalized, field_name=field_name)
    if finding_scope_kind == "module_surface":
        return _assert_internal_module_boundary_ref(normalized, field_name=field_name)
    if finding_scope_kind == "cross_surface_cluster":
        if not normalized.startswith("cluster:"):
            raise ValueError(f"{field_name} must use the cluster: prefix")
        cluster_name = normalized[len("cluster:") :]
        if not cluster_name.strip():
            raise ValueError(f"{field_name} must not be empty after the cluster: prefix")
        return normalized
    raise ValueError(f"unsupported finding_scope_kind: {finding_scope_kind}")


def _assert_cluster_member_ref(
    value: str,
    *,
    field_name: str,
    member_ref_kind: ClusterMemberRefKind,
) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    if member_ref_kind in {"file_surface", "schema_surface", "test_surface"}:
        return _assert_repo_rel_path(normalized, field_name=field_name)
    if member_ref_kind == "module_surface":
        return _assert_internal_module_boundary_ref(normalized, field_name=field_name)
    raise ValueError(f"unsupported member_ref_kind: {member_ref_kind}")


class RepoDescriptionEvidenceRef(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    evidence_ref: str
    evidence_kind: EvidenceKind

    @model_validator(mode="after")
    def _validate_entry(self) -> RepoDescriptionEvidenceRef:
        object.__setattr__(
            self,
            "evidence_ref",
            _assert_non_empty_text(self.evidence_ref, field_name="evidence_ref"),
        )
        return self


class RepoSourceSet(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    source_paths: list[str] = Field(min_length=1)
    source_set_hash: str

    @model_validator(mode="after")
    def _validate_source_set(self) -> RepoSourceSet:
        object.__setattr__(
            self,
            "source_paths",
            _assert_sorted_unique(
                [
                    _assert_repo_rel_path(path, field_name="source_paths")
                    for path in self.source_paths
                ],
                field_name="source_paths",
            ),
        )
        object.__setattr__(
            self,
            "source_set_hash",
            _assert_hash(self.source_set_hash, field_name="source_set_hash"),
        )
        return self


class RepoSchemaReconstructionRow(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema_key: str
    source_schema_definition: dict[str, Any]
    reconstructed_schema_definition: dict[str, Any]
    evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_row(self) -> RepoSchemaReconstructionRow:
        object.__setattr__(
            self, "schema_key", _assert_non_empty_text(self.schema_key, field_name="schema_key")
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _assert_sorted_unique(self.evidence_refs, field_name="reconstruction.evidence_refs"),
        )
        return self


class RepoSchemaFamilyRegistryEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    schema_key: str
    schema_path: str
    schema_discriminator: str
    family_cluster: str
    primary_carrier_class: PrimaryCarrierClass
    secondary_role_form_tags: list[str] = Field(default_factory=list)
    lineage_overlay: str
    core_envelope_features: list[str] = Field(default_factory=list)
    residual_flags: list[str] = Field(default_factory=list)
    classification_posture: ClassificationPosture
    classification_method: ClassificationMethod
    adjudicator_ref: str | None = None
    supporting_evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_entry(self) -> RepoSchemaFamilyRegistryEntry:
        object.__setattr__(
            self, "schema_key", _assert_non_empty_text(self.schema_key, field_name="schema_key")
        )
        object.__setattr__(
            self,
            "schema_path",
            _assert_repo_rel_path(self.schema_path, field_name="schema_path"),
        )
        object.__setattr__(
            self,
            "schema_discriminator",
            _assert_non_empty_text(self.schema_discriminator, field_name="schema_discriminator"),
        )
        object.__setattr__(
            self,
            "family_cluster",
            _assert_non_empty_text(self.family_cluster, field_name="family_cluster"),
        )
        object.__setattr__(
            self,
            "lineage_overlay",
            _assert_non_empty_text(self.lineage_overlay, field_name="lineage_overlay"),
        )
        object.__setattr__(
            self,
            "secondary_role_form_tags",
            _assert_sorted_unique(
                self.secondary_role_form_tags, field_name="secondary_role_form_tags"
            ),
        )
        object.__setattr__(
            self,
            "core_envelope_features",
            _assert_sorted_unique(self.core_envelope_features, field_name="core_envelope_features"),
        )
        object.__setattr__(
            self,
            "residual_flags",
            _assert_sorted_unique(self.residual_flags, field_name="residual_flags"),
        )
        object.__setattr__(
            self,
            "supporting_evidence_refs",
            _assert_sorted_unique(
                self.supporting_evidence_refs, field_name="supporting_evidence_refs"
            ),
        )
        if self.adjudicator_ref is not None:
            object.__setattr__(
                self,
                "adjudicator_ref",
                _assert_non_empty_text(self.adjudicator_ref, field_name="adjudicator_ref"),
            )
        normalized_values = [
            _normalize_for_equality(self.family_cluster),
            _normalize_for_equality(self.primary_carrier_class),
            _normalize_for_equality(self.lineage_overlay),
        ]
        if len(set(normalized_values)) != len(normalized_values):
            raise ValueError(
                "family_cluster, primary_carrier_class, and lineage_overlay must remain "
                "mutually non-equivalent"
            )
        return self


class RepoSchemaFamilyRegistry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, protected_namespaces=())

    schema: Literal["repo_schema_family_registry@1"] = REPO_SCHEMA_FAMILY_REGISTRY_SCHEMA
    schema_family_registry_id: str
    repo_snapshot_id: str
    repo_snapshot_hash: str
    snapshot_validity_posture: SnapshotValidityPosture
    source_set: RepoSourceSet
    classification_policy_ref: str
    classification_policy_hash: str
    reconstruction_equivalence_mode: ReconstructionEquivalenceMode = RECONSTRUCTION_EQUIVALENCE_MODE
    schema_entries: list[RepoSchemaFamilyRegistryEntry] = Field(min_length=1)
    reconstruction_subset: list[RepoSchemaReconstructionRow] = Field(min_length=1)
    evidence_refs: list[RepoDescriptionEvidenceRef] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_registry(self) -> RepoSchemaFamilyRegistry:
        object.__setattr__(
            self,
            "schema_family_registry_id",
            _assert_non_empty_text(
                self.schema_family_registry_id, field_name="schema_family_registry_id"
            ),
        )
        object.__setattr__(
            self,
            "repo_snapshot_id",
            _assert_non_empty_text(self.repo_snapshot_id, field_name="repo_snapshot_id"),
        )
        object.__setattr__(
            self,
            "repo_snapshot_hash",
            _assert_hash(self.repo_snapshot_hash, field_name="repo_snapshot_hash"),
        )
        object.__setattr__(
            self,
            "classification_policy_ref",
            _assert_non_empty_text(
                self.classification_policy_ref, field_name="classification_policy_ref"
            ),
        )
        object.__setattr__(
            self,
            "classification_policy_hash",
            _assert_hash(self.classification_policy_hash, field_name="classification_policy_hash"),
        )
        if self.classification_policy_ref != V45A_CLASSIFICATION_POLICY_REF:
            raise ValueError("classification_policy_ref must bind to the v45a policy reference")
        expected_policy_hash = compute_v45a_classification_policy_hash()
        if self.classification_policy_hash != expected_policy_hash:
            raise ValueError("classification_policy_hash must match bound policy content")
        if self.reconstruction_equivalence_mode != RECONSTRUCTION_EQUIVALENCE_MODE:
            raise ValueError(
                "reconstruction_equivalence_mode must be canonical_normalized_semantic_equivalence"
            )

        evidence_by_ref = {entry.evidence_ref: entry for entry in self.evidence_refs}
        if len(evidence_by_ref) != len(self.evidence_refs):
            raise ValueError("evidence_refs evidence_ref values must be unique")
        if [entry.evidence_ref for entry in self.evidence_refs] != sorted(evidence_by_ref):
            raise ValueError("evidence_refs must be sorted lexicographically by evidence_ref")

        entries_by_key = {entry.schema_key: entry for entry in self.schema_entries}
        if len(entries_by_key) != len(self.schema_entries):
            raise ValueError("schema_entries schema_key values must be unique")
        if [entry.schema_key for entry in self.schema_entries] != sorted(entries_by_key):
            raise ValueError("schema_entries must be sorted lexicographically by schema_key")

        reconstruction_by_key = {entry.schema_key: entry for entry in self.reconstruction_subset}
        if len(reconstruction_by_key) != len(self.reconstruction_subset):
            raise ValueError("reconstruction_subset schema_key values must be unique")
        if [entry.schema_key for entry in self.reconstruction_subset] != sorted(
            reconstruction_by_key
        ):
            raise ValueError("reconstruction_subset must be sorted lexicographically by schema_key")

        for row in self.schema_entries:
            row_evidence = [evidence_by_ref.get(ref) for ref in row.supporting_evidence_refs]
            if any(item is None for item in row_evidence):
                raise ValueError(
                    "supporting_evidence_refs must reference top-level evidence_refs entries"
                )
            row_kinds = {item.evidence_kind for item in row_evidence if item is not None}

            if (
                row.classification_method == "lexical_naming"
                and not row.schema_discriminator.startswith("missing_schema_discriminator:")
            ):
                raise ValueError(
                    "naming-only role-form classification is forbidden for typed schema rows"
                )
            if row.classification_method == "lexical_naming" and row_kinds.intersection(
                _STRONGER_PRECEDENCE_EVIDENCE_KINDS
            ):
                raise ValueError(
                    "precedence contradiction: lexical naming may not overrule structural, "
                    "semantic, or governance evidence"
                )
            if row.classification_posture == "settled":
                if row.adjudicator_ref is None:
                    raise ValueError("settled posture requires explicit adjudicator_ref support")
                if "adjudication_artifact_evidence" not in row_kinds:
                    raise ValueError(
                        "settled posture requires adjudication_artifact_evidence support"
                    )
                if row.schema_key not in reconstruction_by_key:
                    raise ValueError(
                        "settled posture in v45a is bounded to representative reconstruction subset"
                    )

        for reconstruction_row in self.reconstruction_subset:
            if reconstruction_row.schema_key not in entries_by_key:
                raise ValueError(
                    "reconstruction_subset rows must reference existing schema_entries schema_key"
                )
            for evidence_ref in reconstruction_row.evidence_refs:
                evidence_entry = evidence_by_ref.get(evidence_ref)
                if evidence_entry is None:
                    raise ValueError(
                        "reconstruction_subset evidence_refs must reference "
                        "top-level evidence_refs entries"
                    )
            source_norm = canonical_json(reconstruction_row.source_schema_definition)
            reconstructed_norm = canonical_json(reconstruction_row.reconstructed_schema_definition)
            if source_norm != reconstructed_norm:
                raise ValueError(
                    "reconstruction_subset rows must round-trip under canonical normalized "
                    "semantic equivalence"
                )

        payload_without_id = self.model_dump(mode="json")
        payload_without_id.pop("schema_family_registry_id", None)
        expected_id = compute_repo_schema_family_registry_id(payload_without_id)
        if self.schema_family_registry_id != expected_id:
            raise ValueError(
                "schema_family_registry_id must match canonical full payload hash identity"
            )
        return self


class RepoEntityCatalogEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    entity_ref: str
    surface_kind: str
    semantic_role: str
    governance_posture: str
    derivation_posture: str
    mutation_posture: str
    classification_posture: ClassificationPosture
    classification_method: ClassificationMethod
    adjudicator_ref: str | None = None
    supporting_evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_entry(self) -> RepoEntityCatalogEntry:
        text_fields = (
            "entity_ref",
            "surface_kind",
            "semantic_role",
            "governance_posture",
            "derivation_posture",
            "mutation_posture",
        )
        for field_name in text_fields:
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "supporting_evidence_refs",
            _assert_sorted_unique(
                self.supporting_evidence_refs, field_name="supporting_evidence_refs"
            ),
        )
        if self.adjudicator_ref is not None:
            object.__setattr__(
                self,
                "adjudicator_ref",
                _assert_non_empty_text(self.adjudicator_ref, field_name="adjudicator_ref"),
            )
        return self


class RepoEntityCatalog(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, protected_namespaces=())

    schema: Literal["repo_entity_catalog@1"] = REPO_ENTITY_CATALOG_SCHEMA
    repo_entity_catalog_id: str
    repo_snapshot_id: str
    repo_snapshot_hash: str
    snapshot_validity_posture: SnapshotValidityPosture
    catalog_scope: str
    entity_coverage_mode: EntityCoverageMode = SCHEMA_VISIBLE_ENTITY_COVERAGE_MODE
    classification_policy_ref: str
    classification_policy_hash: str
    entities: list[RepoEntityCatalogEntry] = Field(min_length=1)
    evidence_refs: list[RepoDescriptionEvidenceRef] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_catalog(self) -> RepoEntityCatalog:
        object.__setattr__(
            self,
            "repo_entity_catalog_id",
            _assert_non_empty_text(
                self.repo_entity_catalog_id, field_name="repo_entity_catalog_id"
            ),
        )
        object.__setattr__(
            self,
            "repo_snapshot_id",
            _assert_non_empty_text(self.repo_snapshot_id, field_name="repo_snapshot_id"),
        )
        object.__setattr__(
            self,
            "repo_snapshot_hash",
            _assert_hash(self.repo_snapshot_hash, field_name="repo_snapshot_hash"),
        )
        object.__setattr__(
            self,
            "catalog_scope",
            _assert_non_empty_text(self.catalog_scope, field_name="catalog_scope"),
        )
        object.__setattr__(
            self,
            "classification_policy_ref",
            _assert_non_empty_text(
                self.classification_policy_ref, field_name="classification_policy_ref"
            ),
        )
        object.__setattr__(
            self,
            "classification_policy_hash",
            _assert_hash(self.classification_policy_hash, field_name="classification_policy_hash"),
        )
        if self.entity_coverage_mode != SCHEMA_VISIBLE_ENTITY_COVERAGE_MODE:
            raise ValueError(
                "entity_coverage_mode must remain bounded_schema_visible_slice for v45a"
            )
        if self.classification_policy_ref != V45A_CLASSIFICATION_POLICY_REF:
            raise ValueError("classification_policy_ref must bind to the v45a policy reference")
        if self.classification_policy_hash != compute_v45a_classification_policy_hash():
            raise ValueError("classification_policy_hash must match bound policy content")

        evidence_by_ref = {entry.evidence_ref: entry for entry in self.evidence_refs}
        if len(evidence_by_ref) != len(self.evidence_refs):
            raise ValueError("evidence_refs evidence_ref values must be unique")
        if [entry.evidence_ref for entry in self.evidence_refs] != sorted(evidence_by_ref):
            raise ValueError("evidence_refs must be sorted lexicographically by evidence_ref")

        entities_by_ref = {entry.entity_ref: entry for entry in self.entities}
        if len(entities_by_ref) != len(self.entities):
            raise ValueError("entities entity_ref values must be unique")
        if [entry.entity_ref for entry in self.entities] != sorted(entities_by_ref):
            raise ValueError("entities must be sorted lexicographically by entity_ref")

        for row in self.entities:
            row_evidence = [evidence_by_ref.get(ref) for ref in row.supporting_evidence_refs]
            if any(item is None for item in row_evidence):
                raise ValueError(
                    "supporting_evidence_refs must reference top-level evidence_refs entries"
                )
            row_kinds = {item.evidence_kind for item in row_evidence if item is not None}
            if row.classification_posture == "settled":
                if row.adjudicator_ref is None:
                    raise ValueError("settled posture requires explicit adjudicator_ref support")
                if "adjudication_artifact_evidence" not in row_kinds:
                    raise ValueError(
                        "settled posture requires adjudication_artifact_evidence support"
                    )

        payload_without_id = self.model_dump(mode="json")
        payload_without_id.pop("repo_entity_catalog_id", None)
        expected_id = compute_repo_entity_catalog_id(payload_without_id)
        if self.repo_entity_catalog_id != expected_id:
            raise ValueError(
                "repo_entity_catalog_id must match canonical full payload hash identity"
            )
        return self


class RepoSymbolCatalogEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    symbol_id: str
    module_path: str
    qualname: str
    symbol_kind: SymbolKind
    role_classification_posture: ClassificationPosture
    role_classification_method: SymbolRoleClassificationMethod
    source_artifact_refs: list[str] = Field(min_length=1)
    supporting_evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_entry(self) -> RepoSymbolCatalogEntry:
        object.__setattr__(
            self,
            "module_path",
            _assert_repo_rel_path(self.module_path, field_name="module_path"),
        )
        object.__setattr__(
            self,
            "qualname",
            _assert_non_empty_text(self.qualname, field_name="qualname"),
        )
        object.__setattr__(
            self,
            "source_artifact_refs",
            _assert_sorted_unique(
                [
                    _assert_repo_rel_path(path, field_name="source_artifact_refs")
                    for path in self.source_artifact_refs
                ],
                field_name="source_artifact_refs",
            ),
        )
        object.__setattr__(
            self,
            "supporting_evidence_refs",
            _assert_sorted_unique(
                self.supporting_evidence_refs, field_name="supporting_evidence_refs"
            ),
        )
        expected_symbol_id = compute_symbol_id(
            module_path=self.module_path,
            qualname=self.qualname,
            symbol_kind=self.symbol_kind,
        )
        if self.symbol_id != expected_symbol_id:
            raise ValueError("symbol_id must match canonical module_path + qualname + symbol_kind")
        if self.module_path not in self.source_artifact_refs:
            raise ValueError("source_artifact_refs must include the symbol module_path")
        return self


class RepoSymbolCatalog(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, protected_namespaces=())

    schema: Literal["repo_symbol_catalog@1"] = REPO_SYMBOL_CATALOG_SCHEMA
    repo_symbol_catalog_id: str
    repo_snapshot_id: str
    repo_snapshot_hash: str
    snapshot_validity_posture: SnapshotValidityPosture
    source_set: list[str] = Field(min_length=1)
    source_set_hash: str
    graph_scope: str
    extraction_posture: ClassificationPosture
    extraction_method: DependencyGraphMethod
    symbol_entries: list[RepoSymbolCatalogEntry] = Field(min_length=1)
    evidence_refs: list[RepoDescriptionEvidenceRef] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_catalog(self) -> RepoSymbolCatalog:
        object.__setattr__(
            self,
            "repo_symbol_catalog_id",
            _assert_non_empty_text(
                self.repo_symbol_catalog_id, field_name="repo_symbol_catalog_id"
            ),
        )
        object.__setattr__(
            self,
            "repo_snapshot_id",
            _assert_non_empty_text(self.repo_snapshot_id, field_name="repo_snapshot_id"),
        )
        object.__setattr__(
            self,
            "repo_snapshot_hash",
            _assert_hash(self.repo_snapshot_hash, field_name="repo_snapshot_hash"),
        )
        object.__setattr__(
            self,
            "source_set",
            _assert_sorted_unique(
                [_assert_repo_rel_path(path, field_name="source_set") for path in self.source_set],
                field_name="source_set",
            ),
        )
        object.__setattr__(
            self,
            "source_set_hash",
            _assert_hash(self.source_set_hash, field_name="source_set_hash"),
        )
        object.__setattr__(
            self,
            "graph_scope",
            _assert_no_forbidden_v45b_graph_scope_terms(
                self.graph_scope,
                field_name="graph_scope",
            ),
        )

        evidence_by_ref = {entry.evidence_ref: entry for entry in self.evidence_refs}
        if len(evidence_by_ref) != len(self.evidence_refs):
            raise ValueError("evidence_refs evidence_ref values must be unique")
        if [entry.evidence_ref for entry in self.evidence_refs] != sorted(evidence_by_ref):
            raise ValueError("evidence_refs must be sorted lexicographically by evidence_ref")

        entries_by_id = {entry.symbol_id: entry for entry in self.symbol_entries}
        if len(entries_by_id) != len(self.symbol_entries):
            raise ValueError("symbol_entries symbol_id values must be unique")
        if [entry.symbol_id for entry in self.symbol_entries] != sorted(entries_by_id):
            raise ValueError("symbol_entries must be sorted lexicographically by symbol_id")

        source_set_membership = set(self.source_set)
        for entry in self.symbol_entries:
            if entry.module_path not in source_set_membership:
                raise ValueError("symbol_entries module_path must resolve inside source_set")
            if any(ref not in source_set_membership for ref in entry.source_artifact_refs):
                raise ValueError(
                    "symbol_entries source_artifact_refs must resolve inside source_set"
                )
            row_evidence = [evidence_by_ref.get(ref) for ref in entry.supporting_evidence_refs]
            if any(item is None for item in row_evidence):
                raise ValueError(
                    "symbol_entries supporting_evidence_refs must reference top-level evidence_refs"
                )

        payload_without_id = self.model_dump(mode="json")
        payload_without_id.pop("repo_symbol_catalog_id", None)
        expected_id = compute_repo_symbol_catalog_id(payload_without_id)
        if self.repo_symbol_catalog_id != expected_id:
            raise ValueError(
                "repo_symbol_catalog_id must match canonical full payload hash identity"
            )
        return self


class RepoDependencyGraphEdge(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    edge_id: str
    from_ref_kind: EndpointKind
    from_ref: str
    to_ref_kind: EndpointKind
    to_ref: str
    dependency_kind: DependencyGraphKind
    dependency_posture: DependencyGraphPosture
    derivation_posture: ClassificationPosture
    derivation_method: DependencyGraphMethod
    source_artifact_refs: list[str] = Field(min_length=1)
    supporting_evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_edge(self) -> RepoDependencyGraphEdge:
        object.__setattr__(
            self, "edge_id", _assert_non_empty_text(self.edge_id, field_name="edge_id")
        )
        object.__setattr__(
            self,
            "from_ref",
            _assert_non_empty_text(self.from_ref, field_name="from_ref"),
        )
        object.__setattr__(
            self,
            "to_ref",
            _assert_non_empty_text(self.to_ref, field_name="to_ref"),
        )
        object.__setattr__(
            self,
            "source_artifact_refs",
            _assert_sorted_unique(
                [
                    _assert_repo_rel_path(path, field_name="source_artifact_refs")
                    for path in self.source_artifact_refs
                ],
                field_name="source_artifact_refs",
            ),
        )
        object.__setattr__(
            self,
            "supporting_evidence_refs",
            _assert_sorted_unique(
                self.supporting_evidence_refs, field_name="supporting_evidence_refs"
            ),
        )
        if self.from_ref_kind == "external_dependency":
            raise ValueError("from_ref_kind may not be external_dependency in v45b")
        if self.from_ref_kind == "internal_module_boundary":
            object.__setattr__(
                self,
                "from_ref",
                _assert_internal_module_boundary_ref(self.from_ref, field_name="from_ref"),
            )
        if self.to_ref_kind == "internal_module_boundary":
            object.__setattr__(
                self,
                "to_ref",
                _assert_internal_module_boundary_ref(self.to_ref, field_name="to_ref"),
            )
        if self.to_ref_kind == "external_dependency":
            object.__setattr__(
                self,
                "to_ref",
                _assert_external_dependency_ref(
                    self.to_ref,
                    field_name="to_ref",
                    dependency_posture=self.dependency_posture,
                ),
            )
        elif self.dependency_posture != "internal_resolved":
            raise ValueError(
                "boundary dependency_posture requires to_ref_kind = external_dependency"
            )
        if (
            self.dependency_posture == "internal_resolved"
            and self.to_ref_kind == "external_dependency"
        ):
            raise ValueError(
                "internal_resolved dependency_posture may not target external_dependency"
            )
        if self.from_ref_kind == self.to_ref_kind and self.from_ref == self.to_ref:
            raise ValueError("dependency edges may not be self-referential")
        return self


class RepoDependencyGraph(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, protected_namespaces=())

    schema: Literal["repo_dependency_graph@1"] = REPO_DEPENDENCY_GRAPH_SCHEMA
    repo_dependency_graph_id: str
    repo_snapshot_id: str
    repo_snapshot_hash: str
    snapshot_validity_posture: SnapshotValidityPosture
    source_set: list[str] = Field(min_length=1)
    source_set_hash: str
    graph_scope: str
    extraction_posture: ClassificationPosture
    extraction_method: DependencyGraphMethod
    dependency_edges: list[RepoDependencyGraphEdge] = Field(default_factory=list)
    evidence_refs: list[RepoDescriptionEvidenceRef] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_graph(self) -> RepoDependencyGraph:
        object.__setattr__(
            self,
            "repo_dependency_graph_id",
            _assert_non_empty_text(
                self.repo_dependency_graph_id, field_name="repo_dependency_graph_id"
            ),
        )
        object.__setattr__(
            self,
            "repo_snapshot_id",
            _assert_non_empty_text(self.repo_snapshot_id, field_name="repo_snapshot_id"),
        )
        object.__setattr__(
            self,
            "repo_snapshot_hash",
            _assert_hash(self.repo_snapshot_hash, field_name="repo_snapshot_hash"),
        )
        object.__setattr__(
            self,
            "source_set",
            _assert_sorted_unique(
                [_assert_repo_rel_path(path, field_name="source_set") for path in self.source_set],
                field_name="source_set",
            ),
        )
        object.__setattr__(
            self,
            "source_set_hash",
            _assert_hash(self.source_set_hash, field_name="source_set_hash"),
        )
        object.__setattr__(
            self,
            "graph_scope",
            _assert_no_forbidden_v45b_graph_scope_terms(
                self.graph_scope,
                field_name="graph_scope",
            ),
        )

        evidence_by_ref = {entry.evidence_ref: entry for entry in self.evidence_refs}
        if len(evidence_by_ref) != len(self.evidence_refs):
            raise ValueError("evidence_refs evidence_ref values must be unique")
        if [entry.evidence_ref for entry in self.evidence_refs] != sorted(evidence_by_ref):
            raise ValueError("evidence_refs must be sorted lexicographically by evidence_ref")

        edges_by_id = {edge.edge_id: edge for edge in self.dependency_edges}
        if len(edges_by_id) != len(self.dependency_edges):
            raise ValueError("dependency_edges edge_id values must be unique")
        if [edge.edge_id for edge in self.dependency_edges] != sorted(edges_by_id):
            raise ValueError("dependency_edges must be sorted lexicographically by edge_id")

        source_set_membership = set(self.source_set)
        module_boundary_refs = {
            compute_internal_module_boundary_ref(module_path=path) for path in self.source_set
        }
        for edge in self.dependency_edges:
            if any(ref not in source_set_membership for ref in edge.source_artifact_refs):
                raise ValueError(
                    "dependency_edges source_artifact_refs must resolve inside source_set"
                )
            row_evidence = [evidence_by_ref.get(ref) for ref in edge.supporting_evidence_refs]
            if any(item is None for item in row_evidence):
                raise ValueError(
                    "dependency_edges supporting_evidence_refs must reference "
                    "top-level evidence_refs"
                )
            if (
                edge.from_ref_kind == "internal_module_boundary"
                and edge.from_ref not in module_boundary_refs
            ):
                raise ValueError(
                    "dependency_edges from_ref must resolve inside source_set module boundaries"
                )
            if (
                edge.to_ref_kind == "internal_module_boundary"
                and edge.to_ref not in module_boundary_refs
            ):
                raise ValueError(
                    "dependency_edges to_ref must resolve inside source_set module boundaries"
                )

        payload_without_id = self.model_dump(mode="json")
        payload_without_id.pop("repo_dependency_graph_id", None)
        expected_id = compute_repo_dependency_graph_id(payload_without_id)
        if self.repo_dependency_graph_id != expected_id:
            raise ValueError(
                "repo_dependency_graph_id must match canonical full payload hash identity"
            )
        return self


class RepoGuardedSurfaceRef(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    guarded_surface_ref_kind: GuardedSurfaceRefKind
    guarded_surface_ref_value: str

    @model_validator(mode="after")
    def _validate_ref(self) -> RepoGuardedSurfaceRef:
        object.__setattr__(
            self,
            "guarded_surface_ref_value",
            _assert_guarded_surface_ref(
                self.guarded_surface_ref_value,
                field_name="guarded_surface_ref_value",
                guarded_surface_ref_kind=self.guarded_surface_ref_kind,
            ),
        )
        return self


class RepoClaimedInvariantBinding(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    binding_id: str
    binding_statement: str

    @model_validator(mode="after")
    def _validate_binding(self) -> RepoClaimedInvariantBinding:
        object.__setattr__(
            self,
            "binding_statement",
            _assert_non_empty_text(self.binding_statement, field_name="binding_statement"),
        )
        expected_binding_id = compute_claimed_invariant_binding_id(
            binding_statement=self.binding_statement,
        )
        if self.binding_id == expected_binding_id:
            return self
        raise ValueError("binding_id must match canonical binding payload identity")


class RepoObservedAssertionSurface(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    assertion_surface_kind: AssertionSurfaceKind
    assertion_source_ref: str
    assertion_summary: str

    @model_validator(mode="after")
    def _validate_surface(self) -> RepoObservedAssertionSurface:
        object.__setattr__(
            self,
            "assertion_source_ref",
            _assert_assertion_source_ref(
                self.assertion_source_ref, field_name="assertion_source_ref"
            ),
        )
        object.__setattr__(
            self,
            "assertion_summary",
            _assert_non_empty_text(self.assertion_summary, field_name="assertion_summary"),
        )
        return self


def compute_repo_test_intent_entry_id(payload_without_entry_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_entry_id)
    canonical_payload.pop("entry_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"test_intent_entry_{digest[:24]}"


class RepoTestIntentEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    entry_id: str
    test_ref: str
    test_kind: TestKind
    guarded_surface_ref: RepoGuardedSurfaceRef
    claimed_invariant_binding: RepoClaimedInvariantBinding
    observed_assertion_surface: RepoObservedAssertionSurface
    invariant_domain: InvariantDomain
    gating_posture: GatingPosture
    confidence_posture: ConfidencePosture
    derivation_posture: ClassificationPosture
    derivation_method: TestIntentDerivationMethod
    source_artifact_refs: list[str] = Field(min_length=1)
    supporting_evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_entry(self) -> RepoTestIntentEntry:
        object.__setattr__(
            self,
            "test_ref",
            _assert_test_ref(self.test_ref, field_name="test_ref"),
        )
        object.__setattr__(
            self,
            "source_artifact_refs",
            _assert_sorted_unique(
                [
                    _assert_repo_rel_path(path, field_name="source_artifact_refs")
                    for path in self.source_artifact_refs
                ],
                field_name="source_artifact_refs",
            ),
        )
        object.__setattr__(
            self,
            "supporting_evidence_refs",
            _assert_sorted_unique(
                self.supporting_evidence_refs, field_name="supporting_evidence_refs"
            ),
        )
        test_source_path = _test_source_path_from_test_ref(self.test_ref)
        if test_source_path not in self.source_artifact_refs:
            raise ValueError("source_artifact_refs must include the test source path")
        assertion_source_path = self.observed_assertion_surface.assertion_source_ref[
            len("assertion:") :
        ].split("#L", 1)[0]
        if assertion_source_path not in self.source_artifact_refs:
            raise ValueError(
                "observed_assertion_surface assertion_source_ref must resolve inside "
                "source_artifact_refs"
            )
        if self.derivation_method == "test_name_convention" and self.confidence_posture not in {
            "low",
            "medium",
        }:
            raise ValueError(
                "test_name_convention derivation may not carry high, adjudicated, or settled "
                "confidence_posture"
            )
        if self.derivation_method == "bounded_inference_rule" and self.confidence_posture not in {
            "low",
            "medium",
        }:
            raise ValueError(
                "bounded_inference_rule derivation may not carry high, adjudicated, or settled "
                "confidence_posture"
            )
        if self.confidence_posture == "settled" and self.derivation_posture != "settled":
            raise ValueError("settled confidence_posture requires settled derivation_posture")
        if self.confidence_posture == "adjudicated" and self.derivation_posture not in {
            "adjudicated",
            "settled",
        }:
            raise ValueError(
                "adjudicated confidence_posture requires adjudicated or settled derivation_posture"
            )
        payload_without_id = self.model_dump(mode="json")
        payload_without_id.pop("entry_id", None)
        expected_id = compute_repo_test_intent_entry_id(payload_without_id)
        if self.entry_id != expected_id:
            raise ValueError("entry_id must match canonical full payload hash identity")
        return self


class RepoTestIntentMatrix(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, protected_namespaces=())

    schema: Literal["repo_test_intent_matrix@1"] = REPO_TEST_INTENT_MATRIX_SCHEMA
    repo_test_intent_matrix_id: str
    repo_snapshot_id: str
    repo_snapshot_hash: str
    snapshot_validity_posture: SnapshotValidityPosture
    test_source_set: list[str] = Field(min_length=1)
    test_source_set_hash: str
    bound_symbol_catalog_ref: str
    bound_dependency_graph_ref: str
    matrix_scope: str
    extraction_posture: ClassificationPosture
    extraction_method: TestIntentDerivationMethod
    test_intent_entries: list[RepoTestIntentEntry] = Field(min_length=1)
    evidence_refs: list[RepoDescriptionEvidenceRef] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_matrix(self) -> RepoTestIntentMatrix:
        object.__setattr__(
            self,
            "repo_test_intent_matrix_id",
            _assert_non_empty_text(
                self.repo_test_intent_matrix_id, field_name="repo_test_intent_matrix_id"
            ),
        )
        object.__setattr__(
            self,
            "repo_snapshot_id",
            _assert_non_empty_text(self.repo_snapshot_id, field_name="repo_snapshot_id"),
        )
        object.__setattr__(
            self,
            "repo_snapshot_hash",
            _assert_hash(self.repo_snapshot_hash, field_name="repo_snapshot_hash"),
        )
        object.__setattr__(
            self,
            "test_source_set",
            _assert_sorted_unique(
                [
                    _assert_repo_rel_path(path, field_name="test_source_set")
                    for path in self.test_source_set
                ],
                field_name="test_source_set",
            ),
        )
        object.__setattr__(
            self,
            "test_source_set_hash",
            _assert_hash(self.test_source_set_hash, field_name="test_source_set_hash"),
        )
        object.__setattr__(
            self,
            "bound_symbol_catalog_ref",
            _assert_non_empty_text(
                self.bound_symbol_catalog_ref, field_name="bound_symbol_catalog_ref"
            ),
        )
        object.__setattr__(
            self,
            "bound_dependency_graph_ref",
            _assert_non_empty_text(
                self.bound_dependency_graph_ref, field_name="bound_dependency_graph_ref"
            ),
        )
        object.__setattr__(
            self,
            "matrix_scope",
            _assert_no_forbidden_v45d_matrix_scope_terms(
                self.matrix_scope, field_name="matrix_scope"
            ),
        )

        evidence_by_ref = {entry.evidence_ref: entry for entry in self.evidence_refs}
        if len(evidence_by_ref) != len(self.evidence_refs):
            raise ValueError("evidence_refs evidence_ref values must be unique")
        if [entry.evidence_ref for entry in self.evidence_refs] != sorted(evidence_by_ref):
            raise ValueError("evidence_refs must be sorted lexicographically by evidence_ref")

        entries_by_id = {entry.entry_id: entry for entry in self.test_intent_entries}
        if len(entries_by_id) != len(self.test_intent_entries):
            raise ValueError("test_intent_entries entry_id values must be unique")
        if [entry.entry_id for entry in self.test_intent_entries] != sorted(entries_by_id):
            raise ValueError("test_intent_entries must be sorted lexicographically by entry_id")

        source_set_membership = set(self.test_source_set)
        for entry in self.test_intent_entries:
            test_source_path = _test_source_path_from_test_ref(entry.test_ref)
            if test_source_path not in source_set_membership:
                raise ValueError("test_ref must resolve inside test_source_set")
            if any(ref not in source_set_membership for ref in entry.source_artifact_refs):
                raise ValueError(
                    "test_intent_entries source_artifact_refs must resolve inside "
                    "test_source_set"
                )
            assertion_source_path = entry.observed_assertion_surface.assertion_source_ref[
                len("assertion:") :
            ].split("#L", 1)[0]
            if assertion_source_path not in source_set_membership:
                raise ValueError(
                    "observed_assertion_surface assertion_source_ref must resolve inside "
                    "test_source_set"
                )
            row_evidence = [evidence_by_ref.get(ref) for ref in entry.supporting_evidence_refs]
            if any(item is None for item in row_evidence):
                raise ValueError(
                    "test_intent_entries supporting_evidence_refs must reference top-level "
                    "evidence_refs"
                )

        payload_without_id = self.model_dump(mode="json")
        payload_without_id.pop("repo_test_intent_matrix_id", None)
        expected_id = compute_repo_test_intent_matrix_id(payload_without_id)
        if self.repo_test_intent_matrix_id != expected_id:
            raise ValueError(
                "repo_test_intent_matrix_id must match canonical full payload hash identity"
            )
        return self


def validate_repo_symbol_catalog_dependency_graph_pair(
    *,
    symbol_catalog_payload: dict[str, Any],
    dependency_graph_payload: dict[str, Any],
) -> tuple[RepoSymbolCatalog, RepoDependencyGraph]:
    symbol_catalog = RepoSymbolCatalog.model_validate(symbol_catalog_payload)
    dependency_graph = RepoDependencyGraph.model_validate(dependency_graph_payload)
    if symbol_catalog.repo_snapshot_id != dependency_graph.repo_snapshot_id:
        raise ValueError("symbol catalog and dependency graph must share repo_snapshot_id")
    if symbol_catalog.repo_snapshot_hash != dependency_graph.repo_snapshot_hash:
        raise ValueError("symbol catalog and dependency graph must share repo_snapshot_hash")
    if symbol_catalog.source_set != dependency_graph.source_set:
        raise ValueError("symbol catalog and dependency graph must share source_set")
    if symbol_catalog.source_set_hash != dependency_graph.source_set_hash:
        raise ValueError("symbol catalog and dependency graph must share source_set_hash")

    symbol_ids = {entry.symbol_id for entry in symbol_catalog.symbol_entries}
    module_boundary_refs = {
        compute_internal_module_boundary_ref(module_path=path) for path in symbol_catalog.source_set
    }
    for edge in dependency_graph.dependency_edges:
        if edge.from_ref_kind == "internal_symbol" and edge.from_ref not in symbol_ids:
            raise ValueError("dependency edge from_ref must resolve against repo_symbol_catalog")
        if edge.to_ref_kind == "internal_symbol" and edge.to_ref not in symbol_ids:
            raise ValueError("dependency edge to_ref must resolve against repo_symbol_catalog")
        if (
            edge.from_ref_kind == "internal_module_boundary"
            and edge.from_ref not in module_boundary_refs
        ):
            raise ValueError(
                "dependency edge from_ref must resolve against internal module boundaries"
            )
        if (
            edge.to_ref_kind == "internal_module_boundary"
            and edge.to_ref not in module_boundary_refs
        ):
            raise ValueError(
                "dependency edge to_ref must resolve against internal module boundaries"
            )
    return symbol_catalog, dependency_graph


def validate_repo_test_intent_matrix_against_v45b(
    *,
    test_intent_matrix_payload: dict[str, Any],
    symbol_catalog_payload: dict[str, Any],
    dependency_graph_payload: dict[str, Any],
) -> tuple[RepoTestIntentMatrix, RepoSymbolCatalog, RepoDependencyGraph]:
    matrix = RepoTestIntentMatrix.model_validate(test_intent_matrix_payload)
    symbol_catalog, dependency_graph = validate_repo_symbol_catalog_dependency_graph_pair(
        symbol_catalog_payload=symbol_catalog_payload,
        dependency_graph_payload=dependency_graph_payload,
    )
    if matrix.bound_symbol_catalog_ref != symbol_catalog.repo_symbol_catalog_id:
        raise ValueError("repo_test_intent_matrix must bind the provided repo_symbol_catalog")
    if matrix.bound_dependency_graph_ref != dependency_graph.repo_dependency_graph_id:
        raise ValueError("repo_test_intent_matrix must bind the provided repo_dependency_graph")
    if matrix.repo_snapshot_id != symbol_catalog.repo_snapshot_id:
        raise ValueError("repo_test_intent_matrix must share repo_snapshot_id with V45-B")
    if matrix.repo_snapshot_hash != symbol_catalog.repo_snapshot_hash:
        raise ValueError("repo_test_intent_matrix must share repo_snapshot_hash with V45-B")
    if matrix.snapshot_validity_posture != symbol_catalog.snapshot_validity_posture:
        raise ValueError(
            "repo_test_intent_matrix must share snapshot_validity_posture with V45-B"
        )
    symbol_ids = {entry.symbol_id for entry in symbol_catalog.symbol_entries}
    module_boundary_refs = {
        compute_internal_module_boundary_ref(module_path=path) for path in symbol_catalog.source_set
    }
    for entry in matrix.test_intent_entries:
        guarded_ref = entry.guarded_surface_ref
        if (
            guarded_ref.guarded_surface_ref_kind == "internal_symbol"
            and guarded_ref.guarded_surface_ref_value not in symbol_ids
        ):
            raise ValueError(
                "repo_test_intent_matrix guarded_surface_ref must resolve against "
                "repo_symbol_catalog"
            )
        if (
            guarded_ref.guarded_surface_ref_kind == "internal_module_boundary"
            and guarded_ref.guarded_surface_ref_value not in module_boundary_refs
        ):
            raise ValueError(
                "repo_test_intent_matrix guarded_surface_ref must resolve against "
                "internal module boundaries"
            )
    return matrix, symbol_catalog, dependency_graph


class RepoOptimizationClusterMemberRef(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    member_ref_kind: ClusterMemberRefKind
    member_ref: str

    @model_validator(mode="after")
    def _validate_member_ref(self) -> RepoOptimizationClusterMemberRef:
        object.__setattr__(
            self,
            "member_ref",
            _assert_cluster_member_ref(
                self.member_ref,
                field_name="member_ref",
                member_ref_kind=self.member_ref_kind,
            ),
        )
        return self


class RepoOptimizationFindingScope(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    finding_scope_kind: FindingScopeKind
    finding_scope_ref: str
    cluster_member_refs: list[RepoOptimizationClusterMemberRef] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_scope(self) -> RepoOptimizationFindingScope:
        object.__setattr__(
            self,
            "finding_scope_ref",
            _assert_finding_scope_ref(
                self.finding_scope_ref,
                field_name="finding_scope_ref",
                finding_scope_kind=self.finding_scope_kind,
            ),
        )
        cluster_members = list(self.cluster_member_refs)
        if self.finding_scope_kind == "cross_surface_cluster":
            if len(cluster_members) < 2:
                raise ValueError(
                    "cross_surface_cluster finding_scope_kind requires at least two "
                    "cluster_member_refs"
                )
            seen_members: set[tuple[str, str]] = set()
            for member in cluster_members:
                member_key = (member.member_ref_kind, member.member_ref)
                if member_key in seen_members:
                    raise ValueError("cluster_member_refs must be unique by kind/ref pair")
                seen_members.add(member_key)
        elif cluster_members:
            raise ValueError(
                "cluster_member_refs are only allowed when finding_scope_kind = "
                "cross_surface_cluster"
            )
        return self


def compute_repo_optimization_entry_id(payload_without_entry_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_entry_id)
    canonical_payload.pop("entry_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"optimization_entry_{digest[:24]}"


class RepoOptimizationEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    entry_id: str
    finding_scope: RepoOptimizationFindingScope
    compression_axis: CompressionAxis
    optimization_posture: OptimizationPosture
    support_basis: SupportBasis
    secondary_compression_axes: list[CompressionAxis] = Field(default_factory=list)
    secondary_support_basis_tags: list[SupportBasis] = Field(default_factory=list)
    descriptive_finding_summary: str
    optimization_candidate_summary: str
    priority_posture: PriorityPosture
    amendment_entitlement: AmendmentEntitlement
    derivation_posture: ClassificationPosture
    derivation_method: OptimizationDerivationMethod
    source_artifact_refs: list[str] = Field(min_length=1)
    supporting_evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_entry(self) -> RepoOptimizationEntry:
        object.__setattr__(
            self,
            "descriptive_finding_summary",
            _assert_no_forbidden_v45e_register_scope_terms(
                self.descriptive_finding_summary,
                field_name="descriptive_finding_summary",
            ),
        )
        object.__setattr__(
            self,
            "optimization_candidate_summary",
            _assert_no_forbidden_v45e_register_scope_terms(
                self.optimization_candidate_summary,
                field_name="optimization_candidate_summary",
            ),
        )
        object.__setattr__(
            self,
            "source_artifact_refs",
            _assert_sorted_unique(
                [
                    _assert_repo_rel_path(path, field_name="source_artifact_refs")
                    for path in self.source_artifact_refs
                ],
                field_name="source_artifact_refs",
            ),
        )
        object.__setattr__(
            self,
            "supporting_evidence_refs",
            _assert_sorted_unique(
                self.supporting_evidence_refs, field_name="supporting_evidence_refs"
            ),
        )
        object.__setattr__(
            self,
            "secondary_compression_axes",
            sorted(set(self.secondary_compression_axes)),
        )
        object.__setattr__(
            self,
            "secondary_support_basis_tags",
            sorted(set(self.secondary_support_basis_tags)),
        )
        if self.compression_axis in self.secondary_compression_axes:
            raise ValueError("secondary_compression_axes may not repeat compression_axis")
        if self.support_basis in self.secondary_support_basis_tags:
            raise ValueError("secondary_support_basis_tags may not repeat support_basis")
        payload_without_id = self.model_dump(mode="json")
        payload_without_id.pop("entry_id", None)
        expected_id = compute_repo_optimization_entry_id(payload_without_id)
        if self.entry_id != expected_id:
            raise ValueError("entry_id must match canonical full payload hash identity")
        return self


class RepoOptimizationRegister(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, protected_namespaces=())

    schema: Literal["repo_optimization_register@1"] = REPO_OPTIMIZATION_REGISTER_SCHEMA
    repo_optimization_register_id: str
    repo_snapshot_id: str
    repo_snapshot_hash: str
    snapshot_validity_posture: SnapshotValidityPosture
    source_set: list[str] = Field(min_length=1)
    source_set_hash: str
    bound_entity_catalog_ref: str
    bound_schema_family_registry_ref: str
    bound_symbol_catalog_ref: str
    bound_dependency_graph_ref: str
    bound_test_intent_matrix_ref: str
    register_scope: str
    extraction_posture: ClassificationPosture
    extraction_method: OptimizationDerivationMethod
    optimization_entries: list[RepoOptimizationEntry] = Field(min_length=1)
    evidence_refs: list[RepoDescriptionEvidenceRef] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_register(self) -> RepoOptimizationRegister:
        object.__setattr__(
            self,
            "repo_optimization_register_id",
            _assert_non_empty_text(
                self.repo_optimization_register_id, field_name="repo_optimization_register_id"
            ),
        )
        object.__setattr__(
            self,
            "repo_snapshot_id",
            _assert_non_empty_text(self.repo_snapshot_id, field_name="repo_snapshot_id"),
        )
        object.__setattr__(
            self,
            "repo_snapshot_hash",
            _assert_hash(self.repo_snapshot_hash, field_name="repo_snapshot_hash"),
        )
        object.__setattr__(
            self,
            "source_set",
            _assert_sorted_unique(
                [_assert_repo_rel_path(path, field_name="source_set") for path in self.source_set],
                field_name="source_set",
            ),
        )
        object.__setattr__(
            self,
            "source_set_hash",
            _assert_hash(self.source_set_hash, field_name="source_set_hash"),
        )
        for field_name in (
            "bound_entity_catalog_ref",
            "bound_schema_family_registry_ref",
            "bound_symbol_catalog_ref",
            "bound_dependency_graph_ref",
            "bound_test_intent_matrix_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "register_scope",
            _assert_no_forbidden_v45e_register_scope_terms(
                self.register_scope, field_name="register_scope"
            ),
        )

        evidence_by_ref = {entry.evidence_ref: entry for entry in self.evidence_refs}
        if len(evidence_by_ref) != len(self.evidence_refs):
            raise ValueError("evidence_refs evidence_ref values must be unique")
        if [entry.evidence_ref for entry in self.evidence_refs] != sorted(evidence_by_ref):
            raise ValueError("evidence_refs must be sorted lexicographically by evidence_ref")

        entries_by_id = {entry.entry_id: entry for entry in self.optimization_entries}
        if len(entries_by_id) != len(self.optimization_entries):
            raise ValueError("optimization_entries entry_id values must be unique")
        if [entry.entry_id for entry in self.optimization_entries] != sorted(entries_by_id):
            raise ValueError("optimization_entries must be sorted lexicographically by entry_id")

        source_set_membership = set(self.source_set)
        for entry in self.optimization_entries:
            if any(ref not in source_set_membership for ref in entry.source_artifact_refs):
                raise ValueError(
                    "optimization_entries source_artifact_refs must resolve inside source_set"
                )
            row_evidence = [evidence_by_ref.get(ref) for ref in entry.supporting_evidence_refs]
            if any(item is None for item in row_evidence):
                raise ValueError(
                    "optimization_entries supporting_evidence_refs must reference top-level "
                    "evidence_refs"
                )

        payload_without_id = self.model_dump(mode="json")
        payload_without_id.pop("repo_optimization_register_id", None)
        expected_id = compute_repo_optimization_register_id(payload_without_id)
        if self.repo_optimization_register_id != expected_id:
            raise ValueError(
                "repo_optimization_register_id must match canonical full payload hash identity"
            )
        return self


def validate_repo_optimization_register_against_v45_baseline(
    *,
    optimization_register_payload: dict[str, Any],
    entity_catalog_payload: dict[str, Any],
    schema_family_registry_payload: dict[str, Any],
    symbol_catalog_payload: dict[str, Any],
    dependency_graph_payload: dict[str, Any],
    test_intent_matrix_payload: dict[str, Any],
    arc_dependency_register_payload: dict[str, Any] | None = None,
) -> tuple[
    RepoOptimizationRegister,
    RepoEntityCatalog,
    RepoSchemaFamilyRegistry,
    RepoSymbolCatalog,
    RepoDependencyGraph,
    RepoTestIntentMatrix,
]:
    optimization_register = RepoOptimizationRegister.model_validate(optimization_register_payload)
    entity_catalog = RepoEntityCatalog.model_validate(entity_catalog_payload)
    schema_family_registry = RepoSchemaFamilyRegistry.model_validate(schema_family_registry_payload)
    symbol_catalog, dependency_graph = validate_repo_symbol_catalog_dependency_graph_pair(
        symbol_catalog_payload=symbol_catalog_payload,
        dependency_graph_payload=dependency_graph_payload,
    )
    test_intent_matrix, _bound_symbol_catalog, _bound_dependency_graph = (
        validate_repo_test_intent_matrix_against_v45b(
            test_intent_matrix_payload=test_intent_matrix_payload,
            symbol_catalog_payload=symbol_catalog_payload,
            dependency_graph_payload=dependency_graph_payload,
        )
    )
    if arc_dependency_register_payload is not None:
        arc_dependency_register = RepoArcDependencyRegister.model_validate(
            arc_dependency_register_payload
        )
        if (
            arc_dependency_register.snapshot_validity_posture
            != optimization_register.snapshot_validity_posture
        ):
            raise ValueError(
                "repo_optimization_register must share snapshot_validity_posture with V45-C"
            )

    if optimization_register.bound_entity_catalog_ref != entity_catalog.repo_entity_catalog_id:
        raise ValueError("repo_optimization_register must bind the provided repo_entity_catalog")
    if (
        optimization_register.bound_schema_family_registry_ref
        != schema_family_registry.schema_family_registry_id
    ):
        raise ValueError(
            "repo_optimization_register must bind the provided repo_schema_family_registry"
        )
    if optimization_register.bound_symbol_catalog_ref != symbol_catalog.repo_symbol_catalog_id:
        raise ValueError("repo_optimization_register must bind the provided repo_symbol_catalog")
    if (
        optimization_register.bound_dependency_graph_ref
        != dependency_graph.repo_dependency_graph_id
    ):
        raise ValueError("repo_optimization_register must bind the provided repo_dependency_graph")
    if (
        optimization_register.bound_test_intent_matrix_ref
        != test_intent_matrix.repo_test_intent_matrix_id
    ):
        raise ValueError(
            "repo_optimization_register must bind the provided repo_test_intent_matrix"
        )

    if optimization_register.repo_snapshot_id != symbol_catalog.repo_snapshot_id:
        raise ValueError("repo_optimization_register must share repo_snapshot_id with V45-B")
    if optimization_register.repo_snapshot_hash != symbol_catalog.repo_snapshot_hash:
        raise ValueError("repo_optimization_register must share repo_snapshot_hash with V45-B")
    if optimization_register.snapshot_validity_posture != symbol_catalog.snapshot_validity_posture:
        raise ValueError(
            "repo_optimization_register must share snapshot_validity_posture with V45-B"
        )
    if optimization_register.repo_snapshot_id != test_intent_matrix.repo_snapshot_id:
        raise ValueError("repo_optimization_register must share repo_snapshot_id with V45-D")
    if optimization_register.repo_snapshot_hash != test_intent_matrix.repo_snapshot_hash:
        raise ValueError("repo_optimization_register must share repo_snapshot_hash with V45-D")
    if (
        optimization_register.snapshot_validity_posture
        != test_intent_matrix.snapshot_validity_posture
    ):
        raise ValueError(
            "repo_optimization_register must share snapshot_validity_posture with V45-D"
        )
    if (
        optimization_register.snapshot_validity_posture
        != entity_catalog.snapshot_validity_posture
    ):
        raise ValueError(
            "repo_optimization_register must share snapshot_validity_posture with "
            "V45-A entity catalog"
        )
    if (
        optimization_register.snapshot_validity_posture
        != schema_family_registry.snapshot_validity_posture
    ):
        raise ValueError(
            "repo_optimization_register must share snapshot_validity_posture with "
            "V45-A schema registry"
        )

    source_set_membership = set(optimization_register.source_set)
    schema_surface_refs = {
        entry.schema_path for entry in schema_family_registry.schema_entries
    } | set(schema_family_registry.source_set.source_paths)
    module_boundary_refs = {
        compute_internal_module_boundary_ref(module_path=path) for path in symbol_catalog.source_set
    }
    test_surface_refs = set(test_intent_matrix.test_source_set)

    def _scope_ref_resolves(scope: RepoOptimizationFindingScope) -> bool:
        if scope.finding_scope_kind in {"file_surface", "test_surface"}:
            if scope.finding_scope_ref in source_set_membership:
                return True
            if (
                scope.finding_scope_kind == "test_surface"
                and scope.finding_scope_ref in test_surface_refs
            ):
                return True
            return False
        if scope.finding_scope_kind == "schema_surface":
            return scope.finding_scope_ref in schema_surface_refs
        if scope.finding_scope_kind == "module_surface":
            return scope.finding_scope_ref in module_boundary_refs
        if scope.finding_scope_kind == "cross_surface_cluster":
            for member in scope.cluster_member_refs:
                member_scope = RepoOptimizationFindingScope(
                    finding_scope_kind=member.member_ref_kind,
                    finding_scope_ref=member.member_ref,
                )
                if not _scope_ref_resolves(member_scope):
                    return False
            return True
        return False

    for entry in optimization_register.optimization_entries:
        if not _scope_ref_resolves(entry.finding_scope):
            raise ValueError(
                "repo_optimization_register finding_scope must resolve against source_set "
                "or a bound V45-A through V45-D descriptive artifact"
            )
    return (
        optimization_register,
        entity_catalog,
        schema_family_registry,
        symbol_catalog,
        dependency_graph,
        test_intent_matrix,
    )


class RepoArcDependencyRegisterEntryV1(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    arc_id: str
    family_path: str
    phase_status: ArcPhaseStatus
    authority_layer: AuthorityLayer
    readiness_posture: ReadinessPosture
    blocker_arc_ids: list[str] = Field(default_factory=list)
    blocked_by_arc_ids: list[str] = Field(default_factory=list)
    supporting_evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_entry(self) -> RepoArcDependencyRegisterEntryV1:
        object.__setattr__(self, "arc_id", _assert_non_empty_text(self.arc_id, field_name="arc_id"))
        object.__setattr__(
            self,
            "family_path",
            _assert_non_empty_text(self.family_path, field_name="family_path"),
        )
        object.__setattr__(
            self,
            "blocker_arc_ids",
            _assert_sorted_unique(self.blocker_arc_ids, field_name="blocker_arc_ids"),
        )
        object.__setattr__(
            self,
            "blocked_by_arc_ids",
            _assert_sorted_unique(self.blocked_by_arc_ids, field_name="blocked_by_arc_ids"),
        )
        object.__setattr__(
            self,
            "supporting_evidence_refs",
            _assert_sorted_unique(
                self.supporting_evidence_refs, field_name="supporting_evidence_refs"
            ),
        )
        if self.readiness_posture == "blocked" and not self.blocked_by_arc_ids:
            raise ValueError("blocked readiness_posture requires blocked_by_arc_ids")
        if self.readiness_posture != "blocked" and (
            self.blocked_by_arc_ids or self.blocker_arc_ids
        ):
            raise ValueError(
                "non-blocked readiness_posture may not carry blocker_arc_ids or blocked_by_arc_ids"
            )
        if self.blocker_arc_ids != self.blocked_by_arc_ids:
            raise ValueError("blocker_arc_ids and blocked_by_arc_ids must match in v45c")
        return self


class RepoArcDependencyEdgeV1(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    edge_id: str
    from_arc_id: str
    to_arc_id: str
    dependency_kind: DependencyKind
    dependency_strength: DependencyStrength
    dependency_status: DependencyStatus
    supports_all_three_way_claim: bool = False
    supporting_evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_edge(self) -> RepoArcDependencyEdgeV1:
        for field_name in ("edge_id", "from_arc_id", "to_arc_id"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "supporting_evidence_refs",
            _assert_sorted_unique(
                self.supporting_evidence_refs, field_name="supporting_evidence_refs"
            ),
        )
        if self.from_arc_id == self.to_arc_id:
            raise ValueError("dependency edges may not be self-referential")
        return self


class RepoArcDependencyRegisterV1(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, protected_namespaces=())

    schema: Literal["repo_arc_dependency_register@1"] = REPO_ARC_DEPENDENCY_REGISTER_V1_SCHEMA
    repo_arc_dependency_register_id: str
    repo_snapshot_id: str
    repo_snapshot_hash: str
    snapshot_validity_posture: SnapshotValidityPosture
    register_scope: str
    dependency_policy_ref: str
    dependency_policy_hash: str
    open_arc_entries: list[RepoArcDependencyRegisterEntryV1] = Field(min_length=1)
    dependency_edges: list[RepoArcDependencyEdgeV1] = Field(default_factory=list)
    evidence_refs: list[RepoDescriptionEvidenceRef] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_register(self) -> RepoArcDependencyRegisterV1:
        object.__setattr__(
            self,
            "repo_arc_dependency_register_id",
            _assert_non_empty_text(
                self.repo_arc_dependency_register_id, field_name="repo_arc_dependency_register_id"
            ),
        )
        object.__setattr__(
            self,
            "repo_snapshot_id",
            _assert_non_empty_text(self.repo_snapshot_id, field_name="repo_snapshot_id"),
        )
        object.__setattr__(
            self,
            "repo_snapshot_hash",
            _assert_hash(self.repo_snapshot_hash, field_name="repo_snapshot_hash"),
        )
        object.__setattr__(
            self,
            "register_scope",
            _assert_no_forbidden_authority_terms(self.register_scope, field_name="register_scope"),
        )
        object.__setattr__(
            self,
            "dependency_policy_ref",
            _assert_non_empty_text(self.dependency_policy_ref, field_name="dependency_policy_ref"),
        )
        object.__setattr__(
            self,
            "dependency_policy_hash",
            _assert_hash(self.dependency_policy_hash, field_name="dependency_policy_hash"),
        )
        if self.dependency_policy_ref != V45C_DEPENDENCY_POLICY_REF:
            raise ValueError("dependency_policy_ref must bind to the v45c dependency policy")
        if self.dependency_policy_hash != compute_v45c_v100_dependency_policy_hash():
            raise ValueError("dependency_policy_hash must match bound policy content")

        evidence_by_ref = {entry.evidence_ref: entry for entry in self.evidence_refs}
        if len(evidence_by_ref) != len(self.evidence_refs):
            raise ValueError("evidence_refs evidence_ref values must be unique")
        if [entry.evidence_ref for entry in self.evidence_refs] != sorted(evidence_by_ref):
            raise ValueError("evidence_refs must be sorted lexicographically by evidence_ref")

        entries_by_id = {entry.arc_id: entry for entry in self.open_arc_entries}
        if len(entries_by_id) != len(self.open_arc_entries):
            raise ValueError("open_arc_entries arc_id values must be unique")
        if [entry.arc_id for entry in self.open_arc_entries] != sorted(entries_by_id):
            raise ValueError("open_arc_entries must be sorted lexicographically by arc_id")

        edges_by_id = {edge.edge_id: edge for edge in self.dependency_edges}
        if len(edges_by_id) != len(self.dependency_edges):
            raise ValueError("dependency_edges edge_id values must be unique")
        if [edge.edge_id for edge in self.dependency_edges] != sorted(edges_by_id):
            raise ValueError("dependency_edges must be sorted lexicographically by edge_id")

        unresolved_hard_incoming: dict[str, list[str]] = {arc_id: [] for arc_id in entries_by_id}
        cycle_adjacency: dict[str, list[str]] = {arc_id: [] for arc_id in entries_by_id}

        for edge in self.dependency_edges:
            edge_evidence = [evidence_by_ref.get(ref) for ref in edge.supporting_evidence_refs]
            if any(item is None for item in edge_evidence):
                raise ValueError(
                    "dependency_edges supporting_evidence_refs must reference "
                    "top-level evidence_refs"
                )
            if edge.from_arc_id not in entries_by_id or edge.to_arc_id not in entries_by_id:
                raise ValueError("dependency edges must reference known open_arc_entries arc_id")
            cycle_adjacency[edge.from_arc_id].append(edge.to_arc_id)
            if edge.dependency_strength == "hard" and edge.dependency_status == "unresolved":
                unresolved_hard_incoming[edge.to_arc_id].append(edge.from_arc_id)

        for entry in self.open_arc_entries:
            row_evidence = [evidence_by_ref.get(ref) for ref in entry.supporting_evidence_refs]
            if any(item is None for item in row_evidence):
                raise ValueError(
                    "open_arc_entries supporting_evidence_refs must reference "
                    "top-level evidence_refs"
                )
            incoming = sorted(set(unresolved_hard_incoming[entry.arc_id]))
            if entry.readiness_posture == "blocked":
                if incoming != entry.blocked_by_arc_ids:
                    raise ValueError(
                        "blocked readiness_posture must match unresolved hard incoming dependencies"
                    )
            elif incoming:
                raise ValueError(
                    "ready/deferred readiness_posture may not coexist with unresolved hard blockers"
                )

        visited: set[str] = set()
        active: set[str] = set()

        def visit(node: str) -> None:
            if node in active:
                raise ValueError(
                    "dependency cycles are forbidden in v45c because no explicit cycle posture "
                    "is modeled"
                )
            if node in visited:
                return
            visited.add(node)
            active.add(node)
            for neighbor in sorted(cycle_adjacency[node]):
                visit(neighbor)
            active.remove(node)

        for arc_id in sorted(cycle_adjacency):
            visit(arc_id)

        payload_without_id = self.model_dump(mode="json")
        payload_without_id.pop("repo_arc_dependency_register_id", None)
        expected_id = compute_repo_arc_dependency_register_v1_id(payload_without_id)
        if self.repo_arc_dependency_register_id != expected_id:
            raise ValueError(
                "repo_arc_dependency_register_id must match canonical full payload hash identity"
            )
        return self


class RepoArcDependencyRegisterEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    arc_id: str
    family_path: str
    phase_status: ArcPhaseStatus
    authority_layer: AuthorityLayer
    readiness_posture: ReadinessPosture
    blocker_arc_ids: list[str] = Field(default_factory=list)
    blocked_by_arc_ids: list[str] = Field(default_factory=list)
    derivation_posture: ClassificationPosture
    derivation_method: DependencyRegisterMethod
    source_artifact_refs: list[str] = Field(min_length=1)
    supporting_evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_entry(self) -> RepoArcDependencyRegisterEntry:
        object.__setattr__(self, "arc_id", _assert_non_empty_text(self.arc_id, field_name="arc_id"))
        object.__setattr__(
            self,
            "family_path",
            _assert_non_empty_text(self.family_path, field_name="family_path"),
        )
        object.__setattr__(
            self,
            "blocker_arc_ids",
            _assert_sorted_unique(self.blocker_arc_ids, field_name="blocker_arc_ids"),
        )
        object.__setattr__(
            self,
            "blocked_by_arc_ids",
            _assert_sorted_unique(self.blocked_by_arc_ids, field_name="blocked_by_arc_ids"),
        )
        object.__setattr__(
            self,
            "source_artifact_refs",
            _assert_sorted_unique(
                [
                    _assert_repo_rel_path(path, field_name="source_artifact_refs")
                    for path in self.source_artifact_refs
                ],
                field_name="source_artifact_refs",
            ),
        )
        object.__setattr__(
            self,
            "supporting_evidence_refs",
            _assert_sorted_unique(
                self.supporting_evidence_refs, field_name="supporting_evidence_refs"
            ),
        )
        if self.readiness_posture == "blocked" and not self.blocked_by_arc_ids:
            raise ValueError("blocked readiness_posture requires blocked_by_arc_ids")
        if self.readiness_posture != "blocked" and (
            self.blocked_by_arc_ids or self.blocker_arc_ids
        ):
            raise ValueError(
                "non-blocked readiness_posture may not carry blocker_arc_ids or blocked_by_arc_ids"
            )
        if self.blocker_arc_ids != self.blocked_by_arc_ids:
            raise ValueError("blocker_arc_ids and blocked_by_arc_ids must match in v45c")
        return self


class RepoArcDependencyEdge(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    edge_id: str
    from_arc_id: str
    to_arc_id: str
    dependency_kind: DependencyKind
    dependency_strength: DependencyStrength
    dependency_status: DependencyStatus
    derivation_posture: ClassificationPosture
    derivation_method: DependencyRegisterMethod
    source_artifact_refs: list[str] = Field(min_length=1)
    supporting_evidence_refs: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_edge(self) -> RepoArcDependencyEdge:
        for field_name in ("edge_id", "from_arc_id", "to_arc_id"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "source_artifact_refs",
            _assert_sorted_unique(
                [
                    _assert_repo_rel_path(path, field_name="source_artifact_refs")
                    for path in self.source_artifact_refs
                ],
                field_name="source_artifact_refs",
            ),
        )
        object.__setattr__(
            self,
            "supporting_evidence_refs",
            _assert_sorted_unique(
                self.supporting_evidence_refs, field_name="supporting_evidence_refs"
            ),
        )
        if self.from_arc_id == self.to_arc_id:
            raise ValueError("dependency edges may not be self-referential")
        return self


class RepoArcDependencyRegister(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, protected_namespaces=())

    schema: Literal["repo_arc_dependency_register@2"] = REPO_ARC_DEPENDENCY_REGISTER_SCHEMA
    repo_arc_dependency_register_id: str
    repo_snapshot_id: str
    repo_snapshot_hash: str
    snapshot_validity_posture: SnapshotValidityPosture
    source_set: list[str] = Field(min_length=1)
    source_set_hash: str
    register_scope: str
    pending_list_posture: PendingListPosture
    cycle_posture: CyclePosture
    cycle_detection_scope: CycleDetectionScope
    dependency_policy_ref: str
    dependency_policy_hash: str
    extraction_posture: ClassificationPosture
    extraction_method: DependencyRegisterMethod
    open_arc_entries: list[RepoArcDependencyRegisterEntry] = Field(min_length=1)
    dependency_edges: list[RepoArcDependencyEdge] = Field(default_factory=list)
    evidence_refs: list[RepoDescriptionEvidenceRef] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_register(self) -> RepoArcDependencyRegister:
        object.__setattr__(
            self,
            "repo_arc_dependency_register_id",
            _assert_non_empty_text(
                self.repo_arc_dependency_register_id, field_name="repo_arc_dependency_register_id"
            ),
        )
        object.__setattr__(
            self,
            "repo_snapshot_id",
            _assert_non_empty_text(self.repo_snapshot_id, field_name="repo_snapshot_id"),
        )
        object.__setattr__(
            self,
            "repo_snapshot_hash",
            _assert_hash(self.repo_snapshot_hash, field_name="repo_snapshot_hash"),
        )
        object.__setattr__(
            self,
            "source_set",
            _assert_sorted_unique(
                [_assert_repo_rel_path(path, field_name="source_set") for path in self.source_set],
                field_name="source_set",
            ),
        )
        object.__setattr__(
            self,
            "source_set_hash",
            _assert_hash(self.source_set_hash, field_name="source_set_hash"),
        )
        object.__setattr__(
            self,
            "register_scope",
            _assert_no_forbidden_authority_terms(self.register_scope, field_name="register_scope"),
        )
        if "repo_dependency_graph" in self.register_scope:
            raise ValueError("register_scope may not claim the later repo_dependency_graph surface")
        object.__setattr__(
            self,
            "dependency_policy_ref",
            _assert_non_empty_text(self.dependency_policy_ref, field_name="dependency_policy_ref"),
        )
        object.__setattr__(
            self,
            "dependency_policy_hash",
            _assert_hash(self.dependency_policy_hash, field_name="dependency_policy_hash"),
        )
        if self.dependency_policy_ref != V45C_DEPENDENCY_POLICY_REF:
            raise ValueError("dependency_policy_ref must bind to the v45c dependency policy")
        if self.dependency_policy_hash != compute_v45c_v102_dependency_policy_hash():
            raise ValueError("dependency_policy_hash must match bound policy content")

        evidence_by_ref = {entry.evidence_ref: entry for entry in self.evidence_refs}
        if len(evidence_by_ref) != len(self.evidence_refs):
            raise ValueError("evidence_refs evidence_ref values must be unique")
        if [entry.evidence_ref for entry in self.evidence_refs] != sorted(evidence_by_ref):
            raise ValueError("evidence_refs must be sorted lexicographically by evidence_ref")

        entries_by_id = {entry.arc_id: entry for entry in self.open_arc_entries}
        if len(entries_by_id) != len(self.open_arc_entries):
            raise ValueError("open_arc_entries arc_id values must be unique")
        if [entry.arc_id for entry in self.open_arc_entries] != sorted(entries_by_id):
            raise ValueError("open_arc_entries must be sorted lexicographically by arc_id")

        edges_by_id = {edge.edge_id: edge for edge in self.dependency_edges}
        if len(edges_by_id) != len(self.dependency_edges):
            raise ValueError("dependency_edges edge_id values must be unique")
        if [edge.edge_id for edge in self.dependency_edges] != sorted(edges_by_id):
            raise ValueError("dependency_edges must be sorted lexicographically by edge_id")

        source_set_membership = set(self.source_set)
        unresolved_hard_incoming: dict[str, list[str]] = {arc_id: [] for arc_id in entries_by_id}
        cycle_adjacency: dict[str, list[str]] = {arc_id: [] for arc_id in entries_by_id}

        for entry in self.open_arc_entries:
            row_evidence = [evidence_by_ref.get(ref) for ref in entry.supporting_evidence_refs]
            if any(item is None for item in row_evidence):
                raise ValueError(
                    "open_arc_entries supporting_evidence_refs must reference "
                    "top-level evidence_refs"
                )
            for source_ref in entry.source_artifact_refs:
                if source_ref not in source_set_membership:
                    raise ValueError("entry source_artifact_refs must resolve inside source_set")

        for edge in self.dependency_edges:
            edge_evidence = [evidence_by_ref.get(ref) for ref in edge.supporting_evidence_refs]
            if any(item is None for item in edge_evidence):
                raise ValueError(
                    "dependency_edges supporting_evidence_refs must reference "
                    "top-level evidence_refs"
                )
            for source_ref in edge.source_artifact_refs:
                if source_ref not in source_set_membership:
                    raise ValueError("edge source_artifact_refs must resolve inside source_set")
            if edge.from_arc_id not in entries_by_id or edge.to_arc_id not in entries_by_id:
                raise ValueError("dependency edges must reference known open_arc_entries arc_id")
            cycle_adjacency[edge.from_arc_id].append(edge.to_arc_id)
            if edge.dependency_strength == "hard" and edge.dependency_status == "unresolved":
                unresolved_hard_incoming[edge.to_arc_id].append(edge.from_arc_id)

        for entry in self.open_arc_entries:
            incoming = sorted(set(unresolved_hard_incoming[entry.arc_id]))
            if entry.readiness_posture == "blocked":
                if incoming != entry.blocked_by_arc_ids:
                    raise ValueError(
                        "blocked readiness_posture must match unresolved hard incoming dependencies"
                    )
            elif incoming:
                raise ValueError(
                    "ready/deferred readiness_posture may not coexist with unresolved hard blockers"
                )

        if self.cycle_posture == "cycles_forbidden":
            if self.cycle_detection_scope == "hard_unresolved_edges_only":
                scoped_adjacency = {arc_id: [] for arc_id in entries_by_id}
                for edge in self.dependency_edges:
                    if (
                        edge.dependency_strength == "hard"
                        and edge.dependency_status == "unresolved"
                    ):
                        scoped_adjacency[edge.from_arc_id].append(edge.to_arc_id)
            else:
                scoped_adjacency = cycle_adjacency

            visited: set[str] = set()
            active: set[str] = set()

            def visit(node: str) -> None:
                if node in active:
                    raise ValueError(
                        "dependency cycles are forbidden under the declared cycle posture"
                    )
                if node in visited:
                    return
                visited.add(node)
                active.add(node)
                for neighbor in sorted(scoped_adjacency[node]):
                    visit(neighbor)
                active.remove(node)

            for arc_id in sorted(scoped_adjacency):
                visit(arc_id)

        payload_without_id = self.model_dump(mode="json")
        payload_without_id.pop("repo_arc_dependency_register_id", None)
        expected_id = compute_repo_arc_dependency_register_id(payload_without_id)
        if self.repo_arc_dependency_register_id != expected_id:
            raise ValueError(
                "repo_arc_dependency_register_id must match canonical full payload hash identity"
            )
        return self


def compute_repo_schema_family_registry_id(payload_without_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_id)
    canonical_payload.setdefault("schema", REPO_SCHEMA_FAMILY_REGISTRY_SCHEMA)
    canonical_payload.pop("schema_family_registry_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"repo_schema_family_registry_{digest[:24]}"


def materialize_repo_schema_family_registry_payload(
    payload_without_registry_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_registry_id)
    payload.setdefault("schema", REPO_SCHEMA_FAMILY_REGISTRY_SCHEMA)
    payload.setdefault("classification_policy_ref", V45A_CLASSIFICATION_POLICY_REF)
    payload.setdefault("classification_policy_hash", compute_v45a_classification_policy_hash())
    payload.setdefault("reconstruction_equivalence_mode", RECONSTRUCTION_EQUIVALENCE_MODE)
    payload["schema_family_registry_id"] = compute_repo_schema_family_registry_id(payload)
    return RepoSchemaFamilyRegistry.model_validate(payload).model_dump(mode="json")


def canonicalize_repo_schema_family_registry_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return RepoSchemaFamilyRegistry.model_validate(payload).model_dump(mode="json")


def compute_repo_entity_catalog_id(payload_without_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_id)
    canonical_payload.setdefault("schema", REPO_ENTITY_CATALOG_SCHEMA)
    canonical_payload.pop("repo_entity_catalog_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"repo_entity_catalog_{digest[:24]}"


def materialize_repo_entity_catalog_payload(
    payload_without_catalog_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_catalog_id)
    payload.setdefault("schema", REPO_ENTITY_CATALOG_SCHEMA)
    payload.setdefault("entity_coverage_mode", SCHEMA_VISIBLE_ENTITY_COVERAGE_MODE)
    payload.setdefault("classification_policy_ref", V45A_CLASSIFICATION_POLICY_REF)
    payload.setdefault("classification_policy_hash", compute_v45a_classification_policy_hash())
    payload["repo_entity_catalog_id"] = compute_repo_entity_catalog_id(payload)
    return RepoEntityCatalog.model_validate(payload).model_dump(mode="json")


def canonicalize_repo_entity_catalog_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return RepoEntityCatalog.model_validate(payload).model_dump(mode="json")


def compute_repo_symbol_catalog_id(payload_without_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_id)
    canonical_payload.setdefault("schema", REPO_SYMBOL_CATALOG_SCHEMA)
    canonical_payload.pop("repo_symbol_catalog_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"repo_symbol_catalog_{digest[:24]}"


def materialize_repo_symbol_catalog_payload(
    payload_without_catalog_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_catalog_id)
    payload.setdefault("schema", REPO_SYMBOL_CATALOG_SCHEMA)
    payload["repo_symbol_catalog_id"] = compute_repo_symbol_catalog_id(payload)
    return RepoSymbolCatalog.model_validate(payload).model_dump(mode="json")


def canonicalize_repo_symbol_catalog_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return RepoSymbolCatalog.model_validate(payload).model_dump(mode="json")


def compute_repo_dependency_graph_id(payload_without_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_id)
    canonical_payload.setdefault("schema", REPO_DEPENDENCY_GRAPH_SCHEMA)
    canonical_payload.pop("repo_dependency_graph_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"repo_dependency_graph_{digest[:24]}"


def materialize_repo_dependency_graph_payload(
    payload_without_graph_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_graph_id)
    payload.setdefault("schema", REPO_DEPENDENCY_GRAPH_SCHEMA)
    payload["repo_dependency_graph_id"] = compute_repo_dependency_graph_id(payload)
    return RepoDependencyGraph.model_validate(payload).model_dump(mode="json")


def canonicalize_repo_dependency_graph_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return RepoDependencyGraph.model_validate(payload).model_dump(mode="json")


def compute_repo_test_intent_matrix_id(payload_without_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_id)
    canonical_payload.setdefault("schema", REPO_TEST_INTENT_MATRIX_SCHEMA)
    canonical_payload.pop("repo_test_intent_matrix_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"repo_test_intent_matrix_{digest[:24]}"


def materialize_repo_test_intent_matrix_payload(
    payload_without_matrix_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_matrix_id)
    payload.setdefault("schema", REPO_TEST_INTENT_MATRIX_SCHEMA)
    payload["repo_test_intent_matrix_id"] = compute_repo_test_intent_matrix_id(payload)
    return RepoTestIntentMatrix.model_validate(payload).model_dump(mode="json")


def canonicalize_repo_test_intent_matrix_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return RepoTestIntentMatrix.model_validate(payload).model_dump(mode="json")


def compute_repo_optimization_register_id(payload_without_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_id)
    canonical_payload.setdefault("schema", REPO_OPTIMIZATION_REGISTER_SCHEMA)
    canonical_payload.pop("repo_optimization_register_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"repo_optimization_register_{digest[:24]}"


def materialize_repo_optimization_register_payload(
    payload_without_register_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_register_id)
    payload.setdefault("schema", REPO_OPTIMIZATION_REGISTER_SCHEMA)
    payload["repo_optimization_register_id"] = compute_repo_optimization_register_id(payload)
    return RepoOptimizationRegister.model_validate(payload).model_dump(mode="json")


def canonicalize_repo_optimization_register_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return RepoOptimizationRegister.model_validate(payload).model_dump(mode="json")


def compute_repo_arc_dependency_register_v1_id(payload_without_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_id)
    canonical_payload.setdefault("schema", REPO_ARC_DEPENDENCY_REGISTER_V1_SCHEMA)
    canonical_payload.pop("repo_arc_dependency_register_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"repo_arc_dependency_register_{digest[:24]}"


def materialize_repo_arc_dependency_register_v1_payload(
    payload_without_register_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_register_id)
    payload.setdefault("schema", REPO_ARC_DEPENDENCY_REGISTER_V1_SCHEMA)
    payload.setdefault("dependency_policy_ref", V45C_DEPENDENCY_POLICY_REF)
    payload.setdefault("dependency_policy_hash", compute_v45c_v100_dependency_policy_hash())
    payload["repo_arc_dependency_register_id"] = compute_repo_arc_dependency_register_v1_id(payload)
    return RepoArcDependencyRegisterV1.model_validate(payload).model_dump(mode="json")


def canonicalize_repo_arc_dependency_register_v1_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return RepoArcDependencyRegisterV1.model_validate(payload).model_dump(mode="json")


def compute_repo_arc_dependency_register_id(payload_without_id: dict[str, Any]) -> str:
    canonical_payload = deepcopy(payload_without_id)
    canonical_payload.setdefault("schema", REPO_ARC_DEPENDENCY_REGISTER_SCHEMA)
    canonical_payload.pop("repo_arc_dependency_register_id", None)
    digest = sha256_canonical_json(canonical_payload)
    return f"repo_arc_dependency_register_{digest[:24]}"


def materialize_repo_arc_dependency_register_payload(
    payload_without_register_id: dict[str, Any],
) -> dict[str, Any]:
    payload = deepcopy(payload_without_register_id)
    payload.setdefault("schema", REPO_ARC_DEPENDENCY_REGISTER_SCHEMA)
    payload.setdefault("dependency_policy_ref", V45C_DEPENDENCY_POLICY_REF)
    payload.setdefault("dependency_policy_hash", compute_v45c_v102_dependency_policy_hash())
    payload["repo_arc_dependency_register_id"] = compute_repo_arc_dependency_register_id(payload)
    return RepoArcDependencyRegister.model_validate(payload).model_dump(mode="json")


def canonicalize_repo_arc_dependency_register_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return RepoArcDependencyRegister.model_validate(payload).model_dump(mode="json")


def representative_schema_keys() -> tuple[str, ...]:
    return _RECONSTRUCTION_REPRESENTATIVE_SCHEMA_KEYS
