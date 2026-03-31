from __future__ import annotations

import re
from copy import deepcopy
from pathlib import PurePosixPath
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import canonical_json, sha256_canonical_json

REPO_SCHEMA_FAMILY_REGISTRY_SCHEMA = "repo_schema_family_registry@1"
REPO_ENTITY_CATALOG_SCHEMA = "repo_entity_catalog@1"
REPO_ARC_DEPENDENCY_REGISTER_SCHEMA = "repo_arc_dependency_register@1"
V45A_V99_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS99.md#v99-continuation-contract-machine-checkable"
)
V45A_CLASSIFICATION_POLICY_REF = (
    "docs/DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md#v45a-role-form-classification-policy"
)
V45C_V100_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS100.md#v100-continuation-contract-machine-checkable"
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


def _v45c_dependency_policy_payload() -> dict[str, Any]:
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


def compute_v45c_dependency_policy_hash() -> str:
    return sha256_canonical_json(_v45c_dependency_policy_payload())


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


class RepoArcDependencyRegisterEntry(BaseModel):
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
    supports_all_three_way_claim: bool = False
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

    schema: Literal["repo_arc_dependency_register@1"] = REPO_ARC_DEPENDENCY_REGISTER_SCHEMA
    repo_arc_dependency_register_id: str
    repo_snapshot_id: str
    repo_snapshot_hash: str
    snapshot_validity_posture: SnapshotValidityPosture
    register_scope: str
    dependency_policy_ref: str
    dependency_policy_hash: str
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
            "register_scope",
            _assert_no_forbidden_authority_terms(
                self.register_scope, field_name="register_scope"
            ),
        )
        object.__setattr__(
            self,
            "dependency_policy_ref",
            _assert_non_empty_text(
                self.dependency_policy_ref, field_name="dependency_policy_ref"
            ),
        )
        object.__setattr__(
            self,
            "dependency_policy_hash",
            _assert_hash(self.dependency_policy_hash, field_name="dependency_policy_hash"),
        )
        if self.dependency_policy_ref != V45C_DEPENDENCY_POLICY_REF:
            raise ValueError("dependency_policy_ref must bind to the v45c dependency policy")
        if self.dependency_policy_hash != compute_v45c_dependency_policy_hash():
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
    payload.setdefault("dependency_policy_hash", compute_v45c_dependency_policy_hash())
    payload["repo_arc_dependency_register_id"] = compute_repo_arc_dependency_register_id(payload)
    return RepoArcDependencyRegister.model_validate(payload).model_dump(mode="json")


def canonicalize_repo_arc_dependency_register_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return RepoArcDependencyRegister.model_validate(payload).model_dump(mode="json")


def representative_schema_keys() -> tuple[str, ...]:
    return _RECONSTRUCTION_REPRESENTATIVE_SCHEMA_KEYS
