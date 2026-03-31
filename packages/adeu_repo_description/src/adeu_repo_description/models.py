from __future__ import annotations

from copy import deepcopy
from pathlib import PurePosixPath
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import canonical_json, sha256_canonical_json

REPO_SCHEMA_FAMILY_REGISTRY_SCHEMA = "repo_schema_family_registry@1"
REPO_ENTITY_CATALOG_SCHEMA = "repo_entity_catalog@1"
V45A_V99_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS99.md#v99-continuation-contract-machine-checkable"
)
V45A_CLASSIFICATION_POLICY_REF = (
    "docs/DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md#v45a-role-form-classification-policy"
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
]
EntityCoverageMode = Literal["bounded_schema_visible_slice"]
ReconstructionEquivalenceMode = Literal["canonical_normalized_semantic_equivalence"]

_STRONGER_PRECEDENCE_EVIDENCE_KINDS: tuple[EvidenceKind, ...] = (
    "structural_signature_evidence",
    "semantic_function_cue_evidence",
    "governance_cue_evidence",
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
    return lowered.replace("-", "_").replace(" ", "_")


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


def representative_schema_keys() -> tuple[str, ...]:
    return _RECONSTRUCTION_REPRESENTATIVE_SCHEMA_KEYS
