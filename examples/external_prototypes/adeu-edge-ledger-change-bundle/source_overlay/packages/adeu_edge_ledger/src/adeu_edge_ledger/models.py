from __future__ import annotations

from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import canonical_json, sha256_canonical_json

ADEU_EDGE_CLASS_CATALOG_SCHEMA = "adeu_edge_class_catalog@1"
ADEU_EDGE_PROBE_TEMPLATE_CATALOG_SCHEMA = "adeu_edge_probe_template_catalog@1"
ADEU_SYMBOL_EDGE_APPLICABILITY_FRAME_SCHEMA = "adeu_symbol_edge_applicability_frame@1"
ADEU_SYMBOL_EDGE_ADJUDICATION_LEDGER_SCHEMA = "adeu_symbol_edge_adjudication_ledger@1"
ADEU_EDGE_TAXONOMY_REVISION_JUDGMENT_SCHEMA = "adeu_edge_taxonomy_revision_judgment@1"

MODEL_CONFIG = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

TaxonomyNodeKind = Literal["family", "subfamily", "archetype"]
TaxonomyNodeLifecycle = Literal["candidate", "stabilized", "split", "merged", "deprecated"]
ProbeStrategyKind = Literal[
    "absence_matrix",
    "shape_matrix",
    "boundary_partition",
    "ordering_permutation",
    "branch_partition",
    "state_sequence",
    "round_trip",
    "hash_consistency",
    "cross_field_invariant",
    "dependency_boundary",
    "fail_closed_rejection",
    "manual_adjudication",
]
ProbeExecutionPosture = Literal["example_tests", "property_based", "metamorphic", "review_only"]
EpistemicPosture = Literal[
    "observed",
    "derived_deterministically",
    "inferred_heuristically",
    "adjudicated",
    "settled",
]
ApplicabilityStatus = Literal["applicable", "not_applicable", "underdetermined"]
AdjudicationStatus = Literal[
    "not_applicable",
    "applicable_unchecked",
    "covered_by_existing_tests",
    "checked_no_witness_found",
    "bounded_safe_by_structure",
    "witness_found",
    "underdetermined",
    "deferred",
]
DistinctnessPosture = Literal[
    "same",
    "attribute_refinement_only",
    "adjacent_but_representable",
    "distinct",
]
ReusePosture = Literal["single_symbol", "multi_symbol_candidate", "recurrent_pattern"]
TaxonomyRevisionDecision = Literal[
    "instance_of_existing_class",
    "specialize_under_existing_class",
    "split_existing_class",
    "new_sibling_under_existing_parent",
    "new_intermediate_node",
    "new_top_level_family",
    "defer_candidate",
]
SymbolKind = Literal["class", "function", "method", "local_function"]


def _assert_non_empty_text(value: str, *, field_name: str) -> str:
    normalized = value.strip()
    if not normalized:
        raise ValueError(f"{field_name} must be non-empty")
    return normalized


def _assert_sorted_unique_texts(values: list[str], *, field_name: str) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if normalized != sorted(normalized):
        raise ValueError(f"{field_name} must be sorted")
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must be unique")
    return normalized


def _assert_repo_rel_path(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name).replace("\\", "/")
    if normalized.startswith("/"):
        raise ValueError(f"{field_name} must be repo-relative")
    parts = normalized.split("/")
    if any(part in {"", ".", ".."} for part in parts):
        raise ValueError(f"{field_name} must not contain empty, '.' or '..' segments")
    return normalized


def _assert_hash(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    if len(normalized) != 64 or any(ch not in "0123456789abcdef" for ch in normalized):
        raise ValueError(f"{field_name} must be a lowercase 64-character sha256 hex digest")
    return normalized


def _assert_catalog_ref(value: str, *, field_name: str, prefix: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    if not normalized.startswith(prefix):
        raise ValueError(f"{field_name} must use the {prefix} prefix")
    return normalized


def _assert_edge_class_ref(value: str, *, field_name: str, expected_kind: TaxonomyNodeKind | None = None) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    prefix = "edge_class:"
    if not normalized.startswith(prefix):
        raise ValueError(f"{field_name} must use the edge_class: prefix")
    remainder = normalized[len(prefix) :]
    segments = remainder.split("/")
    if any(not segment or not segment.replace("_", "").isalnum() or not segment[0].isalpha() for segment in segments):
        raise ValueError(f"{field_name} must use slash-separated lowercase slug segments")
    if expected_kind is not None:
        expected_segment_count = {"family": 1, "subfamily": 2, "archetype": 3}[expected_kind]
        if len(segments) != expected_segment_count:
            raise ValueError(
                f"{field_name} must carry {expected_segment_count} path segments for {expected_kind}"
            )
    elif len(segments) not in {1, 2, 3}:
        raise ValueError(f"{field_name} must carry between 1 and 3 path segments")
    return normalized


def _assert_probe_template_ref(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    prefix = "probe:"
    if not normalized.startswith(prefix):
        raise ValueError(f"{field_name} must use the probe: prefix")
    slug = normalized[len(prefix) :]
    if not slug or not slug.replace("_", "").isalnum() or not slug[0].isalpha():
        raise ValueError(f"{field_name} must use one lowercase slug after probe:")
    return normalized


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


def _assert_symbol_id(
    value: str,
    *,
    field_name: str,
    module_path: str | None = None,
    qualname: str | None = None,
    symbol_kind: SymbolKind | None = None,
) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    prefix = "symbol:"
    if not normalized.startswith(prefix):
        raise ValueError(f"{field_name} must use the symbol: prefix")
    if module_path is not None and qualname is not None and symbol_kind is not None:
        expected = compute_symbol_id(
            module_path=module_path,
            qualname=qualname,
            symbol_kind=symbol_kind,
        )
        if normalized != expected:
            raise ValueError(f"{field_name} must match canonical module_path + qualname + symbol_kind")
    return normalized


def compute_symbol_id(*, module_path: str, qualname: str, symbol_kind: SymbolKind) -> str:
    normalized_module_path = _assert_repo_rel_path(module_path, field_name="module_path")
    normalized_qualname = _assert_non_empty_text(qualname, field_name="qualname")
    return f"symbol:{normalized_module_path}:{normalized_qualname}:{symbol_kind}"


class EdgeClassNode(BaseModel):
    model_config = MODEL_CONFIG

    edge_class_ref: str
    parent_edge_class_ref: str | None = None
    node_kind: TaxonomyNodeKind
    short_label: str
    summary: str
    required_cue_tags: list[str] = Field(default_factory=list)
    supporting_cue_tags: list[str] = Field(default_factory=list)
    structural_safety_cue_tags: list[str] = Field(default_factory=list)
    test_token_tags: list[str] = Field(default_factory=list)
    default_probe_template_refs: list[str] = Field(default_factory=list)
    lifecycle_posture: TaxonomyNodeLifecycle = "stabilized"

    @model_validator(mode="after")
    def _validate(self) -> "EdgeClassNode":
        object.__setattr__(
            self,
            "edge_class_ref",
            _assert_edge_class_ref(
                self.edge_class_ref,
                field_name="edge_class_ref",
                expected_kind=self.node_kind,
            ),
        )
        if self.parent_edge_class_ref is not None:
            expected_parent_kind: TaxonomyNodeKind = {
                "family": "family",
                "subfamily": "family",
                "archetype": "subfamily",
            }[self.node_kind]
            if self.node_kind == "family":
                raise ValueError("family node must not carry parent_edge_class_ref")
            object.__setattr__(
                self,
                "parent_edge_class_ref",
                _assert_edge_class_ref(
                    self.parent_edge_class_ref,
                    field_name="parent_edge_class_ref",
                    expected_kind=expected_parent_kind,
                ),
            )
        elif self.node_kind != "family":
            raise ValueError("subfamily and archetype nodes must carry parent_edge_class_ref")
        for field_name in ("short_label", "summary"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in (
            "required_cue_tags",
            "supporting_cue_tags",
            "structural_safety_cue_tags",
            "test_token_tags",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique_texts(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "default_probe_template_refs",
            [
                _assert_probe_template_ref(value, field_name="default_probe_template_refs")
                for value in _assert_sorted_unique_texts(
                    self.default_probe_template_refs,
                    field_name="default_probe_template_refs",
                )
            ],
        )
        return self


class EdgeClassCatalog(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_EDGE_CLASS_CATALOG_SCHEMA] = Field(
        default=ADEU_EDGE_CLASS_CATALOG_SCHEMA,
        alias="schema",
    )
    catalog_id: str
    catalog_name: str
    catalog_version: str
    catalog_posture: str
    nodes: list[EdgeClassNode] = Field(min_length=1)
    catalog_hash: str

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "EdgeClassCatalog":
        for field_name in ("catalog_id", "catalog_name", "catalog_version", "catalog_posture"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(self, "catalog_hash", _assert_hash(self.catalog_hash, field_name="catalog_hash"))
        nodes_by_ref = {node.edge_class_ref: node for node in self.nodes}
        if len(nodes_by_ref) != len(self.nodes):
            raise ValueError("nodes edge_class_ref values must be unique")
        if [node.edge_class_ref for node in self.nodes] != sorted(nodes_by_ref):
            raise ValueError("nodes must be sorted lexicographically by edge_class_ref")
        for node in self.nodes:
            if node.parent_edge_class_ref is not None and node.parent_edge_class_ref not in nodes_by_ref:
                raise ValueError("parent_edge_class_ref must resolve inside nodes")
            if node.node_kind == "subfamily":
                assert node.parent_edge_class_ref is not None
                if nodes_by_ref[node.parent_edge_class_ref].node_kind != "family":
                    raise ValueError("subfamily parent_edge_class_ref must point to a family node")
            if node.node_kind == "archetype":
                assert node.parent_edge_class_ref is not None
                if nodes_by_ref[node.parent_edge_class_ref].node_kind != "subfamily":
                    raise ValueError("archetype parent_edge_class_ref must point to a subfamily node")
                if not node.default_probe_template_refs:
                    raise ValueError("archetype nodes must carry default_probe_template_refs")
        expected_catalog_hash = sha256_canonical_json(
            {
                "schema": self.schema,
                "catalog_name": self.catalog_name,
                "catalog_version": self.catalog_version,
                "catalog_posture": self.catalog_posture,
                "nodes": [node.model_dump(mode="json", exclude_none=True) for node in self.nodes],
            }
        )
        if self.catalog_hash != expected_catalog_hash:
            raise ValueError("catalog_hash must match canonical catalog payload")
        expected_catalog_id = compute_edge_class_catalog_id(
            {
                "schema": self.schema,
                "catalog_name": self.catalog_name,
                "catalog_version": self.catalog_version,
                "catalog_posture": self.catalog_posture,
                "nodes": [node.model_dump(mode="json", exclude_none=True) for node in self.nodes],
                "catalog_hash": self.catalog_hash,
            }
        )
        if self.catalog_id != expected_catalog_id:
            raise ValueError("catalog_id must match canonical catalog identity")
        return self


class EdgeProbeTemplate(BaseModel):
    model_config = MODEL_CONFIG

    probe_template_ref: str
    strategy_kind: ProbeStrategyKind
    execution_postures: list[ProbeExecutionPosture] = Field(min_length=1)
    short_label: str
    summary: str
    suited_edge_class_refs: list[str] = Field(min_length=1)
    required_signal_tags: list[str] = Field(default_factory=list)
    lifecycle_posture: TaxonomyNodeLifecycle = "stabilized"

    @model_validator(mode="after")
    def _validate(self) -> "EdgeProbeTemplate":
        object.__setattr__(
            self,
            "probe_template_ref",
            _assert_probe_template_ref(self.probe_template_ref, field_name="probe_template_ref"),
        )
        for field_name in ("short_label", "summary"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "execution_postures",
            list(_assert_sorted_unique_texts(self.execution_postures, field_name="execution_postures")),
        )
        object.__setattr__(
            self,
            "suited_edge_class_refs",
            [
                _assert_edge_class_ref(value, field_name="suited_edge_class_refs", expected_kind="archetype")
                for value in _assert_sorted_unique_texts(
                    self.suited_edge_class_refs,
                    field_name="suited_edge_class_refs",
                )
            ],
        )
        object.__setattr__(
            self,
            "required_signal_tags",
            _assert_sorted_unique_texts(self.required_signal_tags, field_name="required_signal_tags"),
        )
        return self


class EdgeProbeTemplateCatalog(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_EDGE_PROBE_TEMPLATE_CATALOG_SCHEMA] = Field(
        default=ADEU_EDGE_PROBE_TEMPLATE_CATALOG_SCHEMA,
        alias="schema",
    )
    catalog_id: str
    catalog_name: str
    catalog_version: str
    bound_edge_class_catalog_ref: str
    probe_templates: list[EdgeProbeTemplate] = Field(min_length=1)
    catalog_hash: str

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "EdgeProbeTemplateCatalog":
        for field_name in ("catalog_id", "catalog_name", "catalog_version"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(self, "catalog_hash", _assert_hash(self.catalog_hash, field_name="catalog_hash"))
        object.__setattr__(
            self,
            "bound_edge_class_catalog_ref",
            _assert_catalog_ref(
                self.bound_edge_class_catalog_ref,
                field_name="bound_edge_class_catalog_ref",
                prefix="edge_class_catalog:",
            ),
        )
        probes_by_ref = {probe.probe_template_ref: probe for probe in self.probe_templates}
        if len(probes_by_ref) != len(self.probe_templates):
            raise ValueError("probe_templates probe_template_ref values must be unique")
        if [probe.probe_template_ref for probe in self.probe_templates] != sorted(probes_by_ref):
            raise ValueError("probe_templates must be sorted lexicographically by probe_template_ref")
        expected_catalog_hash = sha256_canonical_json(
            {
                "schema": self.schema,
                "catalog_name": self.catalog_name,
                "catalog_version": self.catalog_version,
                "bound_edge_class_catalog_ref": self.bound_edge_class_catalog_ref,
                "probe_templates": [
                    probe.model_dump(mode="json", exclude_none=True)
                    for probe in self.probe_templates
                ],
            }
        )
        if self.catalog_hash != expected_catalog_hash:
            raise ValueError("catalog_hash must match canonical probe catalog payload")
        expected_catalog_id = compute_edge_probe_template_catalog_id(
            {
                "schema": self.schema,
                "catalog_name": self.catalog_name,
                "catalog_version": self.catalog_version,
                "bound_edge_class_catalog_ref": self.bound_edge_class_catalog_ref,
                "probe_templates": [
                    probe.model_dump(mode="json", exclude_none=True)
                    for probe in self.probe_templates
                ],
                "catalog_hash": self.catalog_hash,
            }
        )
        if self.catalog_id != expected_catalog_id:
            raise ValueError("catalog_id must match canonical probe catalog identity")
        return self


class SymbolEdgeApplicabilityRow(BaseModel):
    model_config = MODEL_CONFIG

    edge_class_ref: str
    applicability_status: ApplicabilityStatus
    epistemic_posture: EpistemicPosture
    matched_cue_tags: list[str] = Field(default_factory=list)
    concrete_binding_refs: list[str] = Field(default_factory=list)
    suggested_probe_template_refs: list[str] = Field(default_factory=list)
    rationale: str

    @model_validator(mode="after")
    def _validate(self) -> "SymbolEdgeApplicabilityRow":
        object.__setattr__(
            self,
            "edge_class_ref",
            _assert_edge_class_ref(self.edge_class_ref, field_name="edge_class_ref", expected_kind="archetype"),
        )
        object.__setattr__(
            self,
            "matched_cue_tags",
            _assert_sorted_unique_texts(self.matched_cue_tags, field_name="matched_cue_tags"),
        )
        object.__setattr__(
            self,
            "concrete_binding_refs",
            _assert_sorted_unique_texts(
                self.concrete_binding_refs,
                field_name="concrete_binding_refs",
            ),
        )
        object.__setattr__(
            self,
            "suggested_probe_template_refs",
            [
                _assert_probe_template_ref(value, field_name="suggested_probe_template_refs")
                for value in _assert_sorted_unique_texts(
                    self.suggested_probe_template_refs,
                    field_name="suggested_probe_template_refs",
                )
            ],
        )
        object.__setattr__(
            self,
            "rationale",
            _assert_non_empty_text(self.rationale, field_name="rationale"),
        )
        return self


class SymbolEdgeApplicabilityFrame(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_SYMBOL_EDGE_APPLICABILITY_FRAME_SCHEMA] = Field(
        default=ADEU_SYMBOL_EDGE_APPLICABILITY_FRAME_SCHEMA,
        alias="schema",
    )
    frame_id: str
    bound_edge_class_catalog_ref: str
    bound_probe_template_catalog_ref: str
    scope_manifest_ref: str
    census_hash: str
    audit_hash: str
    symbol_id: str
    module_path: str
    qualname: str
    symbol_kind: SymbolKind
    frame_posture: str
    applicability_rows: list[SymbolEdgeApplicabilityRow] = Field(min_length=1)
    frame_hash: str

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "SymbolEdgeApplicabilityFrame":
        for field_name in (
            "frame_id",
            "scope_manifest_ref",
            "qualname",
            "frame_posture",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "bound_edge_class_catalog_ref",
            _assert_catalog_ref(
                self.bound_edge_class_catalog_ref,
                field_name="bound_edge_class_catalog_ref",
                prefix="edge_class_catalog:",
            ),
        )
        object.__setattr__(
            self,
            "bound_probe_template_catalog_ref",
            _assert_catalog_ref(
                self.bound_probe_template_catalog_ref,
                field_name="bound_probe_template_catalog_ref",
                prefix="edge_probe_template_catalog:",
            ),
        )
        object.__setattr__(
            self,
            "module_path",
            _assert_repo_rel_path(self.module_path, field_name="module_path"),
        )
        object.__setattr__(
            self,
            "symbol_id",
            _assert_symbol_id(
                self.symbol_id,
                field_name="symbol_id",
                module_path=self.module_path,
                qualname=self.qualname,
                symbol_kind=self.symbol_kind,
            ),
        )
        object.__setattr__(self, "census_hash", _assert_hash(self.census_hash, field_name="census_hash"))
        object.__setattr__(self, "audit_hash", _assert_hash(self.audit_hash, field_name="audit_hash"))
        object.__setattr__(self, "frame_hash", _assert_hash(self.frame_hash, field_name="frame_hash"))
        rows_by_ref = {row.edge_class_ref: row for row in self.applicability_rows}
        if len(rows_by_ref) != len(self.applicability_rows):
            raise ValueError("applicability_rows edge_class_ref values must be unique")
        if [row.edge_class_ref for row in self.applicability_rows] != sorted(rows_by_ref):
            raise ValueError("applicability_rows must be sorted lexicographically by edge_class_ref")
        expected_frame_hash = sha256_canonical_json(
            {
                "schema": self.schema,
                "bound_edge_class_catalog_ref": self.bound_edge_class_catalog_ref,
                "bound_probe_template_catalog_ref": self.bound_probe_template_catalog_ref,
                "scope_manifest_ref": self.scope_manifest_ref,
                "census_hash": self.census_hash,
                "audit_hash": self.audit_hash,
                "symbol_id": self.symbol_id,
                "module_path": self.module_path,
                "qualname": self.qualname,
                "symbol_kind": self.symbol_kind,
                "frame_posture": self.frame_posture,
                "applicability_rows": [
                    row.model_dump(mode="json", exclude_none=True)
                    for row in self.applicability_rows
                ],
            }
        )
        if self.frame_hash != expected_frame_hash:
            raise ValueError("frame_hash must match canonical applicability frame payload")
        expected_frame_id = compute_symbol_edge_applicability_frame_id(
            {
                "schema": self.schema,
                "bound_edge_class_catalog_ref": self.bound_edge_class_catalog_ref,
                "bound_probe_template_catalog_ref": self.bound_probe_template_catalog_ref,
                "scope_manifest_ref": self.scope_manifest_ref,
                "census_hash": self.census_hash,
                "audit_hash": self.audit_hash,
                "symbol_id": self.symbol_id,
                "module_path": self.module_path,
                "qualname": self.qualname,
                "symbol_kind": self.symbol_kind,
                "frame_posture": self.frame_posture,
                "applicability_rows": [
                    row.model_dump(mode="json", exclude_none=True)
                    for row in self.applicability_rows
                ],
                "frame_hash": self.frame_hash,
            }
        )
        if self.frame_id != expected_frame_id:
            raise ValueError("frame_id must match canonical applicability frame identity")
        return self


class SymbolEdgeAdjudicationRow(BaseModel):
    model_config = MODEL_CONFIG

    edge_class_ref: str
    source_applicability_status: ApplicabilityStatus
    adjudication_status: AdjudicationStatus
    status_posture: EpistemicPosture
    matched_cue_tags: list[str] = Field(default_factory=list)
    supporting_test_refs: list[str] = Field(default_factory=list)
    supporting_evidence_refs: list[str] = Field(default_factory=list)
    suggested_probe_template_refs: list[str] = Field(default_factory=list)
    witness_summary: str | None = None
    rationale: str

    @model_validator(mode="after")
    def _validate(self) -> "SymbolEdgeAdjudicationRow":
        object.__setattr__(
            self,
            "edge_class_ref",
            _assert_edge_class_ref(self.edge_class_ref, field_name="edge_class_ref", expected_kind="archetype"),
        )
        object.__setattr__(
            self,
            "matched_cue_tags",
            _assert_sorted_unique_texts(self.matched_cue_tags, field_name="matched_cue_tags"),
        )
        object.__setattr__(
            self,
            "supporting_test_refs",
            [
                _assert_test_ref(value, field_name="supporting_test_refs")
                for value in _assert_sorted_unique_texts(
                    self.supporting_test_refs,
                    field_name="supporting_test_refs",
                )
            ],
        )
        object.__setattr__(
            self,
            "supporting_evidence_refs",
            _assert_sorted_unique_texts(
                self.supporting_evidence_refs,
                field_name="supporting_evidence_refs",
            ),
        )
        object.__setattr__(
            self,
            "suggested_probe_template_refs",
            [
                _assert_probe_template_ref(value, field_name="suggested_probe_template_refs")
                for value in _assert_sorted_unique_texts(
                    self.suggested_probe_template_refs,
                    field_name="suggested_probe_template_refs",
                )
            ],
        )
        if self.witness_summary is not None:
            object.__setattr__(
                self,
                "witness_summary",
                _assert_non_empty_text(self.witness_summary, field_name="witness_summary"),
            )
        object.__setattr__(
            self,
            "rationale",
            _assert_non_empty_text(self.rationale, field_name="rationale"),
        )
        if self.adjudication_status == "not_applicable" and self.source_applicability_status != "not_applicable":
            raise ValueError("not_applicable adjudication_status requires source_applicability_status = not_applicable")
        if self.adjudication_status == "witness_found" and self.witness_summary is None:
            raise ValueError("witness_found requires witness_summary")
        if self.adjudication_status == "covered_by_existing_tests" and not self.supporting_test_refs:
            raise ValueError("covered_by_existing_tests requires supporting_test_refs")
        return self


class SymbolEdgeAdjudicationLedger(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_SYMBOL_EDGE_ADJUDICATION_LEDGER_SCHEMA] = Field(
        default=ADEU_SYMBOL_EDGE_ADJUDICATION_LEDGER_SCHEMA,
        alias="schema",
    )
    ledger_id: str
    bound_edge_class_catalog_ref: str
    bound_probe_template_catalog_ref: str
    scope_manifest_ref: str
    census_hash: str
    audit_hash: str
    symbol_id: str
    module_path: str
    qualname: str
    symbol_kind: SymbolKind
    bound_applicability_frame_ref: str
    ledger_posture: str
    adjudication_rows: list[SymbolEdgeAdjudicationRow] = Field(min_length=1)
    ledger_hash: str

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "SymbolEdgeAdjudicationLedger":
        for field_name in (
            "ledger_id",
            "scope_manifest_ref",
            "qualname",
            "bound_applicability_frame_ref",
            "ledger_posture",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "bound_edge_class_catalog_ref",
            _assert_catalog_ref(
                self.bound_edge_class_catalog_ref,
                field_name="bound_edge_class_catalog_ref",
                prefix="edge_class_catalog:",
            ),
        )
        object.__setattr__(
            self,
            "bound_probe_template_catalog_ref",
            _assert_catalog_ref(
                self.bound_probe_template_catalog_ref,
                field_name="bound_probe_template_catalog_ref",
                prefix="edge_probe_template_catalog:",
            ),
        )
        object.__setattr__(
            self,
            "module_path",
            _assert_repo_rel_path(self.module_path, field_name="module_path"),
        )
        object.__setattr__(
            self,
            "symbol_id",
            _assert_symbol_id(
                self.symbol_id,
                field_name="symbol_id",
                module_path=self.module_path,
                qualname=self.qualname,
                symbol_kind=self.symbol_kind,
            ),
        )
        object.__setattr__(self, "census_hash", _assert_hash(self.census_hash, field_name="census_hash"))
        object.__setattr__(self, "audit_hash", _assert_hash(self.audit_hash, field_name="audit_hash"))
        object.__setattr__(self, "ledger_hash", _assert_hash(self.ledger_hash, field_name="ledger_hash"))
        rows_by_ref = {row.edge_class_ref: row for row in self.adjudication_rows}
        if len(rows_by_ref) != len(self.adjudication_rows):
            raise ValueError("adjudication_rows edge_class_ref values must be unique")
        if [row.edge_class_ref for row in self.adjudication_rows] != sorted(rows_by_ref):
            raise ValueError("adjudication_rows must be sorted lexicographically by edge_class_ref")
        expected_ledger_hash = sha256_canonical_json(
            {
                "schema": self.schema,
                "bound_edge_class_catalog_ref": self.bound_edge_class_catalog_ref,
                "bound_probe_template_catalog_ref": self.bound_probe_template_catalog_ref,
                "scope_manifest_ref": self.scope_manifest_ref,
                "census_hash": self.census_hash,
                "audit_hash": self.audit_hash,
                "symbol_id": self.symbol_id,
                "module_path": self.module_path,
                "qualname": self.qualname,
                "symbol_kind": self.symbol_kind,
                "bound_applicability_frame_ref": self.bound_applicability_frame_ref,
                "ledger_posture": self.ledger_posture,
                "adjudication_rows": [
                    row.model_dump(mode="json", exclude_none=True)
                    for row in self.adjudication_rows
                ],
            }
        )
        if self.ledger_hash != expected_ledger_hash:
            raise ValueError("ledger_hash must match canonical adjudication ledger payload")
        expected_ledger_id = compute_symbol_edge_adjudication_ledger_id(
            {
                "schema": self.schema,
                "bound_edge_class_catalog_ref": self.bound_edge_class_catalog_ref,
                "bound_probe_template_catalog_ref": self.bound_probe_template_catalog_ref,
                "scope_manifest_ref": self.scope_manifest_ref,
                "census_hash": self.census_hash,
                "audit_hash": self.audit_hash,
                "symbol_id": self.symbol_id,
                "module_path": self.module_path,
                "qualname": self.qualname,
                "symbol_kind": self.symbol_kind,
                "bound_applicability_frame_ref": self.bound_applicability_frame_ref,
                "ledger_posture": self.ledger_posture,
                "adjudication_rows": [
                    row.model_dump(mode="json", exclude_none=True)
                    for row in self.adjudication_rows
                ],
                "ledger_hash": self.ledger_hash,
            }
        )
        if self.ledger_id != expected_ledger_id:
            raise ValueError("ledger_id must match canonical adjudication ledger identity")
        return self


class EdgeTaxonomyRevisionJudgment(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_EDGE_TAXONOMY_REVISION_JUDGMENT_SCHEMA] = Field(
        default=ADEU_EDGE_TAXONOMY_REVISION_JUDGMENT_SCHEMA,
        alias="schema",
    )
    judgment_id: str
    bound_edge_class_catalog_ref: str
    candidate_label: str
    nearest_existing_edge_class_refs: list[str] = Field(min_length=1)
    observed_symbol_ids: list[str] = Field(min_length=1)
    applicability_cue_tags: list[str] = Field(default_factory=list)
    probe_signature_tags: list[str] = Field(default_factory=list)
    applicability_pattern_distinctness: DistinctnessPosture
    probe_pattern_distinctness: DistinctnessPosture
    representable_without_information_loss: bool
    reuse_posture: ReusePosture
    evidence_count: int
    decision: TaxonomyRevisionDecision
    proposed_parent_edge_class_ref: str | None = None
    proposed_edge_class_ref: str | None = None
    proposed_lifecycle_posture: TaxonomyNodeLifecycle
    judgment_posture: EpistemicPosture
    rationale: str
    judgment_hash: str

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "EdgeTaxonomyRevisionJudgment":
        for field_name in ("judgment_id", "candidate_label", "rationale"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "bound_edge_class_catalog_ref",
            _assert_catalog_ref(
                self.bound_edge_class_catalog_ref,
                field_name="bound_edge_class_catalog_ref",
                prefix="edge_class_catalog:",
            ),
        )
        object.__setattr__(
            self,
            "nearest_existing_edge_class_refs",
            [
                _assert_edge_class_ref(value, field_name="nearest_existing_edge_class_refs")
                for value in _assert_sorted_unique_texts(
                    self.nearest_existing_edge_class_refs,
                    field_name="nearest_existing_edge_class_refs",
                )
            ],
        )
        object.__setattr__(
            self,
            "observed_symbol_ids",
            _assert_sorted_unique_texts(self.observed_symbol_ids, field_name="observed_symbol_ids"),
        )
        object.__setattr__(
            self,
            "applicability_cue_tags",
            _assert_sorted_unique_texts(
                self.applicability_cue_tags,
                field_name="applicability_cue_tags",
            ),
        )
        object.__setattr__(
            self,
            "probe_signature_tags",
            _assert_sorted_unique_texts(
                self.probe_signature_tags,
                field_name="probe_signature_tags",
            ),
        )
        if self.proposed_parent_edge_class_ref is not None:
            object.__setattr__(
                self,
                "proposed_parent_edge_class_ref",
                _assert_edge_class_ref(
                    self.proposed_parent_edge_class_ref,
                    field_name="proposed_parent_edge_class_ref",
                ),
            )
        if self.proposed_edge_class_ref is not None:
            object.__setattr__(
                self,
                "proposed_edge_class_ref",
                _assert_edge_class_ref(self.proposed_edge_class_ref, field_name="proposed_edge_class_ref"),
            )
        object.__setattr__(
            self,
            "judgment_hash",
            _assert_hash(self.judgment_hash, field_name="judgment_hash"),
        )
        if self.evidence_count <= 0:
            raise ValueError("evidence_count must be positive")
        if self.decision == "instance_of_existing_class":
            if self.proposed_edge_class_ref is not None or self.proposed_parent_edge_class_ref is not None:
                raise ValueError(
                    "instance_of_existing_class must not propose a new edge_class_ref or parent"
                )
        if self.decision in {
            "specialize_under_existing_class",
            "new_sibling_under_existing_parent",
            "new_intermediate_node",
        }:
            if self.proposed_edge_class_ref is None or self.proposed_parent_edge_class_ref is None:
                raise ValueError(
                    f"{self.decision} requires proposed_edge_class_ref and proposed_parent_edge_class_ref"
                )
        if self.decision == "new_top_level_family":
            if self.proposed_edge_class_ref is None:
                raise ValueError("new_top_level_family requires proposed_edge_class_ref")
            if self.proposed_parent_edge_class_ref is not None:
                raise ValueError("new_top_level_family must not carry proposed_parent_edge_class_ref")
            _assert_edge_class_ref(
                self.proposed_edge_class_ref,
                field_name="proposed_edge_class_ref",
                expected_kind="family",
            )
        if self.decision == "split_existing_class" and self.proposed_lifecycle_posture != "split":
            raise ValueError("split_existing_class requires proposed_lifecycle_posture = split")
        expected_judgment_hash = sha256_canonical_json(
            {
                "schema": self.schema,
                "bound_edge_class_catalog_ref": self.bound_edge_class_catalog_ref,
                "candidate_label": self.candidate_label,
                "nearest_existing_edge_class_refs": self.nearest_existing_edge_class_refs,
                "observed_symbol_ids": self.observed_symbol_ids,
                "applicability_cue_tags": self.applicability_cue_tags,
                "probe_signature_tags": self.probe_signature_tags,
                "applicability_pattern_distinctness": self.applicability_pattern_distinctness,
                "probe_pattern_distinctness": self.probe_pattern_distinctness,
                "representable_without_information_loss": self.representable_without_information_loss,
                "reuse_posture": self.reuse_posture,
                "evidence_count": self.evidence_count,
                "decision": self.decision,
                "proposed_parent_edge_class_ref": self.proposed_parent_edge_class_ref,
                "proposed_edge_class_ref": self.proposed_edge_class_ref,
                "proposed_lifecycle_posture": self.proposed_lifecycle_posture,
                "judgment_posture": self.judgment_posture,
                "rationale": self.rationale,
            }
        )
        if self.judgment_hash != expected_judgment_hash:
            raise ValueError("judgment_hash must match canonical revision judgment payload")
        expected_judgment_id = compute_edge_taxonomy_revision_judgment_id(
            {
                "schema": self.schema,
                "bound_edge_class_catalog_ref": self.bound_edge_class_catalog_ref,
                "candidate_label": self.candidate_label,
                "nearest_existing_edge_class_refs": self.nearest_existing_edge_class_refs,
                "observed_symbol_ids": self.observed_symbol_ids,
                "applicability_cue_tags": self.applicability_cue_tags,
                "probe_signature_tags": self.probe_signature_tags,
                "applicability_pattern_distinctness": self.applicability_pattern_distinctness,
                "probe_pattern_distinctness": self.probe_pattern_distinctness,
                "representable_without_information_loss": self.representable_without_information_loss,
                "reuse_posture": self.reuse_posture,
                "evidence_count": self.evidence_count,
                "decision": self.decision,
                "proposed_parent_edge_class_ref": self.proposed_parent_edge_class_ref,
                "proposed_edge_class_ref": self.proposed_edge_class_ref,
                "proposed_lifecycle_posture": self.proposed_lifecycle_posture,
                "judgment_posture": self.judgment_posture,
                "rationale": self.rationale,
                "judgment_hash": self.judgment_hash,
            }
        )
        if self.judgment_id != expected_judgment_id:
            raise ValueError("judgment_id must match canonical revision judgment identity")
        return self


def compute_edge_class_catalog_id(payload_without_id: dict[str, Any]) -> str:
    return f"edge_class_catalog:{sha256_canonical_json(payload_without_id)[:16]}"


def compute_edge_probe_template_catalog_id(payload_without_id: dict[str, Any]) -> str:
    return f"edge_probe_template_catalog:{sha256_canonical_json(payload_without_id)[:16]}"


def compute_symbol_edge_applicability_frame_id(payload_without_id: dict[str, Any]) -> str:
    return f"symbol_edge_applicability_frame:{sha256_canonical_json(payload_without_id)[:16]}"


def compute_symbol_edge_adjudication_ledger_id(payload_without_id: dict[str, Any]) -> str:
    return f"symbol_edge_adjudication_ledger:{sha256_canonical_json(payload_without_id)[:16]}"


def compute_edge_taxonomy_revision_judgment_id(payload_without_id: dict[str, Any]) -> str:
    return f"edge_taxonomy_revision_judgment:{sha256_canonical_json(payload_without_id)[:16]}"


__all__ = [
    "ADEU_EDGE_CLASS_CATALOG_SCHEMA",
    "ADEU_EDGE_PROBE_TEMPLATE_CATALOG_SCHEMA",
    "ADEU_EDGE_TAXONOMY_REVISION_JUDGMENT_SCHEMA",
    "ADEU_SYMBOL_EDGE_ADJUDICATION_LEDGER_SCHEMA",
    "ADEU_SYMBOL_EDGE_APPLICABILITY_FRAME_SCHEMA",
    "AdjudicationStatus",
    "ApplicabilityStatus",
    "DistinctnessPosture",
    "EdgeClassCatalog",
    "EdgeClassNode",
    "EdgeProbeTemplate",
    "EdgeProbeTemplateCatalog",
    "EdgeTaxonomyRevisionJudgment",
    "EpistemicPosture",
    "ProbeExecutionPosture",
    "ProbeStrategyKind",
    "SymbolEdgeAdjudicationLedger",
    "SymbolEdgeAdjudicationRow",
    "SymbolEdgeApplicabilityFrame",
    "SymbolEdgeApplicabilityRow",
    "SymbolKind",
    "TaxonomyNodeKind",
    "TaxonomyNodeLifecycle",
    "TaxonomyRevisionDecision",
    "ReusePosture",
    "canonical_json",
    "compute_edge_class_catalog_id",
    "compute_edge_probe_template_catalog_id",
    "compute_edge_taxonomy_revision_judgment_id",
    "compute_symbol_edge_adjudication_ledger_id",
    "compute_symbol_edge_applicability_frame_id",
    "compute_symbol_id",
    "sha256_canonical_json",
]
