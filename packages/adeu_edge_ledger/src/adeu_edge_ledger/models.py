from __future__ import annotations

import hashlib
import json
import re
from pathlib import PurePosixPath
from typing import Any, Literal

from adeu_repo_description.models import compute_symbol_id
from pydantic import BaseModel, ConfigDict, Field, model_validator

ADEU_EDGE_CLASS_CATALOG_SCHEMA = "adeu_edge_class_catalog@1"
ADEU_EDGE_PROBE_TEMPLATE_CATALOG_SCHEMA = "adeu_edge_probe_template_catalog@1"
ADEU_SYMBOL_EDGE_APPLICABILITY_FRAME_SCHEMA = "adeu_symbol_edge_applicability_frame@1"
ADEU_SYMBOL_EDGE_ADJUDICATION_LEDGER_SCHEMA = "adeu_symbol_edge_adjudication_ledger@1"

MODEL_CONFIG = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

STARTER_TOP_LEVEL_FAMILY_SLUGS = (
    "input_domain",
    "boundary_order",
    "control_partition",
    "state_sequence",
    "canonicalization_representation",
    "contract_invariant",
    "dependency_boundary",
    "failure_path",
)
STARTER_TOP_LEVEL_FAMILY_REFS = tuple(
    f"edge_class:{family_slug}" for family_slug in STARTER_TOP_LEVEL_FAMILY_SLUGS
)
STARTER_NODE_KIND_VOCABULARY = ("family", "subfamily", "archetype")
STARTER_LIFECYCLE_POSTURE_VOCABULARY = (
    "candidate",
    "stabilized",
    "split",
    "merged",
    "deprecated",
)
STARTER_PROBE_EXECUTION_POSTURE_VOCABULARY = (
    "example_tests",
    "property_based",
    "metamorphic",
    "review_only",
)
STARTER_PROBE_STRATEGY_KIND_VOCABULARY = (
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
)
STARTER_APPLICABILITY_STATUS_VOCABULARY = (
    "applicable",
    "not_applicable",
    "underdetermined",
)
STARTER_ADJUDICATION_STATUS_VOCABULARY = (
    "not_applicable",
    "applicable_unchecked",
    "witness_found",
    "checked_no_witness_found",
    "underdetermined",
    "deferred",
)
STARTER_EPISTEMIC_POSTURE_VOCABULARY = (
    "derived_deterministically",
    "inferred_heuristically",
)
ADMITTED_V50_SYMBOL_KIND_VOCABULARY = ("class", "function", "method", "local_function")

TaxonomyNodeKind = Literal["family", "subfamily", "archetype"]
TaxonomyNodeLifecycle = Literal["candidate", "stabilized", "split", "merged", "deprecated"]
ProbeExecutionPosture = Literal["example_tests", "property_based", "metamorphic", "review_only"]
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
]
ApplicabilityStatus = Literal["applicable", "not_applicable", "underdetermined"]
AdjudicationStatus = Literal[
    "not_applicable",
    "applicable_unchecked",
    "witness_found",
    "checked_no_witness_found",
    "underdetermined",
    "deferred",
]
EpistemicPosture = Literal["derived_deterministically", "inferred_heuristically"]
SymbolKind = Literal["class", "function", "method", "local_function"]

_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


def _assert_non_empty_text(value: str, *, field_name: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{field_name} must be a string")
    normalized = value.strip()
    if not normalized:
        raise ValueError(f"{field_name} must be non-empty")
    return normalized


def _assert_repo_rel_path(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    if normalized.startswith("/"):
        raise ValueError(f"{field_name} must be repo-relative")
    if "\\" in normalized:
        raise ValueError(f"{field_name} must use forward slashes")
    path = PurePosixPath(normalized)
    if path.is_absolute():
        raise ValueError(f"{field_name} must be repo-relative")
    if any(part in {"", ".", ".."} for part in path.parts):
        raise ValueError(f"{field_name} must not contain empty, '.' or '..' segments")
    if path.name == "":
        raise ValueError(f"{field_name} must point to a file path")
    return path.as_posix()


def _assert_sha256_hex(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    if not _SHA256_RE.fullmatch(normalized):
        raise ValueError(f"{field_name} must be a lowercase 64-character sha256 hex digest")
    return normalized


def _assert_ordered_unique_texts(values: list[str], *, field_name: str) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must be unique")
    return normalized


def _assert_sorted_unique_texts(values: list[str], *, field_name: str) -> list[str]:
    normalized = _assert_ordered_unique_texts(values, field_name=field_name)
    if normalized != sorted(normalized):
        raise ValueError(f"{field_name} must be sorted")
    return normalized


def _assert_ordered_subset(
    values: list[str],
    *,
    field_name: str,
    vocabulary: tuple[str, ...],
) -> list[str]:
    normalized = _assert_ordered_unique_texts(values, field_name=field_name)
    positions: list[int] = []
    for value in normalized:
        if value not in vocabulary:
            raise ValueError(f"{field_name} must use the frozen starter vocabulary")
        positions.append(vocabulary.index(value))
    if positions != sorted(positions):
        raise ValueError(f"{field_name} must respect frozen starter vocabulary order")
    return normalized


def _edge_class_segments(value: str, *, field_name: str) -> tuple[str, ...]:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    prefix = "edge_class:"
    if not normalized.startswith(prefix):
        raise ValueError(f"{field_name} must use the edge_class: prefix")
    remainder = normalized[len(prefix) :]
    segments = tuple(remainder.split("/"))
    if len(segments) not in {1, 2, 3}:
        raise ValueError(f"{field_name} must carry 1, 2, or 3 slug segments")
    for segment in segments:
        if not segment or not re.fullmatch(r"[a-z][a-z0-9_]*", segment):
            raise ValueError(f"{field_name} must use lowercase underscore slug segments")
    if segments[0] not in STARTER_TOP_LEVEL_FAMILY_SLUGS:
        raise ValueError(f"{field_name} must use one of the frozen starter top-level families")
    return segments


def _assert_edge_class_ref(
    value: str,
    *,
    field_name: str,
    expected_kind: TaxonomyNodeKind | None = None,
) -> str:
    segments = _edge_class_segments(value, field_name=field_name)
    if expected_kind is not None:
        expected_segment_count = {"family": 1, "subfamily": 2, "archetype": 3}[expected_kind]
        if len(segments) != expected_segment_count:
            raise ValueError(
                f"{field_name} must carry {expected_segment_count} segments for {expected_kind}"
            )
    return f"edge_class:{'/'.join(segments)}"


def _assert_probe_template_ref(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    prefix = "probe:"
    if not normalized.startswith(prefix):
        raise ValueError(f"{field_name} must use the probe: prefix")
    slug = normalized[len(prefix) :]
    if not re.fullmatch(r"[a-z][a-z0-9_]*", slug):
        raise ValueError(f"{field_name} must use a lowercase underscore slug after probe:")
    return normalized


def _assert_catalog_ref(value: str, *, field_name: str, prefix: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    if not normalized.startswith(prefix):
        raise ValueError(f"{field_name} must use the {prefix} prefix")
    return normalized


def _dump_canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def _sha256_canonical_payload(value: Any) -> str:
    return hashlib.sha256(_dump_canonical_json(value).encode("utf-8")).hexdigest()


def compute_edge_class_catalog_id(payload_without_id: dict[str, Any]) -> str:
    return f"edge_class_catalog:{_sha256_canonical_payload(payload_without_id)[:16]}"


def compute_edge_probe_template_catalog_id(payload_without_id: dict[str, Any]) -> str:
    return f"edge_probe_template_catalog:{_sha256_canonical_payload(payload_without_id)[:16]}"


def compute_symbol_edge_applicability_frame_id(payload_without_id: dict[str, Any]) -> str:
    return f"symbol_edge_applicability_frame:{_sha256_canonical_payload(payload_without_id)[:16]}"


def compute_symbol_edge_adjudication_ledger_id(payload_without_id: dict[str, Any]) -> str:
    return f"symbol_edge_adjudication_ledger:{_sha256_canonical_payload(payload_without_id)[:16]}"


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
        if set(self.required_cue_tags) & set(self.supporting_cue_tags):
            raise ValueError("required_cue_tags and supporting_cue_tags must be disjoint")

        edge_segments = _edge_class_segments(self.edge_class_ref, field_name="edge_class_ref")
        if self.node_kind == "family":
            if self.parent_edge_class_ref is not None:
                raise ValueError("family node must not carry parent_edge_class_ref")
            if self.edge_class_ref not in STARTER_TOP_LEVEL_FAMILY_REFS:
                raise ValueError(
                    "family node must use the frozen starter top-level family vocabulary"
                )
            if any(
                (
                    self.required_cue_tags,
                    self.supporting_cue_tags,
                    self.structural_safety_cue_tags,
                    self.test_token_tags,
                    self.default_probe_template_refs,
                )
            ):
                raise ValueError("family nodes must not carry cue or probe-template bindings")
            return self

        if self.parent_edge_class_ref is None:
            raise ValueError("subfamily and archetype nodes must carry parent_edge_class_ref")

        expected_parent_kind: TaxonomyNodeKind = (
            "family" if self.node_kind == "subfamily" else "subfamily"
        )
        object.__setattr__(
            self,
            "parent_edge_class_ref",
            _assert_edge_class_ref(
                self.parent_edge_class_ref,
                field_name="parent_edge_class_ref",
                expected_kind=expected_parent_kind,
            ),
        )
        parent_segments = _edge_class_segments(
            self.parent_edge_class_ref, field_name="parent_edge_class_ref"
        )
        if self.node_kind == "subfamily":
            expected_parent_ref = f"edge_class:{edge_segments[0]}"
            if self.parent_edge_class_ref != expected_parent_ref:
                raise ValueError("subfamily parent_edge_class_ref must match the family prefix")
            if any(
                (
                    self.required_cue_tags,
                    self.supporting_cue_tags,
                    self.structural_safety_cue_tags,
                    self.test_token_tags,
                    self.default_probe_template_refs,
                )
            ):
                raise ValueError("subfamily nodes must not carry cue or probe-template bindings")
            return self

        expected_parent_ref = f"edge_class:{edge_segments[0]}/{edge_segments[1]}"
        if self.parent_edge_class_ref != expected_parent_ref:
            raise ValueError("archetype parent_edge_class_ref must match the subfamily prefix")
        if not (self.required_cue_tags or self.supporting_cue_tags):
            raise ValueError(
                "archetype nodes must declare required_cue_tags or supporting_cue_tags"
            )
        if not self.default_probe_template_refs:
            raise ValueError("archetype nodes must carry default_probe_template_refs")
        if len(parent_segments) != 2:
            raise ValueError("archetype parent_edge_class_ref must point to a subfamily node")
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
        object.__setattr__(
            self, "catalog_hash", _assert_sha256_hex(self.catalog_hash, field_name="catalog_hash")
        )
        nodes_by_ref = {node.edge_class_ref: node for node in self.nodes}
        if len(nodes_by_ref) != len(self.nodes):
            raise ValueError("nodes edge_class_ref values must be unique")
        if [node.edge_class_ref for node in self.nodes] != sorted(nodes_by_ref):
            raise ValueError("nodes must be sorted lexicographically by edge_class_ref")
        family_refs = [node.edge_class_ref for node in self.nodes if node.node_kind == "family"]
        if family_refs != sorted(STARTER_TOP_LEVEL_FAMILY_REFS):
            raise ValueError(
                "family nodes must match the frozen starter top-level family vocabulary"
            )
        children_by_parent: dict[str, list[str]] = {}
        for node in self.nodes:
            if node.parent_edge_class_ref is None:
                continue
            if node.parent_edge_class_ref not in nodes_by_ref:
                raise ValueError("parent_edge_class_ref must resolve inside nodes")
            children_by_parent.setdefault(node.parent_edge_class_ref, []).append(
                node.edge_class_ref
            )
            parent_kind = nodes_by_ref[node.parent_edge_class_ref].node_kind
            expected_parent_kind: TaxonomyNodeKind = (
                "family" if node.node_kind == "subfamily" else "subfamily"
            )
            if parent_kind != expected_parent_kind:
                raise ValueError(
                    f"{node.node_kind} parent_edge_class_ref must point to "
                    f"a {expected_parent_kind} node"
                )
        for node in self.nodes:
            if (
                node.node_kind in {"family", "subfamily"}
                and node.edge_class_ref not in children_by_parent
            ):
                raise ValueError("family and subfamily nodes must have at least one child node")
        expected_catalog_hash = _sha256_canonical_payload(
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
            _assert_ordered_subset(
                self.execution_postures,
                field_name="execution_postures",
                vocabulary=STARTER_PROBE_EXECUTION_POSTURE_VOCABULARY,
            ),
        )
        object.__setattr__(
            self,
            "suited_edge_class_refs",
            [
                _assert_edge_class_ref(
                    value,
                    field_name="suited_edge_class_refs",
                    expected_kind="archetype",
                )
                for value in _assert_sorted_unique_texts(
                    self.suited_edge_class_refs,
                    field_name="suited_edge_class_refs",
                )
            ],
        )
        object.__setattr__(
            self,
            "required_signal_tags",
            _assert_sorted_unique_texts(
                self.required_signal_tags, field_name="required_signal_tags"
            ),
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
            self, "catalog_hash", _assert_sha256_hex(self.catalog_hash, field_name="catalog_hash")
        )
        probes_by_ref = {probe.probe_template_ref: probe for probe in self.probe_templates}
        if len(probes_by_ref) != len(self.probe_templates):
            raise ValueError("probe_templates probe_template_ref values must be unique")
        if [probe.probe_template_ref for probe in self.probe_templates] != sorted(probes_by_ref):
            raise ValueError(
                "probe_templates must be sorted lexicographically by probe_template_ref"
            )
        expected_catalog_hash = _sha256_canonical_payload(
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
            _assert_edge_class_ref(
                self.edge_class_ref,
                field_name="edge_class_ref",
                expected_kind="archetype",
            ),
        )
        object.__setattr__(
            self,
            "matched_cue_tags",
            _assert_ordered_unique_texts(self.matched_cue_tags, field_name="matched_cue_tags"),
        )
        object.__setattr__(
            self,
            "concrete_binding_refs",
            _assert_ordered_unique_texts(
                self.concrete_binding_refs,
                field_name="concrete_binding_refs",
            ),
        )
        object.__setattr__(
            self,
            "suggested_probe_template_refs",
            [
                _assert_probe_template_ref(value, field_name="suggested_probe_template_refs")
                for value in _assert_ordered_unique_texts(
                    self.suggested_probe_template_refs,
                    field_name="suggested_probe_template_refs",
                )
            ],
        )
        object.__setattr__(
            self, "rationale", _assert_non_empty_text(self.rationale, field_name="rationale")
        )
        if self.applicability_status == "underdetermined":
            if self.epistemic_posture != "inferred_heuristically":
                raise ValueError(
                    "underdetermined applicability_status requires epistemic_posture = "
                    "inferred_heuristically"
                )
        else:
            if self.epistemic_posture != "derived_deterministically":
                raise ValueError(
                    "applicable and not_applicable rows require epistemic_posture = "
                    "derived_deterministically"
                )
        if self.applicability_status in {"applicable", "underdetermined"}:
            if not self.matched_cue_tags or not self.concrete_binding_refs:
                raise ValueError(
                    "applicable and underdetermined rows require non-empty matched_cue_tags "
                    "and concrete_binding_refs"
                )
        else:
            if self.matched_cue_tags or self.concrete_binding_refs:
                raise ValueError(
                    "not_applicable rows require empty matched_cue_tags and concrete_binding_refs"
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
        for field_name in ("frame_id", "scope_manifest_ref", "qualname", "frame_posture"):
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
            self, "module_path", _assert_repo_rel_path(self.module_path, field_name="module_path")
        )
        expected_symbol_id = compute_symbol_id(
            module_path=self.module_path,
            qualname=self.qualname,
            symbol_kind=self.symbol_kind,
        )
        if self.symbol_id != expected_symbol_id:
            raise ValueError("symbol_id must match canonical module_path + qualname + symbol_kind")
        object.__setattr__(
            self, "census_hash", _assert_sha256_hex(self.census_hash, field_name="census_hash")
        )
        object.__setattr__(
            self, "audit_hash", _assert_sha256_hex(self.audit_hash, field_name="audit_hash")
        )
        object.__setattr__(
            self, "frame_hash", _assert_sha256_hex(self.frame_hash, field_name="frame_hash")
        )
        rows_by_ref = {row.edge_class_ref: row for row in self.applicability_rows}
        if len(rows_by_ref) != len(self.applicability_rows):
            raise ValueError("applicability_rows edge_class_ref values must be unique")
        if [row.edge_class_ref for row in self.applicability_rows] != sorted(rows_by_ref):
            raise ValueError(
                "applicability_rows must be sorted lexicographically by edge_class_ref"
            )
        expected_frame_hash = _sha256_canonical_payload(
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


class WitnessSummaryRecord(BaseModel):
    model_config = MODEL_CONFIG

    witness_ref: str
    edge_class_ref: str
    summary_text: str

    @model_validator(mode="after")
    def _validate(self) -> "WitnessSummaryRecord":
        object.__setattr__(
            self,
            "witness_ref",
            _assert_non_empty_text(self.witness_ref, field_name="witness_ref"),
        )
        object.__setattr__(
            self,
            "edge_class_ref",
            _assert_edge_class_ref(
                self.edge_class_ref,
                field_name="edge_class_ref",
                expected_kind="archetype",
            ),
        )
        object.__setattr__(
            self,
            "summary_text",
            _assert_non_empty_text(self.summary_text, field_name="summary_text"),
        )
        return self


class SymbolEdgeAdjudicationRow(BaseModel):
    model_config = MODEL_CONFIG

    edge_class_ref: str
    source_applicability_status: ApplicabilityStatus
    adjudication_status: AdjudicationStatus
    supporting_witness_refs: list[str] = Field(default_factory=list)
    supporting_checked_no_witness_refs: list[str] = Field(default_factory=list)
    deferral_reason: str | None = None

    @model_validator(mode="after")
    def _validate(self) -> "SymbolEdgeAdjudicationRow":
        object.__setattr__(
            self,
            "edge_class_ref",
            _assert_edge_class_ref(
                self.edge_class_ref,
                field_name="edge_class_ref",
                expected_kind="archetype",
            ),
        )
        object.__setattr__(
            self,
            "supporting_witness_refs",
            _assert_ordered_unique_texts(
                self.supporting_witness_refs,
                field_name="supporting_witness_refs",
            ),
        )
        object.__setattr__(
            self,
            "supporting_checked_no_witness_refs",
            [
                _assert_edge_class_ref(
                    value,
                    field_name="supporting_checked_no_witness_refs",
                    expected_kind="archetype",
                )
                for value in _assert_ordered_unique_texts(
                    self.supporting_checked_no_witness_refs,
                    field_name="supporting_checked_no_witness_refs",
                )
            ],
        )
        if self.deferral_reason is not None:
            object.__setattr__(
                self,
                "deferral_reason",
                _assert_non_empty_text(self.deferral_reason, field_name="deferral_reason"),
            )

        if self.source_applicability_status == "not_applicable":
            if self.adjudication_status != "not_applicable":
                raise ValueError(
                    "not_applicable source_applicability_status must remain not_applicable"
                )
            if self.supporting_witness_refs or self.supporting_checked_no_witness_refs:
                raise ValueError("not_applicable rows must have empty support refs")
            if self.deferral_reason is not None:
                raise ValueError("not_applicable rows must not carry deferral_reason")
            return self

        if self.source_applicability_status == "applicable":
            if self.adjudication_status == "applicable_unchecked":
                if self.supporting_witness_refs or self.supporting_checked_no_witness_refs:
                    raise ValueError("applicable_unchecked rows must have empty support refs")
                if self.deferral_reason is not None:
                    raise ValueError("applicable_unchecked rows must not carry deferral_reason")
                return self
            if self.adjudication_status == "witness_found":
                if not self.supporting_witness_refs or self.supporting_checked_no_witness_refs:
                    raise ValueError(
                        "witness_found rows require non-empty supporting_witness_refs only"
                    )
                if self.deferral_reason is not None:
                    raise ValueError("witness_found rows must not carry deferral_reason")
                return self
            if self.adjudication_status == "checked_no_witness_found":
                if self.supporting_witness_refs or not self.supporting_checked_no_witness_refs:
                    raise ValueError(
                        "checked_no_witness_found rows require non-empty "
                        "supporting_checked_no_witness_refs only"
                    )
                if self.supporting_checked_no_witness_refs != [self.edge_class_ref]:
                    raise ValueError(
                        "checked_no_witness_found rows must carry the row edge_class_ref "
                        "as the starter checked-no-witness support ref"
                    )
                if self.deferral_reason is not None:
                    raise ValueError(
                        "checked_no_witness_found rows must not carry deferral_reason"
                    )
                return self
            raise ValueError(
                "applicable source_applicability_status only admits applicable_unchecked, "
                "witness_found, or checked_no_witness_found"
            )

        if self.source_applicability_status == "underdetermined":
            if self.adjudication_status == "underdetermined":
                if self.supporting_witness_refs or self.supporting_checked_no_witness_refs:
                    raise ValueError("underdetermined rows must have empty support refs")
                if self.deferral_reason is not None:
                    raise ValueError("underdetermined rows must not carry deferral_reason")
                return self
            if self.adjudication_status == "deferred":
                if not (self.supporting_witness_refs or self.supporting_checked_no_witness_refs):
                    raise ValueError("deferred rows require explicit support refs")
                if self.supporting_checked_no_witness_refs not in ([], [self.edge_class_ref]):
                    raise ValueError(
                        "deferred rows with checked-no-witness support must carry the "
                        "row edge_class_ref exactly once"
                    )
                if self.deferral_reason is None:
                    raise ValueError("deferred rows require deferral_reason")
                return self
            raise ValueError(
                "underdetermined source_applicability_status only admits underdetermined "
                "or deferred"
            )

        return self


class SymbolEdgeAdjudicationLedger(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_SYMBOL_EDGE_ADJUDICATION_LEDGER_SCHEMA] = Field(
        default=ADEU_SYMBOL_EDGE_ADJUDICATION_LEDGER_SCHEMA,
        alias="schema",
    )
    ledger_id: str
    applicability_frame_ref: str
    bound_edge_class_catalog_ref: str
    bound_probe_template_catalog_ref: str
    symbol_id: str
    module_path: str
    qualname: str
    symbol_kind: SymbolKind
    adjudication_rows: list[SymbolEdgeAdjudicationRow] = Field(min_length=1)
    ledger_hash: str

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "SymbolEdgeAdjudicationLedger":
        for field_name in ("ledger_id", "applicability_frame_ref", "qualname"):
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
            "ledger_hash",
            _assert_sha256_hex(self.ledger_hash, field_name="ledger_hash"),
        )
        expected_symbol_id = compute_symbol_id(
            module_path=self.module_path,
            qualname=self.qualname,
            symbol_kind=self.symbol_kind,
        )
        if self.symbol_id != expected_symbol_id:
            raise ValueError("symbol_id must match canonical module_path + qualname + symbol_kind")
        rows_by_ref = {row.edge_class_ref: row for row in self.adjudication_rows}
        if len(rows_by_ref) != len(self.adjudication_rows):
            raise ValueError("adjudication_rows edge_class_ref values must be unique")
        if [row.edge_class_ref for row in self.adjudication_rows] != sorted(rows_by_ref):
            raise ValueError(
                "adjudication_rows must be sorted lexicographically by edge_class_ref"
            )
        expected_ledger_hash = _sha256_canonical_payload(
            {
                "schema": self.schema,
                "applicability_frame_ref": self.applicability_frame_ref,
                "bound_edge_class_catalog_ref": self.bound_edge_class_catalog_ref,
                "bound_probe_template_catalog_ref": self.bound_probe_template_catalog_ref,
                "symbol_id": self.symbol_id,
                "module_path": self.module_path,
                "qualname": self.qualname,
                "symbol_kind": self.symbol_kind,
                "adjudication_rows": [
                    row.model_dump(mode="json", exclude_none=True)
                    for row in self.adjudication_rows
                ],
            }
        )
        if self.ledger_hash != expected_ledger_hash:
            raise ValueError("ledger_hash must match canonical adjudication payload")
        expected_ledger_id = compute_symbol_edge_adjudication_ledger_id(
            {
                "schema": self.schema,
                "applicability_frame_ref": self.applicability_frame_ref,
                "bound_edge_class_catalog_ref": self.bound_edge_class_catalog_ref,
                "bound_probe_template_catalog_ref": self.bound_probe_template_catalog_ref,
                "symbol_id": self.symbol_id,
                "module_path": self.module_path,
                "qualname": self.qualname,
                "symbol_kind": self.symbol_kind,
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


__all__ = [
    "ADEU_SYMBOL_EDGE_ADJUDICATION_LEDGER_SCHEMA",
    "ADEU_EDGE_CLASS_CATALOG_SCHEMA",
    "ADEU_EDGE_PROBE_TEMPLATE_CATALOG_SCHEMA",
    "ADEU_SYMBOL_EDGE_APPLICABILITY_FRAME_SCHEMA",
    "ADMITTED_V50_SYMBOL_KIND_VOCABULARY",
    "AdjudicationStatus",
    "ApplicabilityStatus",
    "EdgeClassCatalog",
    "EdgeClassNode",
    "EdgeProbeTemplate",
    "EdgeProbeTemplateCatalog",
    "EpistemicPosture",
    "MODEL_CONFIG",
    "ProbeExecutionPosture",
    "ProbeStrategyKind",
    "STARTER_ADJUDICATION_STATUS_VOCABULARY",
    "STARTER_APPLICABILITY_STATUS_VOCABULARY",
    "STARTER_EPISTEMIC_POSTURE_VOCABULARY",
    "STARTER_LIFECYCLE_POSTURE_VOCABULARY",
    "STARTER_NODE_KIND_VOCABULARY",
    "STARTER_PROBE_EXECUTION_POSTURE_VOCABULARY",
    "STARTER_PROBE_STRATEGY_KIND_VOCABULARY",
    "STARTER_TOP_LEVEL_FAMILY_REFS",
    "STARTER_TOP_LEVEL_FAMILY_SLUGS",
    "SymbolEdgeAdjudicationLedger",
    "SymbolEdgeAdjudicationRow",
    "SymbolEdgeApplicabilityFrame",
    "SymbolEdgeApplicabilityRow",
    "SymbolKind",
    "TaxonomyNodeKind",
    "TaxonomyNodeLifecycle",
    "WitnessSummaryRecord",
    "compute_symbol_edge_adjudication_ledger_id",
    "compute_edge_class_catalog_id",
    "compute_edge_probe_template_catalog_id",
    "compute_symbol_edge_applicability_frame_id",
]
