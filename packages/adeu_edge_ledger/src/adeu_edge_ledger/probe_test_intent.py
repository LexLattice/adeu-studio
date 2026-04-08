from __future__ import annotations

from typing import Any, Iterable, Literal

from adeu_repo_description.models import (
    RepoDependencyGraph,
    RepoSymbolCatalog,
    RepoTestIntentMatrix,
    validate_repo_test_intent_matrix_against_v45b,
)
from pydantic import BaseModel, Field, model_validator

from .models import (
    ADMITTED_V50_SYMBOL_KIND_VOCABULARY,
    MODEL_CONFIG,
    STARTER_PROBE_STRATEGY_KIND_VOCABULARY,
    EdgeClassCatalog,
    EdgeProbeTemplateCatalog,
    ProbeStrategyKind,
    SymbolEdgeApplicabilityFrame,
    _sha256_canonical_payload,
)
from .taxonomy import validate_probe_template_catalog_binding

ADEU_EDGE_PROBE_TEST_INTENT_BRIDGE_SCHEMA = "adeu_edge_probe_test_intent_bridge@1"
BRIDGE_SCOPE = "v53d-bounded-probe-test-intent-bridge-over-v45d-with-v53a-membership"
BRIDGE_POSTURE = (
    "bounded_v53d_bridge_no_probe_mapping_without_explicit_applicability_frame_membership"
)
STARTER_BRIDGE_MAPPING_STATUS_VOCABULARY = (
    "mapped_from_applicability_frame",
    "no_applicable_probe_in_frame",
    "out_of_scope_non_symbol_guard",
    "out_of_scope_outside_v50_scope",
)

BridgeMappingStatus = Literal[
    "mapped_from_applicability_frame",
    "no_applicable_probe_in_frame",
    "out_of_scope_non_symbol_guard",
    "out_of_scope_outside_v50_scope",
]

_GUARDED_SURFACE_KIND_VOCABULARY = (
    "internal_symbol",
    "internal_module_boundary",
    "external_boundary",
)


def _assert_non_empty_text(value: str, *, field_name: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{field_name} must be a string")
    normalized = value.strip()
    if not normalized:
        raise ValueError(f"{field_name} must be non-empty")
    return normalized


def _assert_prefixed_ref(value: str, *, field_name: str, prefix: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    if not normalized.startswith(prefix):
        raise ValueError(f"{field_name} must use the {prefix} prefix")
    return normalized


def _assert_sorted_unique_texts(values: list[str], *, field_name: str) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must be unique")
    if normalized != sorted(normalized):
        raise ValueError(f"{field_name} must be sorted")
    return normalized


def _ordered_unique(values: Iterable[str]) -> list[str]:
    return list(dict.fromkeys(values))


def _sorted_unique(values: Iterable[str]) -> list[str]:
    return sorted(set(values))


def _symbol_kind_from_symbol_id(symbol_id: str) -> str:
    normalized = _assert_prefixed_ref(symbol_id, field_name="symbol_id", prefix="symbol:")
    parts = normalized.split(":")
    if len(parts) < 4:
        raise ValueError("symbol_id must include module_path, qualname, and symbol_kind segments")
    return parts[-1]


def _applicable_probe_refs(frame: SymbolEdgeApplicabilityFrame) -> list[str]:
    return _ordered_unique(
        probe_ref
        for row in frame.applicability_rows
        if row.applicability_status in {"applicable", "underdetermined"}
        for probe_ref in row.suggested_probe_template_refs
    )


def _applicable_edge_refs(frame: SymbolEdgeApplicabilityFrame) -> list[str]:
    return [
        row.edge_class_ref
        for row in frame.applicability_rows
        if row.applicability_status in {"applicable", "underdetermined"}
        and row.suggested_probe_template_refs
    ]


def compute_edge_probe_test_intent_bridge_entry_id(payload_without_entry_id: dict[str, Any]) -> str:
    digest = _sha256_canonical_payload(payload_without_entry_id)
    return f"edge_probe_test_intent_bridge_entry:{digest[:24]}"


def compute_edge_probe_test_intent_bridge_id(payload_without_bridge_id: dict[str, Any]) -> str:
    digest = _sha256_canonical_payload(payload_without_bridge_id)
    return f"edge_probe_test_intent_bridge:{digest[:24]}"


class EdgeProbeTestIntentBridgeEntry(BaseModel):
    model_config = MODEL_CONFIG

    bridge_entry_id: str
    test_intent_entry_ref: str
    test_ref: str
    guarded_surface_ref_kind: str
    guarded_surface_ref_value: str
    symbol_id: str | None = None
    bound_applicability_frame_ref: str | None = None
    mapping_status: BridgeMappingStatus
    applicable_edge_class_refs: list[str] = Field(default_factory=list)
    selected_probe_template_refs: list[str] = Field(default_factory=list)
    selected_strategy_kinds: list[ProbeStrategyKind] = Field(default_factory=list)
    supporting_evidence_refs: list[str] = Field(default_factory=list)
    mapping_rationale: str

    @model_validator(mode="after")
    def _validate(self) -> "EdgeProbeTestIntentBridgeEntry":
        for field_name in (
            "bridge_entry_id",
            "test_intent_entry_ref",
            "test_ref",
            "guarded_surface_ref_value",
            "mapping_rationale",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "guarded_surface_ref_kind",
            _assert_non_empty_text(
                self.guarded_surface_ref_kind,
                field_name="guarded_surface_ref_kind",
            ),
        )
        if self.guarded_surface_ref_kind not in _GUARDED_SURFACE_KIND_VOCABULARY:
            raise ValueError("guarded_surface_ref_kind must use the released V45-D vocabulary")
        object.__setattr__(
            self,
            "applicable_edge_class_refs",
            _assert_sorted_unique_texts(
                self.applicable_edge_class_refs,
                field_name="applicable_edge_class_refs",
            ),
        )
        object.__setattr__(
            self,
            "selected_probe_template_refs",
            _assert_sorted_unique_texts(
                self.selected_probe_template_refs,
                field_name="selected_probe_template_refs",
            ),
        )
        object.__setattr__(
            self,
            "supporting_evidence_refs",
            _assert_sorted_unique_texts(
                self.supporting_evidence_refs,
                field_name="supporting_evidence_refs",
            ),
        )
        selected_strategy_kinds = [
            _assert_non_empty_text(strategy, field_name="selected_strategy_kinds")
            for strategy in self.selected_strategy_kinds
        ]
        if len(selected_strategy_kinds) != len(set(selected_strategy_kinds)):
            raise ValueError("selected_strategy_kinds must be unique")
        for strategy in selected_strategy_kinds:
            if strategy not in STARTER_PROBE_STRATEGY_KIND_VOCABULARY:
                raise ValueError("selected_strategy_kinds must use the released probe vocabulary")
        if selected_strategy_kinds != sorted(selected_strategy_kinds):
            raise ValueError("selected_strategy_kinds must be sorted")
        object.__setattr__(self, "selected_strategy_kinds", selected_strategy_kinds)

        if self.symbol_id is not None:
            object.__setattr__(
                self,
                "symbol_id",
                _assert_prefixed_ref(self.symbol_id, field_name="symbol_id", prefix="symbol:"),
            )
        if self.bound_applicability_frame_ref is not None:
            object.__setattr__(
                self,
                "bound_applicability_frame_ref",
                _assert_prefixed_ref(
                    self.bound_applicability_frame_ref,
                    field_name="bound_applicability_frame_ref",
                    prefix="symbol_edge_applicability_frame:",
                ),
            )

        if self.mapping_status == "mapped_from_applicability_frame":
            if self.symbol_id is None or self.bound_applicability_frame_ref is None:
                raise ValueError(
                    "mapped_from_applicability_frame rows require symbol_id and "
                    "bound_applicability_frame_ref"
                )
            if not (
                self.applicable_edge_class_refs
                and self.selected_probe_template_refs
                and self.selected_strategy_kinds
            ):
                raise ValueError(
                    "mapped_from_applicability_frame rows require non-empty mapped probes"
                )
        elif self.mapping_status == "no_applicable_probe_in_frame":
            if self.symbol_id is None or self.bound_applicability_frame_ref is None:
                raise ValueError(
                    "no_applicable_probe_in_frame rows require symbol_id and "
                    "bound_applicability_frame_ref"
                )
            if (
                self.applicable_edge_class_refs
                or self.selected_probe_template_refs
                or self.selected_strategy_kinds
            ):
                raise ValueError(
                    "no_applicable_probe_in_frame rows must not carry mapped probes"
                )
        elif self.mapping_status == "out_of_scope_non_symbol_guard":
            if self.guarded_surface_ref_kind == "internal_symbol":
                raise ValueError(
                    "out_of_scope_non_symbol_guard rows must not use internal_symbol guards"
                )
            if (
                self.symbol_id is not None
                or self.bound_applicability_frame_ref is not None
                or self.applicable_edge_class_refs
                or self.selected_probe_template_refs
                or self.selected_strategy_kinds
            ):
                raise ValueError(
                    "out_of_scope_non_symbol_guard rows must not carry symbol or probe mapping data"
                )
        elif self.mapping_status == "out_of_scope_outside_v50_scope":
            if self.guarded_surface_ref_kind != "internal_symbol":
                raise ValueError(
                    "out_of_scope_outside_v50_scope rows require internal_symbol guards"
                )
            if self.symbol_id is None:
                raise ValueError("out_of_scope_outside_v50_scope rows require symbol_id")
            if (
                self.bound_applicability_frame_ref is not None
                or self.applicable_edge_class_refs
                or self.selected_probe_template_refs
                or self.selected_strategy_kinds
            ):
                raise ValueError(
                    "out_of_scope_outside_v50_scope rows must not carry mapped probes"
                )
        else:
            raise ValueError(
                "mapping_status must be one of the released bridge mapping status values"
            )

        expected_bridge_entry_id = compute_edge_probe_test_intent_bridge_entry_id(
            {
                "test_intent_entry_ref": self.test_intent_entry_ref,
                "test_ref": self.test_ref,
                "guarded_surface_ref_kind": self.guarded_surface_ref_kind,
                "guarded_surface_ref_value": self.guarded_surface_ref_value,
                "symbol_id": self.symbol_id,
                "bound_applicability_frame_ref": self.bound_applicability_frame_ref,
                "mapping_status": self.mapping_status,
                "applicable_edge_class_refs": self.applicable_edge_class_refs,
                "selected_probe_template_refs": self.selected_probe_template_refs,
                "selected_strategy_kinds": self.selected_strategy_kinds,
                "supporting_evidence_refs": self.supporting_evidence_refs,
                "mapping_rationale": self.mapping_rationale,
            }
        )
        if self.bridge_entry_id != expected_bridge_entry_id:
            raise ValueError(
                "bridge_entry_id must match canonical probe-test-intent bridge entry identity"
            )

        return self


class EdgeProbeTestIntentBridge(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_EDGE_PROBE_TEST_INTENT_BRIDGE_SCHEMA] = Field(
        default=ADEU_EDGE_PROBE_TEST_INTENT_BRIDGE_SCHEMA,
        alias="schema",
    )
    bridge_id: str
    bridge_scope: str
    bridge_posture: str
    bound_edge_class_catalog_ref: str
    bound_probe_template_catalog_ref: str
    bound_test_intent_matrix_ref: str
    bound_symbol_catalog_ref: str
    bound_dependency_graph_ref: str
    bound_applicability_frame_refs: list[str]
    bridge_entries: list[EdgeProbeTestIntentBridgeEntry] = Field(min_length=1)
    bridge_hash: str

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "EdgeProbeTestIntentBridge":
        for field_name in (
            "bridge_id",
            "bridge_scope",
            "bridge_posture",
            "bridge_hash",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "bound_edge_class_catalog_ref",
            _assert_prefixed_ref(
                self.bound_edge_class_catalog_ref,
                field_name="bound_edge_class_catalog_ref",
                prefix="edge_class_catalog:",
            ),
        )
        object.__setattr__(
            self,
            "bound_probe_template_catalog_ref",
            _assert_prefixed_ref(
                self.bound_probe_template_catalog_ref,
                field_name="bound_probe_template_catalog_ref",
                prefix="edge_probe_template_catalog:",
            ),
        )
        object.__setattr__(
            self,
            "bound_test_intent_matrix_ref",
            _assert_prefixed_ref(
                self.bound_test_intent_matrix_ref,
                field_name="bound_test_intent_matrix_ref",
                prefix="repo_test_intent_matrix_",
            ),
        )
        object.__setattr__(
            self,
            "bound_symbol_catalog_ref",
            _assert_prefixed_ref(
                self.bound_symbol_catalog_ref,
                field_name="bound_symbol_catalog_ref",
                prefix="repo_symbol_catalog_",
            ),
        )
        object.__setattr__(
            self,
            "bound_dependency_graph_ref",
            _assert_prefixed_ref(
                self.bound_dependency_graph_ref,
                field_name="bound_dependency_graph_ref",
                prefix="repo_dependency_graph_",
            ),
        )
        object.__setattr__(
            self,
            "bound_applicability_frame_refs",
            _assert_sorted_unique_texts(
                [
                    _assert_prefixed_ref(
                        value,
                        field_name="bound_applicability_frame_refs",
                        prefix="symbol_edge_applicability_frame:",
                    )
                    for value in self.bound_applicability_frame_refs
                ],
                field_name="bound_applicability_frame_refs",
            ),
        )

        entries_by_ref = {row.test_intent_entry_ref: row for row in self.bridge_entries}
        if len(entries_by_ref) != len(self.bridge_entries):
            raise ValueError("bridge_entries test_intent_entry_ref values must be unique")
        if [row.test_intent_entry_ref for row in self.bridge_entries] != sorted(entries_by_ref):
            raise ValueError("bridge_entries must be sorted by test_intent_entry_ref")

        expected_bridge_hash = _sha256_canonical_payload(
            {
                "schema": self.schema,
                "bridge_scope": self.bridge_scope,
                "bridge_posture": self.bridge_posture,
                "bound_edge_class_catalog_ref": self.bound_edge_class_catalog_ref,
                "bound_probe_template_catalog_ref": self.bound_probe_template_catalog_ref,
                "bound_test_intent_matrix_ref": self.bound_test_intent_matrix_ref,
                "bound_symbol_catalog_ref": self.bound_symbol_catalog_ref,
                "bound_dependency_graph_ref": self.bound_dependency_graph_ref,
                "bound_applicability_frame_refs": self.bound_applicability_frame_refs,
                "bridge_entries": [
                    row.model_dump(mode="json", exclude_none=True) for row in self.bridge_entries
                ],
            }
        )
        if self.bridge_hash != expected_bridge_hash:
            raise ValueError("bridge_hash must match canonical probe-test-intent bridge payload")
        expected_bridge_id = compute_edge_probe_test_intent_bridge_id(
            {
                "schema": self.schema,
                "bridge_scope": self.bridge_scope,
                "bridge_posture": self.bridge_posture,
                "bound_edge_class_catalog_ref": self.bound_edge_class_catalog_ref,
                "bound_probe_template_catalog_ref": self.bound_probe_template_catalog_ref,
                "bound_test_intent_matrix_ref": self.bound_test_intent_matrix_ref,
                "bound_symbol_catalog_ref": self.bound_symbol_catalog_ref,
                "bound_dependency_graph_ref": self.bound_dependency_graph_ref,
                "bound_applicability_frame_refs": self.bound_applicability_frame_refs,
                "bridge_entries": [
                    row.model_dump(mode="json", exclude_none=True) for row in self.bridge_entries
                ],
                "bridge_hash": self.bridge_hash,
            }
        )
        if self.bridge_id != expected_bridge_id:
            raise ValueError("bridge_id must match canonical probe-test-intent bridge identity")
        return self


def _normalize_v45d_stack(
    *,
    test_intent_matrix: RepoTestIntentMatrix | dict[str, Any],
    symbol_catalog: RepoSymbolCatalog | dict[str, Any],
    dependency_graph: RepoDependencyGraph | dict[str, Any],
) -> tuple[RepoTestIntentMatrix, RepoSymbolCatalog, RepoDependencyGraph]:
    matrix_payload = (
        test_intent_matrix.model_dump(mode="json")
        if isinstance(test_intent_matrix, RepoTestIntentMatrix)
        else test_intent_matrix
    )
    symbol_payload = (
        symbol_catalog.model_dump(mode="json")
        if isinstance(symbol_catalog, RepoSymbolCatalog)
        else symbol_catalog
    )
    dependency_payload = (
        dependency_graph.model_dump(mode="json")
        if isinstance(dependency_graph, RepoDependencyGraph)
        else dependency_graph
    )
    return validate_repo_test_intent_matrix_against_v45b(
        test_intent_matrix_payload=matrix_payload,
        symbol_catalog_payload=symbol_payload,
        dependency_graph_payload=dependency_payload,
    )


def _normalize_frames(
    *,
    frames: Iterable[SymbolEdgeApplicabilityFrame | dict[str, Any]],
    edge_class_catalog: EdgeClassCatalog,
    probe_template_catalog: EdgeProbeTemplateCatalog,
) -> tuple[dict[str, SymbolEdgeApplicabilityFrame], list[str]]:
    frame_models = [
        frame
        if isinstance(frame, SymbolEdgeApplicabilityFrame)
        else SymbolEdgeApplicabilityFrame.model_validate(frame)
        for frame in frames
    ]
    frame_ids = [frame.frame_id for frame in frame_models]
    if len(frame_ids) != len(set(frame_ids)):
        raise ValueError("applicability_frames frame_id values must be unique")
    frame_symbol_ids = [frame.symbol_id for frame in frame_models]
    if len(frame_symbol_ids) != len(set(frame_symbol_ids)):
        raise ValueError("applicability_frames symbol_id values must be unique")
    for frame in frame_models:
        if frame.bound_edge_class_catalog_ref != edge_class_catalog.catalog_id:
            raise ValueError("applicability_frames must bind the supplied edge class catalog")
        if frame.bound_probe_template_catalog_ref != probe_template_catalog.catalog_id:
            raise ValueError("applicability_frames must bind the supplied probe template catalog")
    return {frame.symbol_id: frame for frame in frame_models}, sorted(frame_ids)


def _strategy_map(probe_template_catalog: EdgeProbeTemplateCatalog) -> dict[str, ProbeStrategyKind]:
    return {
        probe.probe_template_ref: probe.strategy_kind
        for probe in probe_template_catalog.probe_templates
    }


def _selected_strategy_kinds_for_probe_refs(
    probe_refs: Iterable[str],
    *,
    strategy_by_probe_ref: dict[str, ProbeStrategyKind],
    error_context: str,
) -> list[ProbeStrategyKind]:
    strategies: list[ProbeStrategyKind] = []
    missing_probe_refs: list[str] = []
    for probe_ref in probe_refs:
        strategy_kind = strategy_by_probe_ref.get(probe_ref)
        if strategy_kind is None:
            missing_probe_refs.append(probe_ref)
            continue
        strategies.append(strategy_kind)

    if missing_probe_refs:
        missing_refs = ", ".join(_sorted_unique(missing_probe_refs))
        raise ValueError(f"{error_context} includes probe refs absent from catalog: {missing_refs}")

    return _sorted_unique(strategies)


def derive_edge_probe_test_intent_bridge(
    *,
    test_intent_matrix: RepoTestIntentMatrix | dict[str, Any],
    symbol_catalog: RepoSymbolCatalog | dict[str, Any],
    dependency_graph: RepoDependencyGraph | dict[str, Any],
    edge_class_catalog: EdgeClassCatalog,
    probe_template_catalog: EdgeProbeTemplateCatalog,
    applicability_frames: Iterable[SymbolEdgeApplicabilityFrame | dict[str, Any]] = (),
) -> EdgeProbeTestIntentBridge:
    matrix, symbol_catalog_model, dependency_graph_model = _normalize_v45d_stack(
        test_intent_matrix=test_intent_matrix,
        symbol_catalog=symbol_catalog,
        dependency_graph=dependency_graph,
    )
    validate_probe_template_catalog_binding(
        edge_class_catalog=edge_class_catalog,
        probe_template_catalog=probe_template_catalog,
    )
    frame_by_symbol_id, frame_ids = _normalize_frames(
        frames=applicability_frames,
        edge_class_catalog=edge_class_catalog,
        probe_template_catalog=probe_template_catalog,
    )
    strategy_by_probe_ref = _strategy_map(probe_template_catalog)

    entries: list[EdgeProbeTestIntentBridgeEntry] = []
    for test_intent_entry in matrix.test_intent_entries:
        guarded = test_intent_entry.guarded_surface_ref
        entry_payload: dict[str, Any] = {
            "test_intent_entry_ref": test_intent_entry.entry_id,
            "test_ref": test_intent_entry.test_ref,
            "guarded_surface_ref_kind": guarded.guarded_surface_ref_kind,
            "guarded_surface_ref_value": guarded.guarded_surface_ref_value,
            "supporting_evidence_refs": list(test_intent_entry.supporting_evidence_refs),
        }
        if guarded.guarded_surface_ref_kind != "internal_symbol":
            entry_payload.update(
                {
                    "mapping_status": "out_of_scope_non_symbol_guard",
                    "symbol_id": None,
                    "bound_applicability_frame_ref": None,
                    "applicable_edge_class_refs": [],
                    "selected_probe_template_refs": [],
                    "selected_strategy_kinds": [],
                    "mapping_rationale": (
                        "guarded surface is not internal_symbol; bounded V53-D seam defers "
                        "non-symbol guard mapping"
                    ),
                }
            )
        else:
            symbol_id = guarded.guarded_surface_ref_value
            symbol_kind = _symbol_kind_from_symbol_id(symbol_id)
            frame = frame_by_symbol_id.get(symbol_id)
            if symbol_kind not in ADMITTED_V50_SYMBOL_KIND_VOCABULARY or frame is None:
                entry_payload.update(
                    {
                        "mapping_status": "out_of_scope_outside_v50_scope",
                        "symbol_id": symbol_id,
                        "bound_applicability_frame_ref": None,
                        "applicable_edge_class_refs": [],
                        "selected_probe_template_refs": [],
                        "selected_strategy_kinds": [],
                        "mapping_rationale": (
                            "internal_symbol guard has no admitted V50 applicability frame "
                            "membership in this bounded seam"
                        ),
                    }
                )
            else:
                selected_probe_refs = _applicable_probe_refs(frame)
                applicable_edge_refs = _applicable_edge_refs(frame)
                if selected_probe_refs:
                    entry_payload.update(
                        {
                            "mapping_status": "mapped_from_applicability_frame",
                            "symbol_id": symbol_id,
                            "bound_applicability_frame_ref": frame.frame_id,
                            "applicable_edge_class_refs": applicable_edge_refs,
                            "selected_probe_template_refs": selected_probe_refs,
                            "selected_strategy_kinds": _selected_strategy_kinds_for_probe_refs(
                                selected_probe_refs,
                                strategy_by_probe_ref=strategy_by_probe_ref,
                                error_context="applicability frame suggested_probe_template_refs",
                            ),
                            "mapping_rationale": (
                                "probe mapping derived only from applicable or "
                                "underdetermined frame rows"
                            ),
                        }
                    )
                else:
                    entry_payload.update(
                        {
                            "mapping_status": "no_applicable_probe_in_frame",
                            "symbol_id": symbol_id,
                            "bound_applicability_frame_ref": frame.frame_id,
                            "applicable_edge_class_refs": [],
                            "selected_probe_template_refs": [],
                            "selected_strategy_kinds": [],
                            "mapping_rationale": (
                                "frame membership exists but no applicable or "
                                "underdetermined probe suggestions were emitted"
                            ),
                        }
                    )
        payload_without_entry_id = dict(entry_payload)
        payload_without_entry_id["bridge_entry_id"] = (
            compute_edge_probe_test_intent_bridge_entry_id(payload_without_entry_id)
        )
        entries.append(EdgeProbeTestIntentBridgeEntry.model_validate(payload_without_entry_id))

    entries.sort(key=lambda row: row.test_intent_entry_ref)
    payload = {
        "schema": ADEU_EDGE_PROBE_TEST_INTENT_BRIDGE_SCHEMA,
        "bridge_scope": BRIDGE_SCOPE,
        "bridge_posture": BRIDGE_POSTURE,
        "bound_edge_class_catalog_ref": edge_class_catalog.catalog_id,
        "bound_probe_template_catalog_ref": probe_template_catalog.catalog_id,
        "bound_test_intent_matrix_ref": matrix.repo_test_intent_matrix_id,
        "bound_symbol_catalog_ref": symbol_catalog_model.repo_symbol_catalog_id,
        "bound_dependency_graph_ref": dependency_graph_model.repo_dependency_graph_id,
        "bound_applicability_frame_refs": frame_ids,
        "bridge_entries": [entry.model_dump(mode="json", exclude_none=True) for entry in entries],
    }
    payload["bridge_hash"] = _sha256_canonical_payload(payload)
    payload["bridge_id"] = compute_edge_probe_test_intent_bridge_id(payload)
    return validate_edge_probe_test_intent_bridge_bindings(
        bridge_payload=payload,
        test_intent_matrix=matrix,
        symbol_catalog=symbol_catalog_model,
        dependency_graph=dependency_graph_model,
        edge_class_catalog=edge_class_catalog,
        probe_template_catalog=probe_template_catalog,
        applicability_frames=list(frame_by_symbol_id.values()),
    )


def validate_edge_probe_test_intent_bridge_bindings(
    *,
    bridge_payload: EdgeProbeTestIntentBridge | dict[str, Any],
    test_intent_matrix: RepoTestIntentMatrix | dict[str, Any],
    symbol_catalog: RepoSymbolCatalog | dict[str, Any],
    dependency_graph: RepoDependencyGraph | dict[str, Any],
    edge_class_catalog: EdgeClassCatalog,
    probe_template_catalog: EdgeProbeTemplateCatalog,
    applicability_frames: Iterable[SymbolEdgeApplicabilityFrame | dict[str, Any]] = (),
) -> EdgeProbeTestIntentBridge:
    matrix, symbol_catalog_model, dependency_graph_model = _normalize_v45d_stack(
        test_intent_matrix=test_intent_matrix,
        symbol_catalog=symbol_catalog,
        dependency_graph=dependency_graph,
    )
    validate_probe_template_catalog_binding(
        edge_class_catalog=edge_class_catalog,
        probe_template_catalog=probe_template_catalog,
    )
    frame_by_symbol_id, frame_ids = _normalize_frames(
        frames=applicability_frames,
        edge_class_catalog=edge_class_catalog,
        probe_template_catalog=probe_template_catalog,
    )
    strategy_by_probe_ref = _strategy_map(probe_template_catalog)
    bridge = (
        bridge_payload
        if isinstance(bridge_payload, EdgeProbeTestIntentBridge)
        else EdgeProbeTestIntentBridge.model_validate(bridge_payload)
    )

    if bridge.bound_edge_class_catalog_ref != edge_class_catalog.catalog_id:
        raise ValueError("bridge must bind the supplied edge class catalog")
    if bridge.bound_probe_template_catalog_ref != probe_template_catalog.catalog_id:
        raise ValueError("bridge must bind the supplied probe template catalog")
    if bridge.bound_test_intent_matrix_ref != matrix.repo_test_intent_matrix_id:
        raise ValueError("bridge must bind the supplied V45-D test intent matrix")
    if bridge.bound_symbol_catalog_ref != symbol_catalog_model.repo_symbol_catalog_id:
        raise ValueError("bridge must bind the supplied V45-B symbol catalog")
    if bridge.bound_dependency_graph_ref != dependency_graph_model.repo_dependency_graph_id:
        raise ValueError("bridge must bind the supplied V45-B dependency graph")
    if bridge.bound_applicability_frame_refs != frame_ids:
        raise ValueError("bridge bound_applicability_frame_refs must match supplied frames")

    test_intent_entries_by_id = {entry.entry_id: entry for entry in matrix.test_intent_entries}
    bridge_entry_refs = [entry.test_intent_entry_ref for entry in bridge.bridge_entries]
    if bridge_entry_refs != sorted(test_intent_entries_by_id):
        raise ValueError(
            "bridge_entries must cover each test_intent_entry exactly once in matrix entry order"
        )

    probe_refs = set(strategy_by_probe_ref)
    for bridge_entry in bridge.bridge_entries:
        test_intent_entry = test_intent_entries_by_id[bridge_entry.test_intent_entry_ref]
        guarded = test_intent_entry.guarded_surface_ref
        if bridge_entry.test_ref != test_intent_entry.test_ref:
            raise ValueError("bridge entry test_ref must match bound test intent entry")
        if bridge_entry.guarded_surface_ref_kind != guarded.guarded_surface_ref_kind:
            raise ValueError(
                "bridge entry guarded_surface_ref_kind must match bound test intent entry"
            )
        if bridge_entry.guarded_surface_ref_value != guarded.guarded_surface_ref_value:
            raise ValueError(
                "bridge entry guarded_surface_ref_value must match bound test intent entry"
            )
        if set(bridge_entry.supporting_evidence_refs) - set(
            test_intent_entry.supporting_evidence_refs
        ):
            raise ValueError(
                "bridge entry supporting_evidence_refs must be drawn from bound test intent "
                "evidence"
            )

        if guarded.guarded_surface_ref_kind != "internal_symbol":
            if bridge_entry.mapping_status != "out_of_scope_non_symbol_guard":
                raise ValueError(
                    "non-internal-symbol guards must remain out_of_scope_non_symbol_guard"
                )
            continue

        symbol_id = guarded.guarded_surface_ref_value
        if bridge_entry.symbol_id != symbol_id:
            raise ValueError("bridge entry symbol_id must match internal_symbol guard value")
        symbol_kind = _symbol_kind_from_symbol_id(symbol_id)
        frame = frame_by_symbol_id.get(symbol_id)
        in_scope = symbol_kind in ADMITTED_V50_SYMBOL_KIND_VOCABULARY and frame is not None
        if not in_scope:
            if bridge_entry.mapping_status != "out_of_scope_outside_v50_scope":
                raise ValueError(
                    "internal_symbol rows outside admitted V50 frame membership must remain "
                    "out_of_scope_outside_v50_scope"
                )
            continue

        if bridge_entry.bound_applicability_frame_ref != frame.frame_id:
            raise ValueError(
                "bridge mapped internal_symbol rows must bind the matching applicability frame"
            )
        allowed_probe_refs = _applicable_probe_refs(frame)
        allowed_edge_refs = set(_applicable_edge_refs(frame))
        if bridge_entry.mapping_status == "mapped_from_applicability_frame":
            if not bridge_entry.selected_probe_template_refs:
                raise ValueError(
                    "mapped_from_applicability_frame rows require non-empty probe template refs"
                )
            if not set(bridge_entry.selected_probe_template_refs).issubset(allowed_probe_refs):
                raise ValueError(
                    "mapped probe template refs must be suggested by applicable/underdetermined "
                    "rows in the bound applicability frame"
                )
            if not set(bridge_entry.selected_probe_template_refs).issubset(probe_refs):
                raise ValueError(
                    "mapped probe template refs must resolve in probe template catalog"
                )
            expected_kinds = _selected_strategy_kinds_for_probe_refs(
                bridge_entry.selected_probe_template_refs,
                strategy_by_probe_ref=strategy_by_probe_ref,
                error_context="bridge entry selected_probe_template_refs",
            )
            if bridge_entry.selected_strategy_kinds != expected_kinds:
                raise ValueError(
                    "selected_strategy_kinds must match mapped probe template strategy kinds"
                )
            if not set(bridge_entry.applicable_edge_class_refs).issubset(allowed_edge_refs):
                raise ValueError(
                    "applicable_edge_class_refs must be sourced from admitted frame rows"
                )
            continue

        if bridge_entry.mapping_status == "no_applicable_probe_in_frame":
            if allowed_probe_refs:
                raise ValueError(
                    "no_applicable_probe_in_frame rows are only valid when the bound frame has no "
                    "admitted probe suggestions"
                )
            continue

        raise ValueError(
            "internal_symbol rows with admitted frame membership must use "
            "mapped_from_applicability_frame or no_applicable_probe_in_frame"
        )
    return bridge


__all__ = [
    "ADEU_EDGE_PROBE_TEST_INTENT_BRIDGE_SCHEMA",
    "BRIDGE_POSTURE",
    "BRIDGE_SCOPE",
    "STARTER_BRIDGE_MAPPING_STATUS_VOCABULARY",
    "BridgeMappingStatus",
    "EdgeProbeTestIntentBridge",
    "EdgeProbeTestIntentBridgeEntry",
    "compute_edge_probe_test_intent_bridge_entry_id",
    "compute_edge_probe_test_intent_bridge_id",
    "derive_edge_probe_test_intent_bridge",
    "validate_edge_probe_test_intent_bridge_bindings",
]
