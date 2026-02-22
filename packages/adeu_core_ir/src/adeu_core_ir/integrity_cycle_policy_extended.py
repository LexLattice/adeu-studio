from __future__ import annotations

from typing import Any, Literal, Mapping

from pydantic import BaseModel, ConfigDict, Field, model_validator

from .models import AdeuCoreIR

IntegrityCyclePolicyExtendedSchemaVersion = Literal[
    "adeu_integrity_cycle_policy_extended@0.1"
]
IntegrityCyclePolicyExtendedKind = Literal[
    "self_cycle",
    "multi_node_cycle",
    "dependency_loop",
    "exception_loop",
]
_GraphScope = Literal["e_continuity", "d_extended"]

_MAX_EMITTED_CYCLES = 1000
_D_EXTENDED_EDGE_TYPES = {"depends_on", "excepts"}


def _is_present_component(value: Any) -> bool:
    return isinstance(value, str) and value != ""


def _cycle_signature(node_ids: list[str]) -> str:
    return "cycle:" + "->".join(node_ids)


def _canonical_cycle_rotation(node_ids: list[str]) -> list[str]:
    if len(node_ids) <= 1:
        return list(node_ids)

    rotations = [node_ids[index:] + node_ids[:index] for index in range(len(node_ids))]
    return min(rotations)


def _cycle_sort_key(cycle: "AdeuIntegrityCyclePolicyExtendedCycle") -> tuple[str, str]:
    return (cycle.kind, cycle.cycle_signature)


class AdeuIntegrityCyclePolicyExtendedSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")

    total_cycles: int
    self_cycle: int
    multi_node_cycle: int
    dependency_loop: int
    exception_loop: int

    @model_validator(mode="after")
    def _validate_total(self) -> "AdeuIntegrityCyclePolicyExtendedSummary":
        expected_total = (
            self.self_cycle
            + self.multi_node_cycle
            + self.dependency_loop
            + self.exception_loop
        )
        if self.total_cycles != expected_total:
            raise ValueError("summary.total_cycles must equal the sum of cycle counts")
        return self


class AdeuIntegrityCyclePolicyExtendedCycle(BaseModel):
    model_config = ConfigDict(extra="forbid")

    kind: IntegrityCyclePolicyExtendedKind
    cycle_signature: str
    node_ids: list[str]

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuIntegrityCyclePolicyExtendedCycle":
        if not self.node_ids:
            raise ValueError("cycle.node_ids may not be empty")
        if any(not node_id for node_id in self.node_ids):
            raise ValueError("cycle.node_ids may not contain empty node ids")
        if len(self.node_ids) > 1 and len(set(self.node_ids)) != len(self.node_ids):
            raise ValueError("cycle.node_ids may not contain duplicate node ids")

        canonical_node_ids = _canonical_cycle_rotation(self.node_ids)
        if self.node_ids != canonical_node_ids:
            raise ValueError("cycle.node_ids must use canonical cycle rotation")

        expected_signature = _cycle_signature(self.node_ids)
        if self.cycle_signature != expected_signature:
            raise ValueError("cycle_signature must match canonical node_ids")
        return self


class AdeuIntegrityCyclePolicyExtended(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: IntegrityCyclePolicyExtendedSchemaVersion = "adeu_integrity_cycle_policy_extended@0.1"
    source_text_hash: str
    summary: AdeuIntegrityCyclePolicyExtendedSummary
    cycles: list[AdeuIntegrityCyclePolicyExtendedCycle] = Field(default_factory=list)
    metadata: dict[str, Any] | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuIntegrityCyclePolicyExtended":
        sorted_cycles = sorted(self.cycles, key=_cycle_sort_key)
        if self.cycles != sorted_cycles:
            raise ValueError("cycles must be sorted by (kind, cycle_signature)")

        counts: dict[IntegrityCyclePolicyExtendedKind, int] = {
            "self_cycle": 0,
            "multi_node_cycle": 0,
            "dependency_loop": 0,
            "exception_loop": 0,
        }
        for cycle in self.cycles:
            counts[cycle.kind] += 1

        expected_summary = {
            "total_cycles": len(self.cycles),
            "self_cycle": counts["self_cycle"],
            "multi_node_cycle": counts["multi_node_cycle"],
            "dependency_loop": counts["dependency_loop"],
            "exception_loop": counts["exception_loop"],
        }
        actual_summary = self.summary.model_dump(mode="json")
        if actual_summary != expected_summary:
            raise ValueError("summary counts must match cycles list counts exactly")
        return self


def _extract_source_text_hash(payload: Mapping[str, Any]) -> str:
    source_text_hash = payload.get("source_text_hash")
    if not _is_present_component(source_text_hash):
        raise ValueError("source_text_hash must be a non-empty string")
    return source_text_hash


def _extract_edges(payload: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    raw_edges = payload.get("edges")
    if raw_edges is None:
        return []
    if not isinstance(raw_edges, list):
        raise ValueError("edges must be a list when present")
    return [edge for edge in raw_edges if isinstance(edge, Mapping)]


def _collect_node_layers(payload: Mapping[str, Any]) -> dict[str, str]:
    raw_nodes = payload.get("nodes")
    if raw_nodes is None:
        return {}
    if not isinstance(raw_nodes, list):
        raise ValueError("nodes must be a list when present")

    node_layers: dict[str, str] = {}
    for node in raw_nodes:
        if not isinstance(node, Mapping):
            continue
        node_id = node.get("id")
        layer = node.get("layer")
        if not (_is_present_component(node_id) and _is_present_component(layer)):
            continue
        if node_id in node_layers:
            continue
        node_layers[node_id] = layer
    return node_layers


def _edge_refs(edge: Mapping[str, Any]) -> tuple[Any, Any, Any]:
    edge_type = edge.get("type")
    from_ref = edge.get("from", edge.get("from_ref"))
    to_ref = edge.get("to", edge.get("to_ref"))
    return edge_type, from_ref, to_ref


def _raise_cycle_cap_error() -> None:
    raise ValueError(
        "URM_ADEU_INTEGRITY_FIXTURE_INVALID: cycle-policy extended diagnostics exceeded cap"
    )


def _build_e_depends_on_adjacency(
    *,
    node_layers: Mapping[str, str],
    edges: list[Mapping[str, Any]],
) -> dict[str, list[tuple[str, str]]]:
    adjacency: dict[str, set[tuple[str, str]]] = {
        node_id: set() for node_id, layer in node_layers.items() if layer == "E"
    }

    for edge in edges:
        edge_type, from_ref, to_ref = _edge_refs(edge)
        if (
            edge_type == "depends_on"
            and _is_present_component(from_ref)
            and _is_present_component(to_ref)
            and from_ref in adjacency
            and to_ref in adjacency
        ):
            adjacency[from_ref].add((to_ref, "depends_on"))

    return {
        node_id: sorted(adjacency[node_id], key=lambda item: (item[0], item[1]))
        for node_id in sorted(adjacency)
    }


def _build_d_extended_adjacency(
    *,
    node_layers: Mapping[str, str],
    edges: list[Mapping[str, Any]],
) -> dict[str, list[tuple[str, str]]]:
    adjacency: dict[str, set[tuple[str, str]]] = {
        node_id: set() for node_id, layer in node_layers.items() if layer == "D"
    }

    for edge in edges:
        edge_type, from_ref, to_ref = _edge_refs(edge)
        if (
            edge_type in _D_EXTENDED_EDGE_TYPES
            and _is_present_component(from_ref)
            and _is_present_component(to_ref)
            and from_ref in adjacency
            and to_ref in adjacency
        ):
            adjacency[from_ref].add((to_ref, edge_type))

    return {
        node_id: sorted(adjacency[node_id], key=lambda item: (item[0], item[1]))
        for node_id in sorted(adjacency)
    }


def _extended_cycle_kind(
    *,
    scope: _GraphScope,
    node_ids: list[str],
    edge_types: list[str],
) -> IntegrityCyclePolicyExtendedKind:
    if scope == "e_continuity":
        return "self_cycle" if len(node_ids) == 1 else "multi_node_cycle"
    return "exception_loop" if "excepts" in edge_types else "dependency_loop"


def _add_cycle(
    *,
    scope: _GraphScope,
    cycle_nodes: list[str],
    cycle_edge_types: list[str],
    cycle_map: dict[
        tuple[IntegrityCyclePolicyExtendedKind, str], AdeuIntegrityCyclePolicyExtendedCycle
    ],
) -> None:
    canonical_node_ids = _canonical_cycle_rotation(cycle_nodes)
    cycle_kind = _extended_cycle_kind(
        scope=scope,
        node_ids=canonical_node_ids,
        edge_types=cycle_edge_types,
    )
    signature = _cycle_signature(canonical_node_ids)
    cycle_key = (cycle_kind, signature)
    if cycle_key in cycle_map:
        return
    if len(cycle_map) >= _MAX_EMITTED_CYCLES:
        _raise_cycle_cap_error()

    cycle_map[cycle_key] = AdeuIntegrityCyclePolicyExtendedCycle(
        kind=cycle_kind,
        cycle_signature=signature,
        node_ids=canonical_node_ids,
    )


def _collect_cycles(
    *,
    scope: _GraphScope,
    adjacency: Mapping[str, list[tuple[str, str]]],
    cycle_map: dict[
        tuple[IntegrityCyclePolicyExtendedKind, str], AdeuIntegrityCyclePolicyExtendedCycle
    ],
) -> list[AdeuIntegrityCyclePolicyExtendedCycle]:
    def _walk(
        start_node_id: str,
        current_node_id: str,
        path_nodes: list[str],
        path_edge_types: list[str],
        in_path: set[str],
    ) -> None:
        for next_node_id, edge_type in adjacency.get(current_node_id, []):
            if next_node_id == start_node_id:
                _add_cycle(
                    scope=scope,
                    cycle_nodes=path_nodes,
                    cycle_edge_types=path_edge_types + [edge_type],
                    cycle_map=cycle_map,
                )
                continue
            if next_node_id in in_path:
                continue

            in_path.add(next_node_id)
            path_nodes.append(next_node_id)
            path_edge_types.append(edge_type)
            _walk(start_node_id, next_node_id, path_nodes, path_edge_types, in_path)
            path_edge_types.pop()
            path_nodes.pop()
            in_path.remove(next_node_id)

    for start_node_id in sorted(adjacency):
        _walk(start_node_id, start_node_id, [start_node_id], [], {start_node_id})
    return sorted(cycle_map.values(), key=_cycle_sort_key)


def build_integrity_cycle_policy_extended_diagnostics(
    payload: AdeuCoreIR | Mapping[str, Any],
) -> AdeuIntegrityCyclePolicyExtended:
    raw_payload: Mapping[str, Any]
    if isinstance(payload, AdeuCoreIR):
        raw_payload = payload.model_dump(mode="json", by_alias=True, exclude_none=False)
    else:
        raw_payload = payload

    source_text_hash = _extract_source_text_hash(raw_payload)
    node_layers = _collect_node_layers(raw_payload)
    edges = _extract_edges(raw_payload)

    e_adjacency = _build_e_depends_on_adjacency(node_layers=node_layers, edges=edges)
    d_adjacency = _build_d_extended_adjacency(node_layers=node_layers, edges=edges)
    cycle_map: dict[
        tuple[IntegrityCyclePolicyExtendedKind, str], AdeuIntegrityCyclePolicyExtendedCycle
    ] = {}
    _collect_cycles(scope="e_continuity", adjacency=e_adjacency, cycle_map=cycle_map)
    _collect_cycles(scope="d_extended", adjacency=d_adjacency, cycle_map=cycle_map)
    sorted_cycles = sorted(cycle_map.values(), key=_cycle_sort_key)

    counts: dict[IntegrityCyclePolicyExtendedKind, int] = {
        "self_cycle": 0,
        "multi_node_cycle": 0,
        "dependency_loop": 0,
        "exception_loop": 0,
    }
    for cycle in sorted_cycles:
        counts[cycle.kind] += 1

    return AdeuIntegrityCyclePolicyExtended(
        schema="adeu_integrity_cycle_policy_extended@0.1",
        source_text_hash=source_text_hash,
        summary=AdeuIntegrityCyclePolicyExtendedSummary(
            total_cycles=len(sorted_cycles),
            self_cycle=counts["self_cycle"],
            multi_node_cycle=counts["multi_node_cycle"],
            dependency_loop=counts["dependency_loop"],
            exception_loop=counts["exception_loop"],
        ),
        cycles=sorted_cycles,
    )


def canonicalize_integrity_cycle_policy_extended_payload(
    payload: AdeuIntegrityCyclePolicyExtended | Mapping[str, Any],
) -> dict[str, Any]:
    diagnostics = (
        payload
        if isinstance(payload, AdeuIntegrityCyclePolicyExtended)
        else AdeuIntegrityCyclePolicyExtended.model_validate(payload)
    )
    return diagnostics.model_dump(mode="json", by_alias=True, exclude_none=True)
