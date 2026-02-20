from __future__ import annotations

from typing import Any, Literal, Mapping

from pydantic import BaseModel, ConfigDict, Field, model_validator

from .models import AdeuCoreIR

IntegrityCyclePolicySchemaVersion = Literal["adeu_integrity_cycle_policy@0.1"]
IntegrityCycleKind = Literal["self_cycle", "multi_node_cycle"]

_MAX_EMITTED_CYCLES = 1000


def _cycle_signature(node_ids: list[str]) -> str:
    return "cycle:" + "->".join(node_ids)


def _canonical_cycle_rotation(node_ids: list[str]) -> list[str]:
    if len(node_ids) <= 1:
        return list(node_ids)

    rotations = [node_ids[index:] + node_ids[:index] for index in range(len(node_ids))]
    return min(rotations)


def _cycle_sort_key(cycle: "AdeuIntegrityCyclePolicyCycle") -> str:
    return cycle.cycle_signature


class AdeuIntegrityCyclePolicySummary(BaseModel):
    model_config = ConfigDict(extra="forbid")

    total_cycles: int
    self_cycle: int
    multi_node_cycle: int

    @model_validator(mode="after")
    def _validate_total(self) -> "AdeuIntegrityCyclePolicySummary":
        expected_total = self.self_cycle + self.multi_node_cycle
        if self.total_cycles != expected_total:
            raise ValueError("summary.total_cycles must equal the sum of cycle counts")
        return self


class AdeuIntegrityCyclePolicyCycle(BaseModel):
    model_config = ConfigDict(extra="forbid")

    kind: IntegrityCycleKind
    cycle_signature: str
    node_ids: list[str]

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuIntegrityCyclePolicyCycle":
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

        expected_kind: IntegrityCycleKind = (
            "self_cycle" if len(self.node_ids) == 1 else "multi_node_cycle"
        )
        if self.kind != expected_kind:
            raise ValueError("cycle.kind must match cycle length classification")
        return self


class AdeuIntegrityCyclePolicy(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: IntegrityCyclePolicySchemaVersion = "adeu_integrity_cycle_policy@0.1"
    source_text_hash: str
    summary: AdeuIntegrityCyclePolicySummary
    cycles: list[AdeuIntegrityCyclePolicyCycle] = Field(default_factory=list)
    metadata: dict[str, Any] | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuIntegrityCyclePolicy":
        sorted_cycles = sorted(self.cycles, key=_cycle_sort_key)
        if self.cycles != sorted_cycles:
            raise ValueError("cycles must be sorted by cycle_signature")

        counts: dict[IntegrityCycleKind, int] = {
            "self_cycle": 0,
            "multi_node_cycle": 0,
        }
        for cycle in self.cycles:
            counts[cycle.kind] += 1

        expected_summary = {
            "total_cycles": len(self.cycles),
            "self_cycle": counts["self_cycle"],
            "multi_node_cycle": counts["multi_node_cycle"],
        }
        actual_summary = self.summary.model_dump(mode="json")
        if actual_summary != expected_summary:
            raise ValueError("summary counts must match cycles list counts exactly")
        return self


def _depends_on_adjacency(core_ir: AdeuCoreIR) -> dict[str, list[str]]:
    adjacency: dict[str, set[str]] = {
        node.id: set() for node in core_ir.nodes if node.layer == "E"
    }

    for edge in core_ir.edges:
        if (
            edge.type == "depends_on"
            and edge.from_ref in adjacency
            and edge.to_ref in adjacency
        ):
            adjacency[edge.from_ref].add(edge.to_ref)

    return {node_id: sorted(targets) for node_id, targets in adjacency.items()}


def _raise_cycle_cap_error() -> None:
    raise ValueError("URM_ADEU_INTEGRITY_FIXTURE_INVALID: cycle diagnostics exceeded cap")


def _add_cycle(
    *,
    cycle_nodes: list[str],
    cycle_map: dict[str, AdeuIntegrityCyclePolicyCycle],
) -> None:
    canonical_node_ids = _canonical_cycle_rotation(cycle_nodes)
    signature = _cycle_signature(canonical_node_ids)
    if signature in cycle_map:
        return
    if len(cycle_map) >= _MAX_EMITTED_CYCLES:
        _raise_cycle_cap_error()

    cycle_kind: IntegrityCycleKind = (
        "self_cycle" if len(canonical_node_ids) == 1 else "multi_node_cycle"
    )
    cycle_map[signature] = AdeuIntegrityCyclePolicyCycle.model_validate(
        {
            "kind": cycle_kind,
            "cycle_signature": signature,
            "node_ids": canonical_node_ids,
        }
    )


def _collect_cycles(adjacency: Mapping[str, list[str]]) -> list[AdeuIntegrityCyclePolicyCycle]:
    cycle_map: dict[str, AdeuIntegrityCyclePolicyCycle] = {}

    def _walk(start_node_id: str, current_node_id: str, path: list[str], in_path: set[str]) -> None:
        for next_node_id in adjacency.get(current_node_id, []):
            if next_node_id == start_node_id:
                _add_cycle(cycle_nodes=path, cycle_map=cycle_map)
                continue
            if next_node_id in in_path:
                continue
            in_path.add(next_node_id)
            path.append(next_node_id)
            _walk(start_node_id, next_node_id, path, in_path)
            path.pop()
            in_path.remove(next_node_id)

    for start_node_id in sorted(adjacency):
        _walk(start_node_id, start_node_id, [start_node_id], {start_node_id})

    return sorted(cycle_map.values(), key=_cycle_sort_key)


def build_integrity_cycle_policy_diagnostics(
    payload: AdeuCoreIR | Mapping[str, Any],
) -> AdeuIntegrityCyclePolicy:
    core_ir = payload if isinstance(payload, AdeuCoreIR) else AdeuCoreIR.model_validate(payload)
    adjacency = _depends_on_adjacency(core_ir)
    cycles = _collect_cycles(adjacency)

    counts: dict[IntegrityCycleKind, int] = {
        "self_cycle": 0,
        "multi_node_cycle": 0,
    }
    for cycle in cycles:
        counts[cycle.kind] += 1

    return AdeuIntegrityCyclePolicy.model_validate(
        {
            "schema": "adeu_integrity_cycle_policy@0.1",
            "source_text_hash": core_ir.source_text_hash,
            "summary": {
                "total_cycles": len(cycles),
                "self_cycle": counts["self_cycle"],
                "multi_node_cycle": counts["multi_node_cycle"],
            },
            "cycles": [
                cycle.model_dump(mode="json", by_alias=True, exclude_none=True)
                for cycle in cycles
            ],
        }
    )


def canonicalize_integrity_cycle_policy_payload(
    payload: AdeuIntegrityCyclePolicy | Mapping[str, Any],
) -> dict[str, Any]:
    diagnostics = (
        payload
        if isinstance(payload, AdeuIntegrityCyclePolicy)
        else AdeuIntegrityCyclePolicy.model_validate(payload)
    )
    return diagnostics.model_dump(mode="json", by_alias=True, exclude_none=True)
