from __future__ import annotations

from typing import Any, Literal, Mapping

from pydantic import BaseModel, ConfigDict, model_validator

from .models import AdeuCoreIR, Layer

LaneReportSchemaVersion = Literal["adeu_lane_report@0.1"]
CANONICAL_LANE_ORDER: tuple[Layer, Layer, Layer, Layer] = ("O", "E", "D", "U")
_CANONICAL_LANE_KEYS = list(CANONICAL_LANE_ORDER)


def _default_lane_edge_counts() -> dict[Layer, int]:
    return {lane: 0 for lane in CANONICAL_LANE_ORDER}


def _validate_lane_keys(*, field_name: str, value: dict[Layer, Any]) -> None:
    keys = list(value.keys())
    if keys != _CANONICAL_LANE_KEYS:
        raise ValueError(
            f"{field_name} must include lane keys in canonical order {_CANONICAL_LANE_KEYS}"
        )


class AdeuLaneReport(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: LaneReportSchemaVersion = "adeu_lane_report@0.1"
    source_text_hash: str
    lane_nodes: dict[Layer, list[str]]
    lane_edge_counts: dict[Layer, int]
    metadata: dict[str, Any] | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuLaneReport":
        _validate_lane_keys(field_name="lane_nodes", value=self.lane_nodes)
        _validate_lane_keys(field_name="lane_edge_counts", value=self.lane_edge_counts)

        for lane in CANONICAL_LANE_ORDER:
            node_ids = self.lane_nodes[lane]
            if any(not node_id for node_id in node_ids):
                raise ValueError(f"lane_nodes[{lane}] may not contain empty node ids")
            if len(set(node_ids)) != len(node_ids):
                raise ValueError(f"lane_nodes[{lane}] contains duplicate node ids")
            if node_ids != sorted(node_ids):
                raise ValueError(f"lane_nodes[{lane}] must be sorted lexicographically")

            edge_count = self.lane_edge_counts[lane]
            if edge_count < 0:
                raise ValueError(f"lane_edge_counts[{lane}] must be >= 0")

        return self


def build_lane_report(core_ir: AdeuCoreIR | Mapping[str, Any]) -> AdeuLaneReport:
    ir = core_ir if isinstance(core_ir, AdeuCoreIR) else AdeuCoreIR.model_validate(core_ir)

    lane_nodes: dict[Layer, list[str]] = {lane: [] for lane in CANONICAL_LANE_ORDER}
    node_lane: dict[str, Layer] = {}
    for node in ir.nodes:
        lane_nodes[node.layer].append(node.id)
        node_lane[node.id] = node.layer

    lane_nodes = {lane: sorted(node_ids) for lane, node_ids in lane_nodes.items()}
    lane_edge_counts: dict[Layer, int] = _default_lane_edge_counts()
    for edge in ir.edges:
        source_lane = node_lane.get(edge.from_ref)
        if source_lane is None:
            raise ValueError(
                "edge source node has unmapped lane: "
                f"edge_from={edge.from_ref} edge_type={edge.type}"
            )
        lane_edge_counts[source_lane] += 1

    return AdeuLaneReport.model_validate(
        {
            "schema": "adeu_lane_report@0.1",
            "source_text_hash": ir.source_text_hash,
            "lane_nodes": lane_nodes,
            "lane_edge_counts": lane_edge_counts,
        }
    )


def canonicalize_lane_report_payload(payload: AdeuLaneReport | Mapping[str, Any]) -> dict[str, Any]:
    report = (
        payload
        if isinstance(payload, AdeuLaneReport)
        else AdeuLaneReport.model_validate(payload)
    )
    return report.model_dump(mode="json", by_alias=True, exclude_none=True)
