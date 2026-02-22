from __future__ import annotations

from typing import Any, Literal, Mapping

from pydantic import BaseModel, ConfigDict, Field, model_validator

from .lane_report import CANONICAL_LANE_ORDER, AdeuLaneReport
from .models import AdeuCoreIR, Layer

ReadSurfacePayloadSchemaVersion = Literal["adeu_read_surface_payload@0.1"]
MISSING_INTEGRITY_ARTIFACT_REASON = "ARTIFACT_NOT_FOUND"
FROZEN_READ_SURFACE_INTEGRITY_FAMILIES: tuple[str, ...] = (
    "dangling_reference",
    "cycle_policy",
    "deontic_conflict",
    "reference_integrity_extended",
    "cycle_policy_extended",
    "deontic_conflict_extended",
)
_INTEGRITY_SCHEMA_BY_FAMILY: dict[str, str] = {
    "dangling_reference": "adeu_integrity_dangling_reference@0.1",
    "cycle_policy": "adeu_integrity_cycle_policy@0.1",
    "deontic_conflict": "adeu_integrity_deontic_conflict@0.1",
    "reference_integrity_extended": "adeu_integrity_reference_integrity_extended@0.1",
    "cycle_policy_extended": "adeu_integrity_cycle_policy_extended@0.1",
    "deontic_conflict_extended": "adeu_integrity_deontic_conflict_extended@0.1",
}
_CANONICAL_LANE_KEYS = list(CANONICAL_LANE_ORDER)


def _validate_lane_key_order(*, field_name: str, value: dict[Layer, Any]) -> None:
    keys = list(value.keys())
    if keys != _CANONICAL_LANE_KEYS:
        raise ValueError(
            f"{field_name} must include lane keys in canonical order {_CANONICAL_LANE_KEYS}"
        )


def integrity_issue_count(payload: dict[str, Any] | None) -> int:
    if payload is None:
        return 0
    summary = payload.get("summary")
    if isinstance(summary, dict):
        for key in ("total_issues", "total_cycles", "total_conflicts"):
            value = summary.get(key)
            if isinstance(value, int) and value >= 0:
                return value
    for key in ("issues", "cycles", "conflicts"):
        value = payload.get(key)
        if isinstance(value, list):
            return len(value)
    return 0


class AdeuLaneProjectionEdge(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    type: str = Field(min_length=1)
    from_ref: str = Field(alias="from", min_length=1)
    to_ref: str = Field(alias="to", min_length=1)


class AdeuLaneProjection(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: Literal["adeu_lane_projection@0.1"] = "adeu_lane_projection@0.1"
    source_text_hash: str
    lanes: dict[Layer, list[str]]
    edges: list[AdeuLaneProjectionEdge] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuLaneProjection":
        _validate_lane_key_order(field_name="lanes", value=self.lanes)
        for lane in CANONICAL_LANE_ORDER:
            node_ids = self.lanes[lane]
            if any(not node_id for node_id in node_ids):
                raise ValueError(f"lanes[{lane}] may not contain empty node ids")
            if len(set(node_ids)) != len(node_ids):
                raise ValueError(f"lanes[{lane}] may not contain duplicate node ids")
            if node_ids != sorted(node_ids):
                raise ValueError(f"lanes[{lane}] must be sorted lexicographically")
        edge_identities = [(edge.type, edge.from_ref, edge.to_ref) for edge in self.edges]
        if edge_identities != sorted(edge_identities):
            raise ValueError("edges must be sorted by (type, from, to)")
        if len(set(edge_identities)) != len(edge_identities):
            raise ValueError("edges may not contain duplicate (type, from, to) identities")
        return self


class AdeuReadSurfaceIntegrityFamilyArtifact(BaseModel):
    model_config = ConfigDict(extra="forbid")

    artifact: dict[str, Any] | None = None
    missing_reason: Literal["ARTIFACT_NOT_FOUND"] | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuReadSurfaceIntegrityFamilyArtifact":
        if self.artifact is None:
            if self.missing_reason != MISSING_INTEGRITY_ARTIFACT_REASON:
                raise ValueError(
                    "missing integrity artifact requires missing_reason=ARTIFACT_NOT_FOUND"
                )
            return self
        if self.missing_reason is not None:
            raise ValueError("present integrity artifact may not include missing_reason")
        return self


class AdeuReadSurfaceCorrelationLaneRef(BaseModel):
    model_config = ConfigDict(extra="forbid")

    source: Literal["lane_projection", "lane_report"]
    lane: Layer


class AdeuReadSurfaceCorrelationIntegrityRef(BaseModel):
    model_config = ConfigDict(extra="forbid")

    family: str = Field(min_length=1)
    kind: str = Field(min_length=1)
    role: str = Field(min_length=1)
    reference_id: str = Field(min_length=1)


class AdeuReadSurfaceNodeCorrelation(BaseModel):
    model_config = ConfigDict(extra="forbid")

    lane_refs: list[AdeuReadSurfaceCorrelationLaneRef] = Field(default_factory=list)
    integrity_refs: list[AdeuReadSurfaceCorrelationIntegrityRef] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuReadSurfaceNodeCorrelation":
        lane_ref_identities = [(item.source, item.lane) for item in self.lane_refs]
        if lane_ref_identities != sorted(lane_ref_identities):
            raise ValueError("lane_refs must be sorted by (source, lane)")
        if len(set(lane_ref_identities)) != len(lane_ref_identities):
            raise ValueError("lane_refs may not contain duplicate (source, lane) entries")
        integrity_ref_identities = [
            (item.family, item.kind, item.role, item.reference_id) for item in self.integrity_refs
        ]
        if integrity_ref_identities != sorted(integrity_ref_identities):
            raise ValueError("integrity_refs must be sorted by (family, kind, role, reference_id)")
        if len(set(integrity_ref_identities)) != len(integrity_ref_identities):
            raise ValueError("integrity_refs may not contain duplicate entries")
        return self


class AdeuReadSurfaceRenderSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")

    core_ir_node_count: int = Field(ge=0)
    core_ir_edge_count: int = Field(ge=0)
    lane_projection_edge_count: int = Field(ge=0)
    lane_node_counts: dict[Layer, int]
    lane_edge_counts: dict[Layer, int]
    integrity_present_family_count: int = Field(ge=0)
    integrity_missing_family_count: int = Field(ge=0)
    integrity_issue_counts: dict[str, int]

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuReadSurfaceRenderSummary":
        _validate_lane_key_order(field_name="lane_node_counts", value=self.lane_node_counts)
        _validate_lane_key_order(field_name="lane_edge_counts", value=self.lane_edge_counts)
        if any(value < 0 for value in self.lane_node_counts.values()):
            raise ValueError("lane_node_counts values must be >= 0")
        if any(value < 0 for value in self.lane_edge_counts.values()):
            raise ValueError("lane_edge_counts values must be >= 0")
        expected_families = list(FROZEN_READ_SURFACE_INTEGRITY_FAMILIES)
        if list(self.integrity_issue_counts.keys()) != expected_families:
            raise ValueError(
                "integrity_issue_counts must include families in canonical order "
                f"{expected_families}"
            )
        if any(value < 0 for value in self.integrity_issue_counts.values()):
            raise ValueError("integrity_issue_counts values must be >= 0")
        total_families = len(FROZEN_READ_SURFACE_INTEGRITY_FAMILIES)
        if (
            self.integrity_present_family_count + self.integrity_missing_family_count
        ) != total_families:
            raise ValueError(
                "integrity_present_family_count + integrity_missing_family_count must equal "
                f"{total_families}"
            )
        return self


class AdeuReadSurfacePayload(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: ReadSurfacePayloadSchemaVersion = "adeu_read_surface_payload@0.1"
    artifact_id: str = Field(min_length=1)
    source_text_hash: str = Field(min_length=1)
    core_ir: AdeuCoreIR
    lane_projection: AdeuLaneProjection
    lane_report: AdeuLaneReport
    integrity: dict[str, AdeuReadSurfaceIntegrityFamilyArtifact]
    render_summary: AdeuReadSurfaceRenderSummary
    correlations: dict[str, AdeuReadSurfaceNodeCorrelation] | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuReadSurfacePayload":
        if self.core_ir.source_text_hash != self.source_text_hash:
            raise ValueError("core_ir.source_text_hash must equal source_text_hash")
        if self.lane_projection.source_text_hash != self.source_text_hash:
            raise ValueError("lane_projection.source_text_hash must equal source_text_hash")
        if self.lane_report.source_text_hash != self.source_text_hash:
            raise ValueError("lane_report.source_text_hash must equal source_text_hash")

        expected_families = list(FROZEN_READ_SURFACE_INTEGRITY_FAMILIES)
        if list(self.integrity.keys()) != expected_families:
            raise ValueError(
                f"integrity must include frozen family keys in order {expected_families}"
            )
        for family in FROZEN_READ_SURFACE_INTEGRITY_FAMILIES:
            entry = self.integrity[family]
            artifact = entry.artifact
            if artifact is None:
                continue
            expected_schema = _INTEGRITY_SCHEMA_BY_FAMILY[family]
            if artifact.get("schema") != expected_schema:
                raise ValueError(
                    f"integrity[{family}] schema must equal {expected_schema!r} when present"
                )
            if artifact.get("source_text_hash") != self.source_text_hash:
                raise ValueError(
                    f"integrity[{family}] source_text_hash must equal top-level source_text_hash"
                )

        lane_projection_node_counts = {
            lane: len(self.lane_projection.lanes[lane]) for lane in CANONICAL_LANE_ORDER
        }
        lane_report_node_counts = {
            lane: len(self.lane_report.lane_nodes[lane]) for lane in CANONICAL_LANE_ORDER
        }
        if lane_projection_node_counts != lane_report_node_counts:
            raise ValueError("lane_projection and lane_report node coverage must match")
        if self.render_summary.lane_node_counts != lane_projection_node_counts:
            raise ValueError("render_summary.lane_node_counts mismatch")

        lane_report_edge_counts = {
            lane: int(self.lane_report.lane_edge_counts[lane]) for lane in CANONICAL_LANE_ORDER
        }
        if self.render_summary.lane_edge_counts != lane_report_edge_counts:
            raise ValueError("render_summary.lane_edge_counts mismatch")

        if self.render_summary.core_ir_node_count != len(self.core_ir.nodes):
            raise ValueError("render_summary.core_ir_node_count mismatch")
        if self.render_summary.core_ir_edge_count != len(self.core_ir.edges):
            raise ValueError("render_summary.core_ir_edge_count mismatch")
        if self.render_summary.lane_projection_edge_count != len(self.lane_projection.edges):
            raise ValueError("render_summary.lane_projection_edge_count mismatch")

        expected_issue_counts = {
            family: integrity_issue_count(self.integrity[family].artifact)
            for family in FROZEN_READ_SURFACE_INTEGRITY_FAMILIES
        }
        if self.render_summary.integrity_issue_counts != expected_issue_counts:
            raise ValueError("render_summary.integrity_issue_counts mismatch")
        present_count = sum(
            1
            for family in FROZEN_READ_SURFACE_INTEGRITY_FAMILIES
            if self.integrity[family].artifact is not None
        )
        if self.render_summary.integrity_present_family_count != present_count:
            raise ValueError("render_summary.integrity_present_family_count mismatch")
        if self.render_summary.integrity_missing_family_count != (
            len(FROZEN_READ_SURFACE_INTEGRITY_FAMILIES) - present_count
        ):
            raise ValueError("render_summary.integrity_missing_family_count mismatch")

        node_ids = sorted(node.id for node in self.core_ir.nodes)
        if self.correlations is not None:
            if list(self.correlations.keys()) != node_ids:
                raise ValueError("correlations must be keyed by sorted core_ir node ids")
            for node_id, correlation in self.correlations.items():
                lane_projection_lanes = self.lane_projection.lanes
                lane_report_lanes = self.lane_report.lane_nodes
                for lane_ref in correlation.lane_refs:
                    if lane_ref.source == "lane_projection":
                        if node_id not in lane_projection_lanes[lane_ref.lane]:
                            raise ValueError(
                                "correlations lane_projection reference points to a non-member node"
                            )
                    else:
                        if node_id not in lane_report_lanes[lane_ref.lane]:
                            raise ValueError(
                                "correlations lane_report reference points to a non-member node"
                            )
                for integrity_ref in correlation.integrity_refs:
                    if integrity_ref.family not in self.integrity:
                        raise ValueError("correlations references an unknown integrity family")
        return self


def canonicalize_read_surface_payload(
    payload: AdeuReadSurfacePayload | Mapping[str, Any],
) -> dict[str, Any]:
    normalized = (
        payload
        if isinstance(payload, AdeuReadSurfacePayload)
        else AdeuReadSurfacePayload.model_validate(payload)
    )
    normalized_payload = normalized.model_dump(mode="json", by_alias=True, exclude_none=True)
    integrity = normalized_payload.get("integrity")
    if isinstance(integrity, dict):
        for family in FROZEN_READ_SURFACE_INTEGRITY_FAMILIES:
            entry = integrity.get(family)
            if isinstance(entry, dict) and "artifact" not in entry:
                entry["artifact"] = None
    return normalized_payload
