from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from adeu_core_ir import FROZEN_READ_SURFACE_INTEGRITY_FAMILIES

from .read_surface_payload_vnext_plus19 import (
    build_read_surface_payload_vnext_plus19,
    list_read_surface_catalog_artifact_ids_vnext_plus19,
)

READ_SURFACE_TRANSFER_REPORT_VNEXT_PLUS19_SCHEMA = "read_surface_transfer_report.vnext_plus19@1"
_FROZEN_READ_SURFACE_IDS: tuple[str, ...] = (
    "adeu.read_surface.core_ir",
    "adeu.read_surface.lane",
    "adeu.read_surface.integrity",
)
_HEX64_RE = re.compile(r"^[0-9a-f]{64}$")
_CANONICAL_LANES: tuple[str, ...] = ("O", "E", "D", "U")


class ReadSurfaceTransferReportVnextPlus19Error(ValueError):
    """Raised when vNext+19 read-surface transfer-report inputs are invalid."""


def _validate_manifest_hash(value: str) -> str:
    normalized = value.strip().lower()
    if not _HEX64_RE.fullmatch(normalized):
        raise ReadSurfaceTransferReportVnextPlus19Error(
            "vnext_plus19_manifest_hash must be a lowercase sha256 hex digest"
        )
    return normalized


def _normalize_artifact_ids(artifact_ids: list[str]) -> list[str]:
    normalized = [artifact_id.strip() for artifact_id in artifact_ids if artifact_id.strip()]
    if not normalized:
        raise ReadSurfaceTransferReportVnextPlus19Error("artifact_ids must not be empty")
    if len(set(normalized)) != len(normalized):
        raise ReadSurfaceTransferReportVnextPlus19Error("artifact_ids may not contain duplicates")
    return sorted(normalized)


def build_read_surface_transfer_report_vnext_plus19_payload(
    *,
    vnext_plus19_manifest_hash: str,
    artifact_ids: list[str] | None = None,
    include_correlations: bool = False,
    catalog_path: Path | None = None,
) -> dict[str, Any]:
    manifest_hash = _validate_manifest_hash(vnext_plus19_manifest_hash)
    if artifact_ids is None:
        normalized_artifact_ids = list_read_surface_catalog_artifact_ids_vnext_plus19(
            catalog_path=catalog_path,
        )
    else:
        normalized_artifact_ids = _normalize_artifact_ids(artifact_ids)
    if not normalized_artifact_ids:
        raise ReadSurfaceTransferReportVnextPlus19Error(
            "catalog does not include any read-surface entries"
        )

    total_core_nodes = 0
    total_core_edges = 0
    total_lane_projection_edges = 0
    lane_node_totals = {lane: 0 for lane in _CANONICAL_LANES}
    lane_edge_totals = {lane: 0 for lane in _CANONICAL_LANES}
    family_present_counts = {family: 0 for family in FROZEN_READ_SURFACE_INTEGRITY_FAMILIES}
    family_missing_counts = {family: 0 for family in FROZEN_READ_SURFACE_INTEGRITY_FAMILIES}
    family_issue_totals = {family: 0 for family in FROZEN_READ_SURFACE_INTEGRITY_FAMILIES}

    for artifact_id in normalized_artifact_ids:
        payload = build_read_surface_payload_vnext_plus19(
            artifact_id=artifact_id,
            include_correlations=include_correlations,
            catalog_path=catalog_path,
        )
        render_summary = payload["render_summary"]
        total_core_nodes += int(render_summary["core_ir_node_count"])
        total_core_edges += int(render_summary["core_ir_edge_count"])
        total_lane_projection_edges += int(render_summary["lane_projection_edge_count"])
        for lane in _CANONICAL_LANES:
            lane_node_totals[lane] += int(render_summary["lane_node_counts"][lane])
            lane_edge_totals[lane] += int(render_summary["lane_edge_counts"][lane])
        integrity_payload = payload["integrity"]
        for family in FROZEN_READ_SURFACE_INTEGRITY_FAMILIES:
            artifact_payload = integrity_payload[family]["artifact"]
            if artifact_payload is None:
                family_missing_counts[family] += 1
            else:
                family_present_counts[family] += 1
            family_issue_totals[family] += int(render_summary["integrity_issue_counts"][family])

    artifact_count = len(normalized_artifact_ids)
    coverage_surfaces = [
        {"surface_id": "adeu.read_surface.core_ir", "artifact_count": artifact_count},
        {"surface_id": "adeu.read_surface.lane", "artifact_count": artifact_count},
        {"surface_id": "adeu.read_surface.integrity", "artifact_count": artifact_count},
    ]
    return {
        "schema": READ_SURFACE_TRANSFER_REPORT_VNEXT_PLUS19_SCHEMA,
        "vnext_plus19_manifest_hash": manifest_hash,
        "coverage_summary": {
            "valid": True,
            "surface_count": len(_FROZEN_READ_SURFACE_IDS),
            "covered_surface_count": len(_FROZEN_READ_SURFACE_IDS),
            "coverage_pct": 100.0,
            "surfaces": coverage_surfaces,
        },
        "core_ir_read_surface_summary": {
            "valid": True,
            "artifact_count": artifact_count,
            "total_nodes": total_core_nodes,
            "total_edges": total_core_edges,
        },
        "lane_read_surface_summary": {
            "valid": True,
            "artifact_count": artifact_count,
            "total_lane_projection_edges": total_lane_projection_edges,
            "lane_node_totals": lane_node_totals,
            "lane_edge_totals": lane_edge_totals,
        },
        "integrity_read_surface_summary": {
            "valid": True,
            "artifact_count": artifact_count,
            "family_present_counts": family_present_counts,
            "family_missing_counts": family_missing_counts,
            "family_issue_totals": family_issue_totals,
        },
        "replay_summary": {
            "valid": True,
            "replay_count": 1,
            "fixture_counts": {
                "core_ir_read_surface": artifact_count,
                "lane_read_surface": artifact_count,
                "integrity_read_surface": artifact_count,
            },
            "replay_unit_counts": {
                "core_ir_read_surface": artifact_count,
                "lane_read_surface": artifact_count,
                "integrity_read_surface": (
                    artifact_count * len(FROZEN_READ_SURFACE_INTEGRITY_FAMILIES)
                ),
            },
        },
    }


def read_surface_transfer_report_vnext_plus19_markdown(payload: dict[str, Any]) -> str:
    rendered_payload = json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True)
    lines: list[str] = [
        "# Read Surface Transfer Report vNext+19",
        "",
        (
            "Deterministic R2 transfer summary generated from fixture-backed "
            "vNext+19 read-surface payloads."
        ),
        "",
        "```json",
        rendered_payload,
        "```",
        "",
    ]
    return "\n".join(lines)
