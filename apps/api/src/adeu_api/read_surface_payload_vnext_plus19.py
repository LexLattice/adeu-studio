from __future__ import annotations

from collections import defaultdict
from collections.abc import Iterator
from contextlib import contextmanager
from pathlib import Path
from typing import Any, cast

from adeu_core_ir import (
    FROZEN_READ_SURFACE_INTEGRITY_FAMILIES,
    MISSING_INTEGRITY_ARTIFACT_REASON,
    AdeuReadSurfacePayload,
    canonicalize_read_surface_payload,
)
from fastapi import HTTPException, Response

from . import main as api_main

READ_SURFACE_PAYLOAD_VNEXT_PLUS19_SCHEMA = "adeu_read_surface_payload@0.1"
_CANONICAL_LANES: tuple[str, ...] = ("O", "E", "D", "U")


class ReadSurfacePayloadVnextPlus19Error(ValueError):
    """Raised when vNext+19 read-surface payload inputs are invalid."""


@contextmanager
def _catalog_path_override(catalog_path: Path | None) -> Iterator[None]:
    if catalog_path is None:
        yield
        return
    previous = api_main._READ_SURFACE_CATALOG_PATH
    api_main._READ_SURFACE_CATALOG_PATH = Path(catalog_path)
    api_main._read_surface_catalog_index.cache_clear()
    try:
        yield
    finally:
        api_main._READ_SURFACE_CATALOG_PATH = previous
        api_main._read_surface_catalog_index.cache_clear()


def _is_artifact_not_found_http(exc: HTTPException) -> bool:
    detail = exc.detail if isinstance(exc.detail, dict) else {}
    return (
        exc.status_code == 404
        and detail.get("code") == "URM_ADEU_READ_SURFACE_ARTIFACT_NOT_FOUND"
    )


def _as_read_surface_payload_error(
    exc: HTTPException,
    *,
    artifact_id: str,
) -> ReadSurfacePayloadVnextPlus19Error:
    detail = exc.detail if isinstance(exc.detail, dict) else {"detail": str(exc.detail)}
    code = detail.get("code")
    reason = detail.get("reason", detail.get("message", "read-surface endpoint error"))
    return ReadSurfacePayloadVnextPlus19Error(
        f"artifact_id={artifact_id!r} endpoint failed status={exc.status_code} code={code!r} "
        f"reason={reason!r}"
    )


def _integrity_issue_count(payload: dict[str, Any] | None) -> int:
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


def _build_integrity_payload(
    *,
    artifact_id: str,
) -> tuple[dict[str, dict[str, Any]], dict[str, dict[str, Any] | None]]:
    render_integrity: dict[str, dict[str, Any]] = {}
    raw_integrity: dict[str, dict[str, Any] | None] = {}
    for family in FROZEN_READ_SURFACE_INTEGRITY_FAMILIES:
        try:
            response = api_main.get_urm_core_ir_integrity_endpoint(
                artifact_id=artifact_id,
                family=family,
                response=Response(),
            ).model_dump(mode="json")
        except HTTPException as exc:
            if _is_artifact_not_found_http(exc):
                render_integrity[family] = {
                    "artifact": None,
                    "missing_reason": MISSING_INTEGRITY_ARTIFACT_REASON,
                }
                raw_integrity[family] = None
                continue
            raise _as_read_surface_payload_error(exc, artifact_id=artifact_id) from exc
        integrity_artifact = response["integrity_artifact"]
        render_integrity[family] = {"artifact": integrity_artifact}
        raw_integrity[family] = integrity_artifact
    return render_integrity, raw_integrity


def _build_render_summary(
    *,
    core_ir: dict[str, Any],
    lane_projection: dict[str, Any],
    lane_report: dict[str, Any],
    integrity_payload_by_family: dict[str, dict[str, Any] | None],
) -> dict[str, Any]:
    lane_node_counts = {
        lane: len(cast(list[str], lane_projection["lanes"][lane])) for lane in _CANONICAL_LANES
    }
    lane_edge_counts = {
        lane: int(lane_report["lane_edge_counts"][lane]) for lane in _CANONICAL_LANES
    }
    integrity_issue_counts = {
        family: _integrity_issue_count(integrity_payload_by_family[family])
        for family in FROZEN_READ_SURFACE_INTEGRITY_FAMILIES
    }
    present_integrity_count = sum(
        1
        for family in FROZEN_READ_SURFACE_INTEGRITY_FAMILIES
        if integrity_payload_by_family[family]
    )
    return {
        "core_ir_node_count": len(cast(list[dict[str, Any]], core_ir["nodes"])),
        "core_ir_edge_count": len(cast(list[dict[str, Any]], core_ir["edges"])),
        "lane_projection_edge_count": len(cast(list[dict[str, Any]], lane_projection["edges"])),
        "lane_node_counts": lane_node_counts,
        "lane_edge_counts": lane_edge_counts,
        "integrity_present_family_count": present_integrity_count,
        "integrity_missing_family_count": (
            len(FROZEN_READ_SURFACE_INTEGRITY_FAMILIES) - present_integrity_count
        ),
        "integrity_issue_counts": integrity_issue_counts,
    }


def _extract_integrity_refs_for_node(
    *,
    family: str,
    artifact: dict[str, Any] | None,
    node_id: str,
) -> list[dict[str, str]]:
    if artifact is None:
        return []
    refs: list[dict[str, str]] = []
    issues = artifact.get("issues")
    if isinstance(issues, list):
        for issue in issues:
            if not isinstance(issue, dict):
                continue
            kind = str(issue.get("kind", "issue"))
            subject_id = issue.get("subject_id")
            related_id = issue.get("related_id")
            if subject_id == node_id:
                refs.append(
                    {
                        "family": family,
                        "kind": kind,
                        "role": "subject_id",
                        "reference_id": str(subject_id),
                    }
                )
            if related_id == node_id:
                refs.append(
                    {
                        "family": family,
                        "kind": kind,
                        "role": "related_id",
                        "reference_id": str(related_id),
                    }
                )
    conflicts = artifact.get("conflicts")
    if isinstance(conflicts, list):
        for conflict in conflicts:
            if not isinstance(conflict, dict):
                continue
            kind = str(conflict.get("kind", "conflict"))
            primary_id = conflict.get("primary_id")
            related_id = conflict.get("related_id")
            if primary_id == node_id:
                refs.append(
                    {
                        "family": family,
                        "kind": kind,
                        "role": "primary_id",
                        "reference_id": str(primary_id),
                    }
                )
            if related_id == node_id:
                refs.append(
                    {
                        "family": family,
                        "kind": kind,
                        "role": "related_id",
                        "reference_id": str(related_id),
                    }
                )
    cycles = artifact.get("cycles")
    if isinstance(cycles, list):
        for cycle in cycles:
            if not isinstance(cycle, dict):
                continue
            node_ids = cycle.get("node_ids")
            if not isinstance(node_ids, list):
                continue
            if node_id not in node_ids:
                continue
            refs.append(
                {
                    "family": family,
                    "kind": str(cycle.get("kind", "cycle")),
                    "role": "node_ids",
                    "reference_id": str(cycle.get("cycle_signature", node_id)),
                }
            )
    unique_refs = {
        (item["family"], item["kind"], item["role"], item["reference_id"]) for item in refs
    }
    return [
        {"family": family, "kind": kind, "role": role, "reference_id": reference_id}
        for family, kind, role, reference_id in sorted(unique_refs)
    ]


def _build_correlations(
    *,
    core_ir: dict[str, Any],
    lane_projection: dict[str, Any],
    lane_report: dict[str, Any],
    integrity_payload_by_family: dict[str, dict[str, Any] | None],
) -> dict[str, dict[str, Any]]:
    lane_membership: dict[str, list[tuple[str, str]]] = defaultdict(list)
    for lane in _CANONICAL_LANES:
        projection_nodes = lane_projection["lanes"][lane]
        report_nodes = lane_report["lane_nodes"][lane]
        for node_id in projection_nodes:
            lane_membership[node_id].append(("lane_projection", lane))
        for node_id in report_nodes:
            lane_membership[node_id].append(("lane_report", lane))

    node_ids = sorted(str(node["id"]) for node in core_ir["nodes"] if isinstance(node, dict))
    correlations: dict[str, dict[str, Any]] = {}
    for node_id in node_ids:
        lane_refs = [
            {"source": source, "lane": lane}
            for source, lane in sorted(set(lane_membership.get(node_id, [])))
        ]
        integrity_refs: list[dict[str, str]] = []
        for family in FROZEN_READ_SURFACE_INTEGRITY_FAMILIES:
            integrity_refs.extend(
                _extract_integrity_refs_for_node(
                    family=family,
                    artifact=integrity_payload_by_family[family],
                    node_id=node_id,
                )
            )
        integrity_refs = sorted(
            integrity_refs,
            key=lambda item: (
                item["family"],
                item["kind"],
                item["role"],
                item["reference_id"],
            ),
        )
        correlations[node_id] = {
            "lane_refs": lane_refs,
            "integrity_refs": integrity_refs,
        }
    return correlations


def list_read_surface_catalog_artifact_ids_vnext_plus19(
    *,
    catalog_path: Path | None = None,
) -> list[str]:
    with _catalog_path_override(catalog_path):
        try:
            index = api_main._read_surface_catalog_index_or_http()
        except HTTPException as exc:
            raise _as_read_surface_payload_error(exc, artifact_id="<catalog>") from exc
    return sorted(index.entries_by_core_ir_id.keys())


def build_read_surface_payload_vnext_plus19(
    *,
    artifact_id: str,
    include_correlations: bool = False,
    catalog_path: Path | None = None,
) -> dict[str, Any]:
    with _catalog_path_override(catalog_path):
        try:
            core_response = api_main.get_urm_core_ir_artifact_endpoint(
                artifact_id=artifact_id,
                response=Response(),
            ).model_dump(mode="json")
            lane_projection_response = api_main.get_urm_core_ir_lane_projection_endpoint(
                artifact_id=artifact_id,
                response=Response(),
            ).model_dump(mode="json")
            lane_report_response = api_main.get_urm_core_ir_lane_report_endpoint(
                artifact_id=artifact_id,
                response=Response(),
            ).model_dump(mode="json")
        except HTTPException as exc:
            raise _as_read_surface_payload_error(exc, artifact_id=artifact_id) from exc

        integrity, integrity_payload_by_family = _build_integrity_payload(artifact_id=artifact_id)

    core_ir = core_response["core_ir"]
    lane_projection = lane_projection_response["lane_projection"]
    lane_report = lane_report_response["lane_report"]

    payload: dict[str, Any] = {
        "schema": READ_SURFACE_PAYLOAD_VNEXT_PLUS19_SCHEMA,
        "artifact_id": artifact_id,
        "source_text_hash": str(core_ir["source_text_hash"]),
        "core_ir": core_ir,
        "lane_projection": lane_projection,
        "lane_report": lane_report,
        "integrity": integrity,
        "render_summary": _build_render_summary(
            core_ir=core_ir,
            lane_projection=lane_projection,
            lane_report=lane_report,
            integrity_payload_by_family=integrity_payload_by_family,
        ),
    }
    if include_correlations:
        payload["correlations"] = _build_correlations(
            core_ir=core_ir,
            lane_projection=lane_projection,
            lane_report=lane_report,
            integrity_payload_by_family=integrity_payload_by_family,
        )

    normalized = AdeuReadSurfacePayload.model_validate(payload)
    return canonicalize_read_surface_payload(normalized)
