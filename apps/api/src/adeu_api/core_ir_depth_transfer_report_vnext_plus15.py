from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from urm_runtime.hashing import canonical_json, sha256_canonical_json

CORE_IR_DEPTH_TRANSFER_REPORT_VNEXT_PLUS15_SCHEMA = (
    "core_ir_depth_transfer_report.vnext_plus15@1"
)
VNEXT_PLUS15_MANIFEST_SCHEMA = "stop_gate.vnext_plus15_manifest@1"
LANE_REPORT_SCHEMA = "adeu_lane_report@0.1"
PROJECTION_ALIGNMENT_SCHEMA = "adeu_projection_alignment@0.1"
_CANONICAL_LANE_ORDER: tuple[str, ...] = ("O", "E", "D", "U")
_FROZEN_DEPTH_SURFACES: tuple[str, ...] = (
    "adeu.core_ir.lane_report",
    "adeu.core_ir.projection_alignment",
    "adeu.core_ir.depth_report",
)
_REQUIRED_METRIC_FIXTURE_KEYS: tuple[str, ...] = (
    "lane_report_replay_fixtures",
    "projection_alignment_fixtures",
    "depth_report_replay_fixtures",
)


class CoreIrDepthTransferReportError(ValueError):
    """Raised when vNext+15 depth transfer-report inputs are invalid."""


def _read_json_object(path: Path, *, description: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise CoreIrDepthTransferReportError(f"{description} is not readable") from exc
    except json.JSONDecodeError as exc:
        raise CoreIrDepthTransferReportError(f"{description} is invalid JSON") from exc
    if not isinstance(payload, dict):
        raise CoreIrDepthTransferReportError(f"{description} must be a JSON object")
    return payload


def _normalize_run_refs(
    *,
    runs: Any,
    field_name: str,
    replay_count: int,
    required_keys: tuple[str, ...],
) -> list[dict[str, str]]:
    if not isinstance(runs, list) or not runs:
        raise CoreIrDepthTransferReportError(f"{field_name} runs must be a non-empty list")
    if len(runs) != replay_count:
        raise CoreIrDepthTransferReportError(
            f"{field_name} runs must have exactly replay_count={replay_count} entries"
        )

    normalized_runs: list[dict[str, str]] = []
    for run_idx, raw_run in enumerate(runs):
        if not isinstance(raw_run, dict) or not raw_run:
            raise CoreIrDepthTransferReportError(
                f"{field_name} runs[{run_idx}] must be a non-empty object"
            )
        normalized_run: dict[str, str] = {}
        for raw_key, raw_value in sorted(raw_run.items()):
            key = str(raw_key).strip()
            value = str(raw_value).strip()
            if not key or not value:
                raise CoreIrDepthTransferReportError(
                    f"{field_name} runs[{run_idx}] entries must be non-empty strings"
                )
            normalized_run[key] = value
        missing_keys = [key for key in required_keys if key not in normalized_run]
        if missing_keys:
            raise CoreIrDepthTransferReportError(
                f"{field_name} runs[{run_idx}] missing required refs: {missing_keys}"
            )
        normalized_runs.append(normalized_run)
    return normalized_runs


def _normalize_fixture_entries(
    *,
    entries: Any,
    field_name: str,
    replay_count: int,
    required_run_keys: tuple[str, ...],
) -> list[dict[str, Any]]:
    if not isinstance(entries, list) or not entries:
        raise CoreIrDepthTransferReportError(f"{field_name} must be a non-empty list")

    normalized_entries: list[dict[str, Any]] = []
    seen_fixture_ids: set[str] = set()
    for idx, raw_entry in enumerate(entries):
        if not isinstance(raw_entry, dict):
            raise CoreIrDepthTransferReportError(f"{field_name}[{idx}] must be an object")

        fixture_id = str(raw_entry.get("fixture_id") or "").strip()
        surface_id = str(raw_entry.get("surface_id") or "").strip()
        if not fixture_id:
            raise CoreIrDepthTransferReportError(f"{field_name}[{idx}] fixture_id is missing")
        if fixture_id in seen_fixture_ids:
            raise CoreIrDepthTransferReportError(
                f"{field_name} fixture_id is duplicated: {fixture_id}"
            )
        if surface_id not in _FROZEN_DEPTH_SURFACES:
            raise CoreIrDepthTransferReportError(
                f"{field_name}[{idx}] surface_id is invalid: {surface_id!r}"
            )

        normalized_entry: dict[str, Any] = {
            "fixture_id": fixture_id,
            "surface_id": surface_id,
            "runs": _normalize_run_refs(
                runs=raw_entry.get("runs"),
                field_name=f"{field_name}[{idx}]",
                replay_count=replay_count,
                required_keys=required_run_keys,
            ),
        }
        notes = raw_entry.get("notes")
        if notes is not None:
            note_value = str(notes).strip()
            if not note_value:
                raise CoreIrDepthTransferReportError(
                    f"{field_name}[{idx}] notes must be non-empty when present"
                )
            normalized_entry["notes"] = note_value
        normalized_entries.append(normalized_entry)
        seen_fixture_ids.add(fixture_id)
    return sorted(normalized_entries, key=lambda item: str(item["fixture_id"]))


def _load_vnext_plus15_manifest_payload(path: Path) -> tuple[dict[str, Any], str]:
    payload = _read_json_object(path, description="vnext+15 manifest")
    if payload.get("schema") != VNEXT_PLUS15_MANIFEST_SCHEMA:
        raise CoreIrDepthTransferReportError("vnext+15 manifest schema is invalid")

    replay_count = payload.get("replay_count")
    if not isinstance(replay_count, int) or replay_count <= 0:
        raise CoreIrDepthTransferReportError("vnext+15 manifest replay_count is invalid")

    normalized_manifest: dict[str, Any] = {
        "schema": VNEXT_PLUS15_MANIFEST_SCHEMA,
        "replay_count": replay_count,
    }
    normalized_manifest["lane_report_replay_fixtures"] = _normalize_fixture_entries(
        entries=payload.get("lane_report_replay_fixtures"),
        field_name="lane_report_replay_fixtures",
        replay_count=replay_count,
        required_run_keys=("lane_report_path",),
    )
    normalized_manifest["projection_alignment_fixtures"] = _normalize_fixture_entries(
        entries=payload.get("projection_alignment_fixtures"),
        field_name="projection_alignment_fixtures",
        replay_count=replay_count,
        required_run_keys=("projection_alignment_path",),
    )
    normalized_manifest["depth_report_replay_fixtures"] = _normalize_fixture_entries(
        entries=payload.get("depth_report_replay_fixtures"),
        field_name="depth_report_replay_fixtures",
        replay_count=replay_count,
        required_run_keys=("lane_report_path", "projection_alignment_path"),
    )

    fixture_id_catalog: set[str] = set()
    fixture_surface_catalog: dict[str, str] = {}
    for list_key in _REQUIRED_METRIC_FIXTURE_KEYS:
        for entry in normalized_manifest[list_key]:
            fixture_id = str(entry["fixture_id"])
            if fixture_id in fixture_id_catalog:
                raise CoreIrDepthTransferReportError(
                    f"vnext+15 manifest fixture_id is duplicated across lists: {fixture_id}"
                )
            fixture_id_catalog.add(fixture_id)
            fixture_surface_catalog[fixture_id] = str(entry["surface_id"])

    coverage_entries = payload.get("coverage")
    if not isinstance(coverage_entries, list) or not coverage_entries:
        raise CoreIrDepthTransferReportError("vnext+15 manifest coverage is invalid")

    normalized_coverage_entries: list[dict[str, Any]] = []
    seen_surface_ids: set[str] = set()
    for idx, raw_entry in enumerate(coverage_entries):
        if not isinstance(raw_entry, dict):
            raise CoreIrDepthTransferReportError(f"coverage[{idx}] must be an object")
        surface_id = str(raw_entry.get("surface_id") or "").strip()
        if surface_id not in _FROZEN_DEPTH_SURFACES:
            raise CoreIrDepthTransferReportError(
                f"coverage[{idx}] surface_id is invalid: {surface_id!r}"
            )
        if surface_id in seen_surface_ids:
            raise CoreIrDepthTransferReportError(
                f"coverage surface_id is duplicated: {surface_id}"
            )
        fixture_ids = raw_entry.get("fixture_ids")
        if not isinstance(fixture_ids, list) or not fixture_ids:
            raise CoreIrDepthTransferReportError(
                f"coverage[{idx}] fixture_ids must be a non-empty list"
            )
        normalized_fixture_ids = sorted(str(value).strip() for value in fixture_ids)
        if any(not fixture_id for fixture_id in normalized_fixture_ids):
            raise CoreIrDepthTransferReportError(
                f"coverage[{idx}] fixture_ids contains an empty value"
            )
        if len(set(normalized_fixture_ids)) != len(normalized_fixture_ids):
            raise CoreIrDepthTransferReportError(
                f"coverage[{idx}] fixture_ids contains duplicates"
            )
        unknown_fixture_ids = sorted(
            fixture_id
            for fixture_id in normalized_fixture_ids
            if fixture_id not in fixture_id_catalog
        )
        if unknown_fixture_ids:
            raise CoreIrDepthTransferReportError(
                f"coverage[{idx}] references unknown fixture_ids: {unknown_fixture_ids}"
            )
        cross_surface_fixture_ids = sorted(
            fixture_id
            for fixture_id in normalized_fixture_ids
            if fixture_surface_catalog.get(fixture_id) != surface_id
        )
        if cross_surface_fixture_ids:
            raise CoreIrDepthTransferReportError(
                f"coverage[{idx}] references fixture_ids mapped to other surfaces: "
                f"{cross_surface_fixture_ids}"
            )
        normalized_entry: dict[str, Any] = {
            "surface_id": surface_id,
            "fixture_ids": normalized_fixture_ids,
        }
        notes = raw_entry.get("notes")
        if notes is not None:
            note_value = str(notes).strip()
            if not note_value:
                raise CoreIrDepthTransferReportError(
                    f"coverage[{idx}] notes must be non-empty when present"
                )
            normalized_entry["notes"] = note_value
        normalized_coverage_entries.append(normalized_entry)
        seen_surface_ids.add(surface_id)

    expected_surfaces = set(_FROZEN_DEPTH_SURFACES)
    if seen_surface_ids != expected_surfaces:
        missing = sorted(expected_surfaces - seen_surface_ids)
        extra = sorted(seen_surface_ids - expected_surfaces)
        raise CoreIrDepthTransferReportError(
            f"coverage surface set mismatch: missing={missing}, extra={extra}"
        )
    normalized_manifest["coverage"] = sorted(
        normalized_coverage_entries, key=lambda item: str(item["surface_id"])
    )

    raw_manifest_hash = payload.get("manifest_hash")
    if not isinstance(raw_manifest_hash, str) or not raw_manifest_hash:
        raise CoreIrDepthTransferReportError("vnext+15 manifest missing manifest_hash")
    recomputed_manifest_hash = sha256_canonical_json(normalized_manifest)
    if raw_manifest_hash != recomputed_manifest_hash:
        raise CoreIrDepthTransferReportError("vnext+15 manifest_hash mismatch")

    normalized_manifest["manifest_hash"] = recomputed_manifest_hash
    return normalized_manifest, recomputed_manifest_hash


def _resolve_ref(*, manifest_path: Path, raw_ref: str) -> Path:
    candidate = Path(raw_ref)
    if candidate.is_absolute():
        return candidate.resolve()
    return (manifest_path.parent / candidate).resolve()


def _validate_lane_report_artifact(path: Path) -> dict[str, Any]:
    payload = _read_json_object(path, description=f"lane report artifact {path}")
    if payload.get("schema") != LANE_REPORT_SCHEMA:
        raise CoreIrDepthTransferReportError(
            f"lane report artifact has invalid schema: {path}"
        )
    source_text_hash = str(payload.get("source_text_hash") or "").strip()
    if not source_text_hash:
        raise CoreIrDepthTransferReportError(
            f"lane report artifact missing source_text_hash: {path}"
        )
    lane_nodes = payload.get("lane_nodes")
    if not isinstance(lane_nodes, dict):
        raise CoreIrDepthTransferReportError(
            f"lane report artifact lane_nodes is invalid: {path}"
        )
    total_nodes = 0
    for lane in _CANONICAL_LANE_ORDER:
        node_ids = lane_nodes.get(lane)
        if not isinstance(node_ids, list):
            raise CoreIrDepthTransferReportError(
                f"lane report artifact lane_nodes[{lane}] is invalid: {path}"
            )
        for node_id in node_ids:
            if not isinstance(node_id, str) or not node_id.strip():
                raise CoreIrDepthTransferReportError(
                    f"lane report artifact lane_nodes[{lane}] has empty node id: {path}"
                )
        total_nodes += len(node_ids)
    if total_nodes <= 0:
        raise CoreIrDepthTransferReportError(
            f"lane report artifact has empty lane-node evidence: {path}"
        )
    return {
        "source_text_hash": source_text_hash,
        "lane_node_count": total_nodes,
    }


def _validate_projection_alignment_artifact(path: Path) -> dict[str, Any]:
    payload = _read_json_object(path, description=f"projection alignment artifact {path}")
    if payload.get("schema") != PROJECTION_ALIGNMENT_SCHEMA:
        raise CoreIrDepthTransferReportError(
            f"projection alignment artifact has invalid schema: {path}"
        )
    source_text_hash = str(payload.get("source_text_hash") or "").strip()
    if not source_text_hash:
        raise CoreIrDepthTransferReportError(
            f"projection alignment artifact missing source_text_hash: {path}"
        )
    summary = payload.get("summary")
    issues = payload.get("issues")
    if not isinstance(summary, dict):
        raise CoreIrDepthTransferReportError(
            f"projection alignment artifact summary is invalid: {path}"
        )
    if not isinstance(issues, list):
        raise CoreIrDepthTransferReportError(
            f"projection alignment artifact issues is invalid: {path}"
        )
    total_issues = summary.get("total_issues")
    if not isinstance(total_issues, int) or total_issues < 0:
        raise CoreIrDepthTransferReportError(
            f"projection alignment artifact summary.total_issues is invalid: {path}"
        )
    if total_issues != len(issues):
        raise CoreIrDepthTransferReportError(
            f"projection alignment artifact total_issues mismatch: {path}"
        )
    kind_counts: dict[str, int] = {
        "missing_in_projection": 0,
        "missing_in_extraction": 0,
        "kind_mismatch": 0,
        "edge_type_mismatch": 0,
    }
    for issue in issues:
        if not isinstance(issue, dict):
            raise CoreIrDepthTransferReportError(
                f"projection alignment artifact issue is invalid: {path}"
            )
        kind = str(issue.get("kind") or "").strip()
        if kind not in kind_counts:
            raise CoreIrDepthTransferReportError(
                f"projection alignment artifact issue kind is invalid: {path}"
            )
        kind_counts[kind] += 1
    for kind, count in kind_counts.items():
        raw_summary_count = summary.get(kind)
        if not isinstance(raw_summary_count, int) or raw_summary_count != count:
            raise CoreIrDepthTransferReportError(
                f"projection alignment artifact summary.{kind} mismatch: {path}"
            )
    return {
        "source_text_hash": source_text_hash,
        "total_issues": total_issues,
        "kind_counts": kind_counts,
    }


def _build_coverage_summary(*, manifest_coverage_entries: list[dict[str, Any]]) -> dict[str, Any]:
    entries = [
        {
            "surface_id": str(entry["surface_id"]),
            "fixture_ids": list(entry["fixture_ids"]),
            "valid": True,
            **({"notes": entry["notes"]} if "notes" in entry else {}),
        }
        for entry in manifest_coverage_entries
    ]
    surface_count = len(_FROZEN_DEPTH_SURFACES)
    covered_surface_count = len(entries)
    coverage_pct = (
        round((100.0 * covered_surface_count) / float(surface_count), 6)
        if surface_count > 0
        else 0.0
    )
    return {
        "valid": covered_surface_count == surface_count,
        "surface_count": surface_count,
        "covered_surface_count": covered_surface_count,
        "coverage_pct": coverage_pct,
        "entries": entries,
    }


def _build_alignment_summary(
    *,
    manifest_path: Path,
    projection_alignment_fixtures: list[dict[str, Any]],
) -> dict[str, Any]:
    total_issues = 0
    issue_kind_counts = {
        "missing_in_projection": 0,
        "missing_in_extraction": 0,
        "kind_mismatch": 0,
        "edge_type_mismatch": 0,
    }
    run_count = 0
    for fixture in projection_alignment_fixtures:
        for run in fixture["runs"]:
            run_count += 1
            artifact_path = _resolve_ref(
                manifest_path=manifest_path,
                raw_ref=str(run["projection_alignment_path"]),
            )
            details = _validate_projection_alignment_artifact(artifact_path)
            total_issues += int(details["total_issues"])
            for key in issue_kind_counts:
                issue_kind_counts[key] += int(details["kind_counts"][key])
    return {
        "valid": True,
        "fixture_count": len(projection_alignment_fixtures),
        "run_count": run_count,
        "total_issues": total_issues,
        "issue_kind_counts": issue_kind_counts,
    }


def _build_replay_summary(
    *,
    manifest_path: Path,
    replay_count: int,
    lane_report_fixtures: list[dict[str, Any]],
    projection_alignment_fixtures: list[dict[str, Any]],
    depth_report_fixtures: list[dict[str, Any]],
) -> dict[str, Any]:
    lane_replay_units = 0
    alignment_replay_units = 0
    depth_replay_units = 0

    for fixture in lane_report_fixtures:
        for run in fixture["runs"]:
            lane_replay_units += 1
            artifact_path = _resolve_ref(
                manifest_path=manifest_path,
                raw_ref=str(run["lane_report_path"]),
            )
            _validate_lane_report_artifact(artifact_path)

    for fixture in projection_alignment_fixtures:
        for run in fixture["runs"]:
            alignment_replay_units += 1
            artifact_path = _resolve_ref(
                manifest_path=manifest_path,
                raw_ref=str(run["projection_alignment_path"]),
            )
            _validate_projection_alignment_artifact(artifact_path)

    for fixture in depth_report_fixtures:
        for run in fixture["runs"]:
            depth_replay_units += 1
            lane_report_path = _resolve_ref(
                manifest_path=manifest_path,
                raw_ref=str(run["lane_report_path"]),
            )
            projection_alignment_path = _resolve_ref(
                manifest_path=manifest_path,
                raw_ref=str(run["projection_alignment_path"]),
            )
            lane_details = _validate_lane_report_artifact(lane_report_path)
            alignment_details = _validate_projection_alignment_artifact(
                projection_alignment_path
            )
            if lane_details["source_text_hash"] != alignment_details["source_text_hash"]:
                raise CoreIrDepthTransferReportError(
                    "depth-report run source_text_hash mismatch between lane and alignment refs"
                )

    return {
        "valid": True,
        "replay_count": replay_count,
        "fixture_counts": {
            "lane_report_replay": len(lane_report_fixtures),
            "projection_alignment": len(projection_alignment_fixtures),
            "depth_report_replay": len(depth_report_fixtures),
        },
        "replay_unit_counts": {
            "lane_report_replay": lane_replay_units,
            "projection_alignment": alignment_replay_units,
            "depth_report_replay": depth_replay_units,
        },
    }


def build_core_ir_depth_transfer_report_vnext_plus15_payload(
    *,
    vnext_plus15_manifest_path: Path,
) -> dict[str, Any]:
    manifest_payload, manifest_hash = _load_vnext_plus15_manifest_payload(
        vnext_plus15_manifest_path
    )
    lane_report_fixtures = manifest_payload["lane_report_replay_fixtures"]
    projection_alignment_fixtures = manifest_payload["projection_alignment_fixtures"]
    depth_report_fixtures = manifest_payload["depth_report_replay_fixtures"]
    replay_count = int(manifest_payload["replay_count"])
    return {
        "schema": CORE_IR_DEPTH_TRANSFER_REPORT_VNEXT_PLUS15_SCHEMA,
        "vnext_plus15_manifest_hash": manifest_hash,
        "coverage_summary": _build_coverage_summary(
            manifest_coverage_entries=manifest_payload["coverage"],
        ),
        "alignment_summary": _build_alignment_summary(
            manifest_path=vnext_plus15_manifest_path,
            projection_alignment_fixtures=projection_alignment_fixtures,
        ),
        "replay_summary": _build_replay_summary(
            manifest_path=vnext_plus15_manifest_path,
            replay_count=replay_count,
            lane_report_fixtures=lane_report_fixtures,
            projection_alignment_fixtures=projection_alignment_fixtures,
            depth_report_fixtures=depth_report_fixtures,
        ),
    }


def core_ir_depth_transfer_report_vnext_plus15_markdown(payload: dict[str, Any]) -> str:
    lines: list[str] = [
        "# Core-IR Depth Transfer Report vNext+15",
        "",
        "Deterministic C3 transfer summary generated from persisted vNext+15 "
        "depth-coverage fixtures and artifacts.",
        "",
        "```json",
        canonical_json(payload),
        "```",
        "",
    ]
    return "\n".join(lines)
