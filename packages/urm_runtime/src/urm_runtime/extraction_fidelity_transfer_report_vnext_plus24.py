from __future__ import annotations

from pathlib import Path
from typing import Any, Mapping, cast

from .hashing import canonical_json
from .stop_gate_tools import (
    _EXTRACTION_FIDELITY_CODES,
    _EXTRACTION_FIDELITY_STATUSES,
    VNEXT_PLUS24_MANIFEST_PATH,
    _compute_vnext_plus19_metrics,
    _compute_vnext_plus20_metrics,
    _compute_vnext_plus21_metrics,
    _compute_vnext_plus22_metrics,
    _compute_vnext_plus23_metrics,
    _compute_vnext_plus24_metrics,
    _discover_repo_root,
    _extraction_fidelity_packet_fixture_hash,
    _extraction_fidelity_projection_fixture_hash,
    _load_vnext_plus24_manifest_payload,
    _read_json_object,
    _resolve_manifest_relative_path,
)

EXTRACTION_FIDELITY_TRANSFER_REPORT_VNEXT_PLUS24_SCHEMA = (
    "extraction_fidelity_transfer_report.vnext_plus24@1"
)
_STOP_GATE_SCHEMA = "stop_gate_metrics@1"


class ExtractionFidelityTransferReportVNextPlus24Error(ValueError):
    """Raised when vNext+24 extraction-fidelity transfer-report inputs are invalid."""


def _default_stop_gate_metrics_path() -> Path:
    module_path = Path(__file__).resolve()
    repo_root = _discover_repo_root(module_path)
    if repo_root is not None:
        return repo_root / "artifacts" / "stop_gate" / "metrics_v24_closeout.json"
    return module_path.parent / "metrics_v24_closeout.json"


def _raise_error(message: str, *, context: Mapping[str, Any] | None = None) -> None:
    payload = {"message": message, "context": dict(context or {})}
    raise ExtractionFidelityTransferReportVNextPlus24Error(canonical_json(payload))


def _runtime_observability_from_closeout(
    *,
    stop_gate_metrics_path: Path,
    expected_totals: Mapping[str, int],
    expected_manifest_hash: str,
    expected_packet_pct: float,
    expected_projection_pct: float,
) -> dict[str, int]:
    closeout_payload = _read_json_object(
        stop_gate_metrics_path,
        description="vnext+24 closeout stop-gate metrics",
    )
    if closeout_payload.get("schema") != _STOP_GATE_SCHEMA:
        _raise_error(
            "vnext+24 closeout stop-gate metrics schema is invalid",
            context={"path": str(stop_gate_metrics_path)},
        )

    manifest_hash = closeout_payload.get("vnext_plus24_manifest_hash")
    if manifest_hash != expected_manifest_hash:
        _raise_error(
            "vnext+24 closeout stop-gate manifest hash does not match manifest",
            context={
                "path": str(stop_gate_metrics_path),
                "expected_manifest_hash": expected_manifest_hash,
                "observed_manifest_hash": manifest_hash,
            },
        )

    metrics = closeout_payload.get("metrics")
    if not isinstance(metrics, Mapping):
        _raise_error(
            "vnext+24 closeout stop-gate metrics payload must include metrics object",
            context={"path": str(stop_gate_metrics_path)},
        )
    packet_pct = metrics.get("artifact_extraction_fidelity_packet_determinism_pct")
    projection_pct = metrics.get("artifact_extraction_fidelity_projection_determinism_pct")
    if packet_pct != expected_packet_pct or projection_pct != expected_projection_pct:
        _raise_error(
            "vnext+24 closeout stop-gate determinism metrics do not match computed values",
            context={
                "path": str(stop_gate_metrics_path),
                "expected_packet_pct": expected_packet_pct,
                "observed_packet_pct": packet_pct,
                "expected_projection_pct": expected_projection_pct,
                "observed_projection_pct": projection_pct,
            },
        )

    runtime_observability = closeout_payload.get("runtime_observability")
    if not isinstance(runtime_observability, Mapping):
        _raise_error(
            "vnext+24 closeout stop-gate metrics must include runtime_observability",
            context={"path": str(stop_gate_metrics_path)},
        )

    observed: dict[str, int] = {}
    for field in (
        "total_fixtures",
        "total_replays",
        "bytes_hashed_per_replay",
        "bytes_hashed_total",
        "elapsed_ms",
    ):
        value = runtime_observability.get(field)
        if not isinstance(value, int) or value < 0:
            _raise_error(
                "vnext+24 runtime_observability fields must be non-negative integers",
                context={"path": str(stop_gate_metrics_path), "field": field},
            )
        observed[field] = value

    for field in (
        "total_fixtures",
        "total_replays",
        "bytes_hashed_per_replay",
        "bytes_hashed_total",
    ):
        if observed[field] != expected_totals[field]:
            _raise_error(
                "vnext+24 runtime_observability totals do not match computed fixture totals",
                context={
                    "path": str(stop_gate_metrics_path),
                    "field": field,
                    "expected": expected_totals[field],
                    "observed": observed[field],
                },
            )

    return observed


def _coverage_summary(*, manifest: Mapping[str, Any]) -> dict[str, Any]:
    coverage_entries = cast(list[dict[str, Any]], manifest["coverage"])
    surfaces = [
        {
            "fixture_count": len(cast(list[str], entry["fixture_ids"])),
            "surface_id": str(entry["surface_id"]),
        }
        for entry in sorted(coverage_entries, key=lambda item: str(item["surface_id"]))
    ]
    surface_count = 2
    covered_surface_count = len(surfaces)
    coverage_pct = round((100.0 * covered_surface_count) / float(surface_count), 6)
    return {
        "coverage_pct": coverage_pct,
        "covered_surface_count": covered_surface_count,
        "surface_count": surface_count,
        "surfaces": surfaces,
        "valid": covered_surface_count == surface_count,
    }


def _packet_summary(*, manifest_path: Path, manifest: Mapping[str, Any]) -> dict[str, Any]:
    fixtures = cast(list[dict[str, Any]], manifest["extraction_fidelity_packet_fixtures"])
    source_hashes: set[str] = set()
    projection_alignment_hashes: set[str] = set()
    fidelity_input_hashes: set[str] = set()
    observed_codes: set[str] = set()
    observed_statuses: set[str] = set()
    has_score_mismatch_drift = False

    fidelity_item_count = 0
    counts_by_code = {code: 0 for code in sorted(_EXTRACTION_FIDELITY_CODES)}
    counts_by_status = {status: 0 for status in sorted(_EXTRACTION_FIDELITY_STATUSES)}
    counts_by_severity = {"high": 0, "low": 0, "medium": 0}

    for fixture in fixtures:
        source_text_hash = str(fixture["source_text_hash"])
        source_hashes.add(source_text_hash)
        runs = cast(list[dict[str, Any]], fixture["runs"])
        if not runs:
            _raise_error(
                "vnext+24 packet fixture must contain runs",
                context={"fixture_id": fixture.get("fixture_id")},
            )
        packet_path = _resolve_manifest_relative_path(
            manifest_path=manifest_path,
            raw_path=runs[0].get("extraction_fidelity_packet_path"),
        )
        _extraction_fidelity_packet_fixture_hash(extraction_fidelity_packet_path=packet_path)
        packet_payload = _read_json_object(
            packet_path,
            description="vnext+24 extraction-fidelity packet fixture",
        )
        if packet_payload.get("source_text_hash") != source_text_hash:
            _raise_error(
                "vnext+24 packet fixture source_text_hash does not match manifest fixture",
                context={
                    "fixture_id": fixture.get("fixture_id"),
                    "packet_path": str(packet_path),
                },
            )

        projection_alignment_hashes.add(str(packet_payload["projection_alignment_hash"]))
        fidelity_input_hashes.add(str(packet_payload["fidelity_input_hash"]))

        summary = cast(dict[str, Any], packet_payload["fidelity_summary"])
        fidelity_item_count += int(summary["total_checks"])
        for code, value in cast(dict[str, int], summary["counts_by_code"]).items():
            counts_by_code[str(code)] = counts_by_code.get(str(code), 0) + int(value)
        for status, value in cast(dict[str, int], summary["counts_by_status"]).items():
            counts_by_status[str(status)] = counts_by_status.get(str(status), 0) + int(value)
        for severity, value in cast(dict[str, int], summary["counts_by_severity"]).items():
            counts_by_severity[str(severity)] = counts_by_severity.get(str(severity), 0) + int(
                value
            )

        for item in cast(list[dict[str, Any]], packet_payload["fidelity_items"]):
            fidelity_code = str(item["fidelity_code"])
            status = str(item["status"])
            observed_codes.add(fidelity_code)
            observed_statuses.add(status)
            if fidelity_code == "score_mismatch" and status == "drift":
                has_score_mismatch_drift = True

    total_checks_gt_zero = fidelity_item_count > 0
    required_fidelity_codes = sorted(_EXTRACTION_FIDELITY_CODES)
    required_status_values = sorted(_EXTRACTION_FIDELITY_STATUSES)
    required_non_empty_floor_passed = (
        total_checks_gt_zero
        and all(code in observed_codes for code in required_fidelity_codes)
        and all(status in observed_statuses for status in required_status_values)
        and has_score_mismatch_drift
    )

    return {
        "source_count": len(source_hashes),
        "extraction_fidelity_packet_fixture_count": len(fixtures),
        "fidelity_item_count": fidelity_item_count,
        "fidelity_counts_by_code": {key: counts_by_code[key] for key in sorted(counts_by_code)},
        "fidelity_counts_by_status": {
            key: counts_by_status[key] for key in sorted(counts_by_status)
        },
        "fidelity_counts_by_severity": {
            key: counts_by_severity[key] for key in sorted(counts_by_severity)
        },
        "projection_alignment_hashes": sorted(projection_alignment_hashes),
        "fidelity_input_hashes": sorted(fidelity_input_hashes),
        "required_non_empty_floor": {
            "passed": required_non_empty_floor_passed,
            "required_fidelity_codes_present": required_fidelity_codes,
            "required_status_values_present": required_status_values,
            "required_score_drift_present": has_score_mismatch_drift,
            "total_checks_gt_zero": total_checks_gt_zero,
        },
        "valid": True,
    }


def _projection_summary(*, manifest_path: Path, manifest: Mapping[str, Any]) -> dict[str, Any]:
    fixtures = cast(list[dict[str, Any]], manifest["extraction_fidelity_projection_fixtures"])
    source_count = 0
    fidelity_item_count = 0
    counts_by_code = {code: 0 for code in sorted(_EXTRACTION_FIDELITY_CODES)}
    counts_by_status = {status: 0 for status in sorted(_EXTRACTION_FIDELITY_STATUSES)}
    counts_by_severity = {"high": 0, "low": 0, "medium": 0}

    for fixture in fixtures:
        runs = cast(list[dict[str, Any]], fixture["runs"])
        if not runs:
            _raise_error(
                "vnext+24 projection fixture must contain runs",
                context={"fixture_id": fixture.get("fixture_id")},
            )
        projection_path = _resolve_manifest_relative_path(
            manifest_path=manifest_path,
            raw_path=runs[0].get("extraction_fidelity_projection_path"),
        )
        _extraction_fidelity_projection_fixture_hash(
            extraction_fidelity_projection_path=projection_path
        )
        projection_payload = _read_json_object(
            projection_path,
            description="vnext+24 extraction-fidelity projection fixture",
        )
        source_count += int(projection_payload["source_count"])
        fidelity_item_count += int(projection_payload["fidelity_item_count"])
        for code, value in cast(
            dict[str, int], projection_payload["fidelity_counts_by_code"]
        ).items():
            counts_by_code[str(code)] = counts_by_code.get(str(code), 0) + int(value)
        for status, value in cast(
            dict[str, int], projection_payload["fidelity_counts_by_status"]
        ).items():
            counts_by_status[str(status)] = counts_by_status.get(str(status), 0) + int(value)
        for severity, value in cast(
            dict[str, int], projection_payload["fidelity_counts_by_severity"]
        ).items():
            counts_by_severity[str(severity)] = counts_by_severity.get(str(severity), 0) + int(
                value
            )

    return {
        "source_count": source_count,
        "extraction_fidelity_projection_fixture_count": len(fixtures),
        "fidelity_item_count": fidelity_item_count,
        "fidelity_counts_by_code": {key: counts_by_code[key] for key in sorted(counts_by_code)},
        "fidelity_counts_by_status": {
            key: counts_by_status[key] for key in sorted(counts_by_status)
        },
        "fidelity_counts_by_severity": {
            key: counts_by_severity[key] for key in sorted(counts_by_severity)
        },
        "valid": True,
    }


def build_extraction_fidelity_transfer_report_vnext_plus24_payload(
    *,
    vnext_plus24_manifest_path: Path = VNEXT_PLUS24_MANIFEST_PATH,
    stop_gate_metrics_path: Path | None = None,
) -> dict[str, Any]:
    manifest, manifest_hash = _load_vnext_plus24_manifest_payload(
        manifest_path=vnext_plus24_manifest_path,
    )

    metrics_issues: list[dict[str, Any]] = []
    vnext_plus19_metrics = _compute_vnext_plus19_metrics(manifest_path=None, issues=metrics_issues)
    vnext_plus20_metrics = _compute_vnext_plus20_metrics(manifest_path=None, issues=metrics_issues)
    vnext_plus21_metrics = _compute_vnext_plus21_metrics(manifest_path=None, issues=metrics_issues)
    vnext_plus22_metrics = _compute_vnext_plus22_metrics(manifest_path=None, issues=metrics_issues)
    vnext_plus23_metrics = _compute_vnext_plus23_metrics(manifest_path=None, issues=metrics_issues)
    vnext_plus24_metrics = _compute_vnext_plus24_metrics(
        manifest_path=vnext_plus24_manifest_path,
        issues=metrics_issues,
    )
    if metrics_issues:
        _raise_error(
            "vnext+24 stop-gate metric evidence is invalid",
            context={"issue": metrics_issues[0]},
        )

    expected_runtime_totals = {
        "total_fixtures": (
            int(vnext_plus19_metrics["vnext_plus19_fixture_count_total"])
            + int(vnext_plus20_metrics["vnext_plus20_fixture_count_total"])
            + int(vnext_plus21_metrics["vnext_plus21_fixture_count_total"])
            + int(vnext_plus22_metrics["vnext_plus22_fixture_count_total"])
            + int(vnext_plus23_metrics["vnext_plus23_fixture_count_total"])
            + int(vnext_plus24_metrics["vnext_plus24_fixture_count_total"])
        ),
        "total_replays": (
            int(vnext_plus19_metrics["vnext_plus19_replay_count_total"])
            + int(vnext_plus20_metrics["vnext_plus20_replay_count_total"])
            + int(vnext_plus21_metrics["vnext_plus21_replay_count_total"])
            + int(vnext_plus22_metrics["vnext_plus22_replay_count_total"])
            + int(vnext_plus23_metrics["vnext_plus23_replay_count_total"])
            + int(vnext_plus24_metrics["vnext_plus24_replay_count_total"])
        ),
        "bytes_hashed_per_replay": (
            int(vnext_plus19_metrics.get("vnext_plus19_bytes_hashed_per_replay", 0))
            + int(vnext_plus20_metrics.get("vnext_plus20_bytes_hashed_per_replay", 0))
            + int(vnext_plus21_metrics.get("vnext_plus21_bytes_hashed_per_replay", 0))
            + int(vnext_plus22_metrics.get("vnext_plus22_bytes_hashed_per_replay", 0))
            + int(vnext_plus23_metrics.get("vnext_plus23_bytes_hashed_per_replay", 0))
            + int(vnext_plus24_metrics.get("vnext_plus24_bytes_hashed_per_replay", 0))
        ),
        "bytes_hashed_total": (
            int(vnext_plus19_metrics.get("vnext_plus19_bytes_hashed_total", 0))
            + int(vnext_plus20_metrics.get("vnext_plus20_bytes_hashed_total", 0))
            + int(vnext_plus21_metrics.get("vnext_plus21_bytes_hashed_total", 0))
            + int(vnext_plus22_metrics.get("vnext_plus22_bytes_hashed_total", 0))
            + int(vnext_plus23_metrics.get("vnext_plus23_bytes_hashed_total", 0))
            + int(vnext_plus24_metrics.get("vnext_plus24_bytes_hashed_total", 0))
        ),
    }

    runtime_observability = _runtime_observability_from_closeout(
        stop_gate_metrics_path=(
            stop_gate_metrics_path
            if stop_gate_metrics_path is not None
            else _default_stop_gate_metrics_path()
        ),
        expected_totals=expected_runtime_totals,
        expected_manifest_hash=manifest_hash,
        expected_packet_pct=float(
            vnext_plus24_metrics["artifact_extraction_fidelity_packet_determinism_pct"]
        ),
        expected_projection_pct=float(
            vnext_plus24_metrics["artifact_extraction_fidelity_projection_determinism_pct"]
        ),
    )

    packet_summary = _packet_summary(
        manifest_path=vnext_plus24_manifest_path,
        manifest=manifest,
    )
    projection_summary = _projection_summary(
        manifest_path=vnext_plus24_manifest_path,
        manifest=manifest,
    )

    packet_fixtures = cast(list[dict[str, Any]], manifest["extraction_fidelity_packet_fixtures"])
    projection_fixtures = cast(
        list[dict[str, Any]], manifest["extraction_fidelity_projection_fixtures"]
    )

    packet_determinism_pct = float(
        vnext_plus24_metrics["artifact_extraction_fidelity_packet_determinism_pct"]
    )
    projection_determinism_pct = float(
        vnext_plus24_metrics["artifact_extraction_fidelity_projection_determinism_pct"]
    )
    replay_summary = {
        "all_passed": packet_determinism_pct == 100.0 and projection_determinism_pct == 100.0,
        "determinism_pct": {
            "artifact_extraction_fidelity_packet_determinism_pct": packet_determinism_pct,
            "artifact_extraction_fidelity_projection_determinism_pct": projection_determinism_pct,
        },
        "fixture_counts": {
            "extraction_fidelity_packet": len(packet_fixtures),
            "extraction_fidelity_projection": len(projection_fixtures),
        },
        "replay_count": int(manifest["replay_count"]),
        "replay_unit_counts": {
            "extraction_fidelity_packet": sum(
                len(cast(list[Any], fixture["runs"])) for fixture in packet_fixtures
            ),
            "extraction_fidelity_projection": sum(
                len(cast(list[Any], fixture["runs"])) for fixture in projection_fixtures
            ),
        },
        "runtime_observability": runtime_observability,
        "valid": True,
    }

    return {
        "schema": EXTRACTION_FIDELITY_TRANSFER_REPORT_VNEXT_PLUS24_SCHEMA,
        "vnext_plus24_manifest_hash": manifest_hash,
        "coverage_summary": _coverage_summary(manifest=manifest),
        "extraction_fidelity_packet_summary": packet_summary,
        "extraction_fidelity_projection_summary": projection_summary,
        "replay_summary": replay_summary,
    }
