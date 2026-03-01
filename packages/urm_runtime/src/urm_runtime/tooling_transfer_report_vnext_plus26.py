from __future__ import annotations

import json
import re
from collections.abc import Mapping
from pathlib import Path
from typing import Any, cast

from .hashing import canonical_json, sha256_canonical_json
from .stop_gate_registry import discover_repo_root

TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_SCHEMA = "tooling_transfer_report.vnext_plus26@1"
_STOP_GATE_METRICS_SCHEMA = "stop_gate_metrics@1"
_STOP_GATE_MANIFEST_SCHEMA = "stop_gate.vnext_plus26_manifest@1"

S9_REQUIRED_THRESHOLD = 100.0
S9_REQUIRED_METRIC_KEYS: tuple[str, ...] = (
    "provider_route_contract_parity_pct",
    "codex_candidate_contract_valid_pct",
    "provider_parity_replay_determinism_pct",
)

_RUNTIME_OBSERVABILITY_FIELDS: tuple[str, ...] = (
    "elapsed_ms",
    "total_fixtures",
    "total_replays",
    "bytes_hashed_per_replay",
    "bytes_hashed_total",
)

_JSON_FENCE_RE = re.compile(r"```json\s*\n(.*?)\n```", re.DOTALL)


class ToolingTransferReportVNextPlus26Error(ValueError):
    """Raised when vNext+26 tooling transfer-report inputs are invalid."""


def _raise_error(message: str, *, context: Mapping[str, Any] | None = None) -> None:
    payload = {"message": message, "context": dict(context or {})}
    raise ToolingTransferReportVNextPlus26Error(canonical_json(payload))


def _load_json_object(path: Path, *, description: str) -> Mapping[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        _raise_error(
            f"{description} path does not exist",
            context={"path": str(path)},
        )
    except json.JSONDecodeError as exc:
        _raise_error(
            f"{description} is not valid JSON",
            context={"path": str(path), "error": str(exc)},
        )

    if not isinstance(payload, Mapping):
        _raise_error(
            f"{description} must decode to a JSON object",
            context={"path": str(path)},
        )
    return payload


def _require_schema(payload: Mapping[str, Any], *, expected_schema: str, description: str) -> None:
    if payload.get("schema") != expected_schema:
        _raise_error(
            f"{description} schema is invalid",
            context={
                "expected_schema": expected_schema,
                "observed_schema": payload.get("schema"),
            },
        )


def _require_metrics_object(payload: Mapping[str, Any], *, description: str) -> Mapping[str, Any]:
    metrics = payload.get("metrics")
    if not isinstance(metrics, Mapping):
        _raise_error(
            f"{description} must include metrics object",
            context={"observed_type": type(metrics).__name__},
        )
    return metrics


def _require_numeric_metric(
    *,
    metrics: Mapping[str, Any],
    metric_key: str,
    description: str,
) -> float:
    if metric_key not in metrics:
        _raise_error(
            f"{description} required metric is missing",
            context={"metric_key": metric_key},
        )
    value = metrics[metric_key]
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        _raise_error(
            f"{description} required metric must be numeric",
            context={"metric_key": metric_key, "observed_type": type(value).__name__},
        )
    return float(value)


def _require_replay_count(manifest: Mapping[str, Any]) -> int:
    replay_count = manifest.get("replay_count")
    if not isinstance(replay_count, int) or replay_count <= 0:
        _raise_error(
            "vnext+26 manifest replay_count must be a positive integer",
            context={"observed_replay_count": replay_count},
        )
    return replay_count


def _require_runtime_observability(closeout_payload: Mapping[str, Any]) -> dict[str, int]:
    runtime_observability = closeout_payload.get("runtime_observability")
    if not isinstance(runtime_observability, Mapping):
        _raise_error("stop-gate metrics must include runtime_observability object")

    result: dict[str, int] = {}
    for field in _RUNTIME_OBSERVABILITY_FIELDS:
        value = runtime_observability.get(field)
        if not isinstance(value, int) or value < 0:
            _raise_error(
                "runtime_observability fields must be non-negative integers",
                context={"field": field, "observed": value},
            )
        result[field] = value
    return result


def _require_coverage_surfaces(manifest: Mapping[str, Any]) -> list[dict[str, Any]]:
    coverage = manifest.get("coverage")
    if not isinstance(coverage, list):
        _raise_error(
            "vnext+26 manifest coverage must be a list",
            context={"observed_type": type(coverage).__name__},
        )

    surfaces: list[dict[str, Any]] = []
    for entry in coverage:
        if not isinstance(entry, Mapping):
            _raise_error("vnext+26 coverage entries must be objects")
        surface_id = entry.get("surface_id")
        if not isinstance(surface_id, str) or not surface_id.strip():
            _raise_error(
                "vnext+26 coverage entry surface_id must be a non-empty string",
                context={"observed_surface_id": surface_id},
            )
        fixture_ids = entry.get("fixture_ids")
        if not isinstance(fixture_ids, list) or any(
            not isinstance(value, str) for value in fixture_ids
        ):
            _raise_error(
                "vnext+26 coverage entry fixture_ids must be list[str]",
                context={"surface_id": surface_id},
            )
        surfaces.append(
            {
                "surface_id": surface_id,
                "fixture_count": len(fixture_ids),
                "fixture_ids": list(fixture_ids),
            }
        )
    return surfaces


def _fixture_and_run_counts(manifest: Mapping[str, Any], *, fixture_key: str) -> tuple[int, int]:
    fixtures = manifest.get(fixture_key)
    if not isinstance(fixtures, list):
        _raise_error(
            "vnext+26 manifest fixture collection must be a list",
            context={"fixture_key": fixture_key, "observed_type": type(fixtures).__name__},
        )

    run_count = 0
    for fixture in fixtures:
        if not isinstance(fixture, Mapping):
            _raise_error(
                "vnext+26 fixture entries must be objects",
                context={"fixture_key": fixture_key},
            )
        runs = fixture.get("runs")
        if not isinstance(runs, list):
            _raise_error(
                "vnext+26 fixture runs must be a list",
                context={
                    "fixture_key": fixture_key,
                    "fixture_id": fixture.get("fixture_id"),
                    "observed_type": type(runs).__name__,
                },
            )
        run_count += len(runs)
    return len(fixtures), run_count


def _display_path(path: Path, *, repo_root: Path) -> str:
    resolved = path.resolve()
    try:
        return resolved.relative_to(repo_root.resolve()).as_posix()
    except ValueError:
        return resolved.as_posix()


def _coverage_summary(manifest: Mapping[str, Any]) -> dict[str, Any]:
    surfaces = _require_coverage_surfaces(manifest)
    covered_surface_count = sum(1 for entry in surfaces if int(entry["fixture_count"]) > 0)
    surface_count = len(surfaces)
    coverage_pct = 0.0
    if surface_count > 0:
        coverage_pct = round((100.0 * float(covered_surface_count)) / float(surface_count), 6)

    return {
        "coverage_pct": coverage_pct,
        "covered_surface_count": covered_surface_count,
        "surface_count": surface_count,
        "parity_projection": str(manifest.get("parity_projection")),
        "surfaces": surfaces,
        "valid": covered_surface_count == surface_count,
    }


def _stop_gate_input_model_parity_summary(
    *,
    manifest: Mapping[str, Any],
    closeout_metrics: Mapping[str, Any],
) -> dict[str, Any]:
    metric_key = "artifact_stop_gate_input_model_parity_pct"
    metric_value = _require_numeric_metric(
        metrics=closeout_metrics,
        metric_key=metric_key,
        description="vnext+26 closeout metrics",
    )
    fixture_count, run_count = _fixture_and_run_counts(
        manifest,
        fixture_key="stop_gate_input_model_parity_fixtures",
    )
    replay_count = _require_replay_count(manifest)
    return {
        metric_key: metric_value,
        "fixture_count": fixture_count,
        "run_count": run_count,
        "replay_count": replay_count,
        "parity_projection": str(manifest.get("parity_projection")),
        "valid": metric_value >= 100.0,
    }


def _transfer_report_builder_parity_summary(
    *,
    manifest: Mapping[str, Any],
    closeout_metrics: Mapping[str, Any],
) -> dict[str, Any]:
    metric_key = "artifact_transfer_report_builder_parity_pct"
    metric_value = _require_numeric_metric(
        metrics=closeout_metrics,
        metric_key=metric_key,
        description="vnext+26 closeout metrics",
    )
    fixture_count, run_count = _fixture_and_run_counts(
        manifest,
        fixture_key="transfer_report_builder_parity_fixtures",
    )
    replay_count = _require_replay_count(manifest)
    return {
        metric_key: metric_value,
        "fixture_count": fixture_count,
        "run_count": run_count,
        "replay_count": replay_count,
        "parity_projection": str(manifest.get("parity_projection")),
        "valid": metric_value >= 100.0,
    }


def _s9_trigger_check_summary(
    *,
    s9_metrics: Mapping[str, Any],
    source_stop_gate_metrics_path: str,
    threshold: float,
) -> dict[str, Any]:
    required_metrics: dict[str, Any] = {}
    all_passed = True
    for metric_key in S9_REQUIRED_METRIC_KEYS:
        observed_pct = _require_numeric_metric(
            metrics=s9_metrics,
            metric_key=metric_key,
            description="vnext+25 closeout metrics for S9 summary",
        )
        passes = observed_pct >= threshold
        all_passed = all_passed and passes
        required_metrics[metric_key] = {
            "observed_pct": observed_pct,
            "required_pct": threshold,
            "passes": passes,
        }
    return {
        "source_stop_gate_metrics_path": source_stop_gate_metrics_path,
        "required_metrics": required_metrics,
        "all_passed": all_passed,
        "valid": all_passed,
    }


def _replay_summary(
    *,
    stop_gate_input_model_parity_summary: Mapping[str, Any],
    transfer_report_builder_parity_summary: Mapping[str, Any],
    runtime_observability: Mapping[str, int],
) -> dict[str, Any]:
    stop_gate_pct = float(
        stop_gate_input_model_parity_summary[
            "artifact_stop_gate_input_model_parity_pct"
        ]
    )
    transfer_builder_pct = float(
        transfer_report_builder_parity_summary["artifact_transfer_report_builder_parity_pct"]
    )
    all_passed = stop_gate_pct >= 100.0 and transfer_builder_pct >= 100.0
    return {
        "all_passed": all_passed,
        "determinism_pct": {
            "artifact_stop_gate_input_model_parity_pct": stop_gate_pct,
            "artifact_transfer_report_builder_parity_pct": transfer_builder_pct,
        },
        "fixture_counts": {
            "stop_gate_input_model_parity": int(
                stop_gate_input_model_parity_summary["fixture_count"]
            ),
            "transfer_report_builder_parity": int(
                transfer_report_builder_parity_summary["fixture_count"]
            ),
        },
        "run_counts": {
            "stop_gate_input_model_parity": int(stop_gate_input_model_parity_summary["run_count"]),
            "transfer_report_builder_parity": int(
                transfer_report_builder_parity_summary["run_count"]
            ),
        },
        "replay_count": int(stop_gate_input_model_parity_summary["replay_count"]),
        "runtime_observability": {
            key: int(runtime_observability[key]) for key in _RUNTIME_OBSERVABILITY_FIELDS
        },
        "valid": all_passed,
    }


def build_tooling_transfer_report_vnext_plus26_payload(
    *,
    vnext_plus26_manifest_path: Path,
    stop_gate_metrics_path: Path,
    s9_metrics_path: Path,
    s9_required_threshold: float = S9_REQUIRED_THRESHOLD,
) -> dict[str, Any]:
    manifest = _load_json_object(
        vnext_plus26_manifest_path,
        description="vnext+26 stop-gate manifest",
    )
    _require_schema(
        manifest,
        expected_schema=_STOP_GATE_MANIFEST_SCHEMA,
        description="vnext+26 stop-gate manifest",
    )

    manifest_hash = manifest.get("manifest_hash")
    if not isinstance(manifest_hash, str) or not manifest_hash:
        _raise_error("vnext+26 stop-gate manifest_hash must be a non-empty string")

    closeout_payload = _load_json_object(
        stop_gate_metrics_path,
        description="vnext+26 closeout stop-gate metrics",
    )
    _require_schema(
        closeout_payload,
        expected_schema=_STOP_GATE_METRICS_SCHEMA,
        description="vnext+26 closeout stop-gate metrics",
    )
    closeout_metrics = _require_metrics_object(
        closeout_payload,
        description="vnext+26 closeout stop-gate metrics",
    )

    observed_manifest_hash = closeout_payload.get("vnext_plus26_manifest_hash")
    if observed_manifest_hash != manifest_hash:
        _raise_error(
            "vnext+26 closeout metrics manifest hash does not match vnext+26 manifest",
            context={
                "expected_manifest_hash": manifest_hash,
                "observed_manifest_hash": observed_manifest_hash,
            },
        )

    s9_source_payload = _load_json_object(
        s9_metrics_path,
        description="vnext+25 closeout stop-gate metrics for S9 summary",
    )
    _require_schema(
        s9_source_payload,
        expected_schema=_STOP_GATE_METRICS_SCHEMA,
        description="vnext+25 closeout stop-gate metrics for S9 summary",
    )
    s9_source_metrics = _require_metrics_object(
        s9_source_payload,
        description="vnext+25 closeout stop-gate metrics for S9 summary",
    )

    repo_root = discover_repo_root(Path(__file__).resolve())
    if repo_root is None:
        _raise_error("repository root not found for path normalization")

    coverage_summary = _coverage_summary(manifest)
    stop_gate_input_model_parity_summary = _stop_gate_input_model_parity_summary(
        manifest=manifest,
        closeout_metrics=closeout_metrics,
    )
    transfer_report_builder_parity_summary = _transfer_report_builder_parity_summary(
        manifest=manifest,
        closeout_metrics=closeout_metrics,
    )
    s9_trigger_check_summary = _s9_trigger_check_summary(
        s9_metrics=s9_source_metrics,
        source_stop_gate_metrics_path=_display_path(s9_metrics_path, repo_root=repo_root),
        threshold=s9_required_threshold,
    )
    replay_summary = _replay_summary(
        stop_gate_input_model_parity_summary=stop_gate_input_model_parity_summary,
        transfer_report_builder_parity_summary=transfer_report_builder_parity_summary,
        runtime_observability=_require_runtime_observability(closeout_payload),
    )

    return {
        "schema": TOOLING_TRANSFER_REPORT_VNEXT_PLUS26_SCHEMA,
        "vnext_plus26_manifest_hash": manifest_hash,
        "coverage_summary": coverage_summary,
        "stop_gate_input_model_parity_summary": stop_gate_input_model_parity_summary,
        "transfer_report_builder_parity_summary": transfer_report_builder_parity_summary,
        "s9_trigger_check_summary": s9_trigger_check_summary,
        "replay_summary": replay_summary,
    }


def extract_unique_schema_payload_from_markdown(
    *,
    markdown_text: str,
    schema: str,
) -> dict[str, Any]:
    matches = list(_JSON_FENCE_RE.finditer(markdown_text))
    if not matches:
        _raise_error(
            "baseline markdown must include at least one fenced JSON block",
            context={"schema": schema},
        )

    schema_payloads: list[dict[str, Any]] = []
    for block_index, match in enumerate(matches):
        raw_json_block = match.group(1)
        try:
            parsed = json.loads(raw_json_block)
        except json.JSONDecodeError as exc:
            _raise_error(
                "baseline markdown contains invalid fenced JSON block",
                context={"block_index": block_index, "error": str(exc)},
            )
        if not isinstance(parsed, Mapping):
            _raise_error(
                "baseline fenced JSON block must decode to an object",
                context={"block_index": block_index},
            )
        if parsed.get("schema") == schema:
            schema_payloads.append(dict(parsed))

    if not schema_payloads:
        _raise_error(
            "baseline markdown does not contain required schema block",
            context={"schema": schema},
        )
    if len(schema_payloads) != 1:
        _raise_error(
            "baseline markdown contains duplicate required schema blocks",
            context={"schema": schema, "count": len(schema_payloads)},
        )
    return schema_payloads[0]


def canonical_payload_hash(payload: Mapping[str, Any]) -> str:
    return sha256_canonical_json(payload)


def render_tooling_transfer_report_vnext_plus26_markdown(payload: Mapping[str, Any]) -> str:
    payload_object = cast(dict[str, Any], dict(payload))
    body = json.dumps(payload_object, indent=2, ensure_ascii=False)
    return (
        "# Tooling Transfer Report vNext+26\n\n"
        "Deterministic transfer summary generated from fixture-backed vNext+26 tooling "
        "parity artifacts.\n\n"
        "```json\n"
        f"{body}\n"
        "```\n"
    )
