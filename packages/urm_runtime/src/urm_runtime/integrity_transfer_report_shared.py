from __future__ import annotations

from collections.abc import Callable, Mapping
from pathlib import Path
from typing import Any, TypeVar

from .hashing import canonical_json
from .stop_gate_tools import _resolve_manifest_relative_path

E = TypeVar("E", bound=Exception)


def _resolve_transfer_report_ref(*, manifest_path: Path, raw_ref: str) -> Path:
    return _resolve_manifest_relative_path(
        manifest_path=manifest_path,
        raw_path=raw_ref,
    )


def _as_transfer_report_error(
    exc: ValueError,
    *,
    error_type: type[E],
    default_message: str,
    default_code: str = "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
) -> E:
    issue = exc.args[0] if exc.args else None
    if isinstance(issue, dict):
        code = str(issue.get("code") or default_code)
        message = str(issue.get("message") or default_message)
        context = issue.get("context", {})
        return error_type(f"{code}: {message} ({canonical_json(context)})")
    return error_type(str(exc))


def _make_transfer_report_error_adapter(
    *,
    error_type: type[E],
    default_message: str,
    default_code: str = "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
) -> Callable[[ValueError], E]:
    def _adapter(exc: ValueError) -> E:
        return _as_transfer_report_error(
            exc,
            error_type=error_type,
            default_message=default_message,
            default_code=default_code,
        )

    return _adapter


def _build_transfer_report_coverage_summary(
    *,
    manifest_coverage_entries: list[dict[str, Any]],
    frozen_surface_ids: tuple[str, ...],
) -> dict[str, Any]:
    entries = [
        {
            "surface_id": str(entry["surface_id"]),
            "fixture_ids": list(entry["fixture_ids"]),
            "valid": True,
            **({"notes": entry["notes"]} if "notes" in entry else {}),
        }
        for entry in sorted(
            manifest_coverage_entries,
            key=lambda item: str(item["surface_id"]),
        )
    ]
    surface_count = len(frozen_surface_ids)
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


def _build_transfer_report_replay_summary(
    *,
    replay_count: int,
    fixture_families: Mapping[str, list[dict[str, Any]]],
) -> dict[str, Any]:
    fixture_counts: dict[str, int] = {}
    replay_unit_counts: dict[str, int] = {}
    for family_name, fixtures in fixture_families.items():
        fixture_counts[family_name] = len(fixtures)
        replay_unit_counts[family_name] = sum(len(fixture["runs"]) for fixture in fixtures)
    return {
        "valid": True,
        "replay_count": replay_count,
        "fixture_counts": fixture_counts,
        "replay_unit_counts": replay_unit_counts,
    }


def _build_transfer_report_family_summary(
    *,
    manifest_path: Path,
    fixtures: list[dict[str, Any]],
    run_ref_key: str,
    summary_total_key: str,
    summary_kind_keys: tuple[str, ...],
    validate_payload: Callable[[Path], dict[str, Any]],
    total_output_key: str,
    counts_output_key: str,
    as_error: Callable[[ValueError], Exception],
) -> dict[str, Any]:
    total_count = 0
    kind_counts = {key: 0 for key in summary_kind_keys}
    run_count = 0
    for fixture in fixtures:
        for run in fixture["runs"]:
            run_count += 1
            try:
                artifact_path = _resolve_transfer_report_ref(
                    manifest_path=manifest_path,
                    raw_ref=str(run[run_ref_key]),
                )
            except ValueError as exc:
                raise as_error(exc) from exc
            try:
                payload = validate_payload(artifact_path)
            except ValueError as exc:
                raise as_error(exc) from exc
            summary = payload.get("summary")
            if not isinstance(summary, Mapping):
                raise as_error(
                    ValueError(
                        {
                            "code": "URM_ADEU_INTEGRITY_FIXTURE_INVALID",
                            "message": "validated integrity payload summary must be an object",
                            "context": {"path": str(artifact_path)},
                        }
                    )
                )
            total_count += int(summary[summary_total_key])
            for key in kind_counts:
                kind_counts[key] += int(summary[key])
    return {
        "valid": True,
        "fixture_count": len(fixtures),
        "run_count": run_count,
        total_output_key: total_count,
        counts_output_key: kind_counts,
    }
