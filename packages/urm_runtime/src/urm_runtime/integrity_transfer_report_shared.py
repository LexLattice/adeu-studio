from __future__ import annotations

from collections.abc import Mapping
from pathlib import Path
from typing import Any

from .stop_gate_tools import _resolve_manifest_relative_path


def _resolve_transfer_report_ref(*, manifest_path: Path, raw_ref: str) -> Path:
    return _resolve_manifest_relative_path(
        manifest_path=manifest_path,
        raw_path=raw_ref,
    )


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
