from __future__ import annotations

from pathlib import Path
from typing import Any

from urm_runtime.hashing import canonical_json
from urm_runtime.stop_gate_tools import (
    _load_vnext_plus17_manifest_payload,
    _resolve_manifest_relative_path,
    _validated_adeu_integrity_cycle_policy_extended_payload,
    _validated_adeu_integrity_deontic_conflict_extended_payload,
    _validated_adeu_integrity_reference_integrity_extended_payload,
)

INTEGRITY_TRANSFER_REPORT_VNEXT_PLUS17_SCHEMA = "integrity_transfer_report.vnext_plus17@1"
_FROZEN_INTEGRITY_EXTENDED_SURFACES: tuple[str, ...] = (
    "adeu.integrity.reference_integrity_extended",
    "adeu.integrity.cycle_policy_extended",
    "adeu.integrity.deontic_conflict_extended",
)


class IntegrityTransferReportError(ValueError):
    """Raised when vNext+17 integrity transfer-report inputs are invalid."""


def _as_integrity_transfer_report_error(exc: ValueError) -> IntegrityTransferReportError:
    issue = exc.args[0] if exc.args else None
    if isinstance(issue, dict):
        code = str(issue.get("code") or "URM_ADEU_INTEGRITY_FIXTURE_INVALID")
        message = str(issue.get("message") or "invalid vnext+17 transfer report input")
        context = issue.get("context", {})
        return IntegrityTransferReportError(
            f"{code}: {message} ({canonical_json(context)})"
        )
    return IntegrityTransferReportError(str(exc))


def _resolve_ref(*, manifest_path: Path, raw_ref: str) -> Path:
    try:
        return _resolve_manifest_relative_path(
            manifest_path=manifest_path,
            raw_path=raw_ref,
        )
    except ValueError as exc:
        raise _as_integrity_transfer_report_error(exc) from exc


def _build_coverage_summary(*, manifest_coverage_entries: list[dict[str, Any]]) -> dict[str, Any]:
    entries = [
        {
            "surface_id": str(entry["surface_id"]),
            "fixture_ids": list(entry["fixture_ids"]),
            "valid": True,
            **({"notes": entry["notes"]} if "notes" in entry else {}),
        }
        for entry in sorted(manifest_coverage_entries, key=lambda item: str(item["surface_id"]))
    ]
    surface_count = len(_FROZEN_INTEGRITY_EXTENDED_SURFACES)
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


def _build_reference_integrity_extended_summary(
    *,
    manifest_path: Path,
    fixtures: list[dict[str, Any]],
) -> dict[str, Any]:
    total_issues = 0
    issue_kind_counts = {
        "edge_type_constraint_violation": 0,
        "duplicate_edge_identity": 0,
    }
    run_count = 0
    for fixture in fixtures:
        for run in fixture["runs"]:
            run_count += 1
            artifact_path = _resolve_ref(
                manifest_path=manifest_path,
                raw_ref=str(run["reference_integrity_extended_path"]),
            )
            try:
                payload = _validated_adeu_integrity_reference_integrity_extended_payload(
                    reference_integrity_extended_path=artifact_path,
                )
            except ValueError as exc:
                raise _as_integrity_transfer_report_error(exc) from exc
            summary = payload["summary"]
            assert isinstance(summary, dict)
            total_issues += int(summary["total_issues"])
            for key in issue_kind_counts:
                issue_kind_counts[key] += int(summary[key])
    return {
        "valid": True,
        "fixture_count": len(fixtures),
        "run_count": run_count,
        "total_issues": total_issues,
        "issue_kind_counts": issue_kind_counts,
    }


def _build_cycle_policy_extended_summary(
    *,
    manifest_path: Path,
    fixtures: list[dict[str, Any]],
) -> dict[str, Any]:
    total_cycles = 0
    cycle_kind_counts = {
        "self_cycle": 0,
        "multi_node_cycle": 0,
        "dependency_loop": 0,
        "exception_loop": 0,
    }
    run_count = 0
    for fixture in fixtures:
        for run in fixture["runs"]:
            run_count += 1
            artifact_path = _resolve_ref(
                manifest_path=manifest_path,
                raw_ref=str(run["cycle_policy_extended_path"]),
            )
            try:
                payload = _validated_adeu_integrity_cycle_policy_extended_payload(
                    cycle_policy_extended_path=artifact_path,
                )
            except ValueError as exc:
                raise _as_integrity_transfer_report_error(exc) from exc
            summary = payload["summary"]
            assert isinstance(summary, dict)
            total_cycles += int(summary["total_cycles"])
            for key in cycle_kind_counts:
                cycle_kind_counts[key] += int(summary[key])
    return {
        "valid": True,
        "fixture_count": len(fixtures),
        "run_count": run_count,
        "total_cycles": total_cycles,
        "cycle_kind_counts": cycle_kind_counts,
    }


def _build_deontic_conflict_extended_summary(
    *,
    manifest_path: Path,
    fixtures: list[dict[str, Any]],
) -> dict[str, Any]:
    total_conflicts = 0
    conflict_kind_counts = {
        "deontic_conflict": 0,
        "deontic_tension": 0,
    }
    run_count = 0
    for fixture in fixtures:
        for run in fixture["runs"]:
            run_count += 1
            artifact_path = _resolve_ref(
                manifest_path=manifest_path,
                raw_ref=str(run["deontic_conflict_extended_path"]),
            )
            try:
                payload = _validated_adeu_integrity_deontic_conflict_extended_payload(
                    deontic_conflict_extended_path=artifact_path,
                )
            except ValueError as exc:
                raise _as_integrity_transfer_report_error(exc) from exc
            summary = payload["summary"]
            assert isinstance(summary, dict)
            total_conflicts += int(summary["total_conflicts"])
            for key in conflict_kind_counts:
                conflict_kind_counts[key] += int(summary[key])
    return {
        "valid": True,
        "fixture_count": len(fixtures),
        "run_count": run_count,
        "total_conflicts": total_conflicts,
        "conflict_kind_counts": conflict_kind_counts,
    }


def _build_replay_summary(
    *,
    replay_count: int,
    reference_integrity_extended_fixtures: list[dict[str, Any]],
    cycle_policy_extended_fixtures: list[dict[str, Any]],
    deontic_conflict_extended_fixtures: list[dict[str, Any]],
) -> dict[str, Any]:
    return {
        "valid": True,
        "replay_count": replay_count,
        "fixture_counts": {
            "reference_integrity_extended": len(reference_integrity_extended_fixtures),
            "cycle_policy_extended": len(cycle_policy_extended_fixtures),
            "deontic_conflict_extended": len(deontic_conflict_extended_fixtures),
        },
        "replay_unit_counts": {
            "reference_integrity_extended": sum(
                len(fixture["runs"]) for fixture in reference_integrity_extended_fixtures
            ),
            "cycle_policy_extended": sum(
                len(fixture["runs"]) for fixture in cycle_policy_extended_fixtures
            ),
            "deontic_conflict_extended": sum(
                len(fixture["runs"]) for fixture in deontic_conflict_extended_fixtures
            ),
        },
    }


def build_integrity_transfer_report_vnext_plus17_payload(
    *,
    vnext_plus17_manifest_path: Path,
) -> dict[str, Any]:
    try:
        manifest_payload, manifest_hash = _load_vnext_plus17_manifest_payload(
            manifest_path=vnext_plus17_manifest_path
        )
    except ValueError as exc:
        raise _as_integrity_transfer_report_error(exc) from exc

    reference_integrity_extended_fixtures = manifest_payload[
        "reference_integrity_extended_fixtures"
    ]
    cycle_policy_extended_fixtures = manifest_payload["cycle_policy_extended_fixtures"]
    deontic_conflict_extended_fixtures = manifest_payload[
        "deontic_conflict_extended_fixtures"
    ]
    replay_count = int(manifest_payload["replay_count"])
    return {
        "schema": INTEGRITY_TRANSFER_REPORT_VNEXT_PLUS17_SCHEMA,
        "vnext_plus17_manifest_hash": manifest_hash,
        "coverage_summary": _build_coverage_summary(
            manifest_coverage_entries=manifest_payload["coverage"],
        ),
        "reference_integrity_extended_summary": _build_reference_integrity_extended_summary(
            manifest_path=vnext_plus17_manifest_path,
            fixtures=reference_integrity_extended_fixtures,
        ),
        "cycle_policy_extended_summary": _build_cycle_policy_extended_summary(
            manifest_path=vnext_plus17_manifest_path,
            fixtures=cycle_policy_extended_fixtures,
        ),
        "deontic_conflict_extended_summary": _build_deontic_conflict_extended_summary(
            manifest_path=vnext_plus17_manifest_path,
            fixtures=deontic_conflict_extended_fixtures,
        ),
        "replay_summary": _build_replay_summary(
            replay_count=replay_count,
            reference_integrity_extended_fixtures=reference_integrity_extended_fixtures,
            cycle_policy_extended_fixtures=cycle_policy_extended_fixtures,
            deontic_conflict_extended_fixtures=deontic_conflict_extended_fixtures,
        ),
    }


def integrity_transfer_report_vnext_plus17_markdown(payload: dict[str, Any]) -> str:
    lines: list[str] = [
        "# Integrity Transfer Report vNext+17",
        "",
        "Deterministic E4 transfer summary generated from persisted vNext+17 "
        "extended integrity fixtures and diagnostics.",
        "",
        "```json",
        canonical_json(payload),
        "```",
        "",
    ]
    return "\n".join(lines)
