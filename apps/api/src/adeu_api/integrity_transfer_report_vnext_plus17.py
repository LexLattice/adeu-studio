from __future__ import annotations

import json
from collections.abc import Callable
from pathlib import Path
from typing import Any

from urm_runtime.hashing import canonical_json
from urm_runtime.integrity_transfer_report_shared import (
    _build_transfer_report_coverage_summary,
    _build_transfer_report_replay_summary,
    _resolve_transfer_report_ref,
)
from urm_runtime.stop_gate_tools import (
    _load_vnext_plus17_manifest_payload,
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


def _build_integrity_family_summary(
    *,
    manifest_path: Path,
    fixtures: list[dict[str, Any]],
    run_ref_key: str,
    summary_total_key: str,
    summary_kind_keys: tuple[str, ...],
    validate_payload: Callable[[Path], dict[str, Any]],
    total_output_key: str,
    counts_output_key: str,
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
                raise _as_integrity_transfer_report_error(exc) from exc
            try:
                payload = validate_payload(artifact_path)
            except ValueError as exc:
                raise _as_integrity_transfer_report_error(exc) from exc
            summary = payload["summary"]
            assert isinstance(summary, dict)
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


def _validate_reference_integrity_extended_payload(path: Path) -> dict[str, Any]:
    return _validated_adeu_integrity_reference_integrity_extended_payload(
        reference_integrity_extended_path=path,
    )


def _validate_cycle_policy_extended_payload(path: Path) -> dict[str, Any]:
    return _validated_adeu_integrity_cycle_policy_extended_payload(
        cycle_policy_extended_path=path,
    )


def _validate_deontic_conflict_extended_payload(path: Path) -> dict[str, Any]:
    return _validated_adeu_integrity_deontic_conflict_extended_payload(
        deontic_conflict_extended_path=path,
    )


def _build_reference_integrity_extended_summary(
    *,
    manifest_path: Path,
    fixtures: list[dict[str, Any]],
) -> dict[str, Any]:
    return _build_integrity_family_summary(
        manifest_path=manifest_path,
        fixtures=fixtures,
        run_ref_key="reference_integrity_extended_path",
        summary_total_key="total_issues",
        summary_kind_keys=(
            "edge_type_constraint_violation",
            "duplicate_edge_identity",
        ),
        validate_payload=_validate_reference_integrity_extended_payload,
        total_output_key="total_issues",
        counts_output_key="issue_kind_counts",
    )


def _build_cycle_policy_extended_summary(
    *,
    manifest_path: Path,
    fixtures: list[dict[str, Any]],
) -> dict[str, Any]:
    return _build_integrity_family_summary(
        manifest_path=manifest_path,
        fixtures=fixtures,
        run_ref_key="cycle_policy_extended_path",
        summary_total_key="total_cycles",
        summary_kind_keys=(
            "self_cycle",
            "multi_node_cycle",
            "dependency_loop",
            "exception_loop",
        ),
        validate_payload=_validate_cycle_policy_extended_payload,
        total_output_key="total_cycles",
        counts_output_key="cycle_kind_counts",
    )


def _build_deontic_conflict_extended_summary(
    *,
    manifest_path: Path,
    fixtures: list[dict[str, Any]],
) -> dict[str, Any]:
    return _build_integrity_family_summary(
        manifest_path=manifest_path,
        fixtures=fixtures,
        run_ref_key="deontic_conflict_extended_path",
        summary_total_key="total_conflicts",
        summary_kind_keys=(
            "deontic_conflict",
            "deontic_tension",
        ),
        validate_payload=_validate_deontic_conflict_extended_payload,
        total_output_key="total_conflicts",
        counts_output_key="conflict_kind_counts",
    )


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
        "coverage_summary": _build_transfer_report_coverage_summary(
            manifest_coverage_entries=manifest_payload["coverage"],
            frozen_surface_ids=_FROZEN_INTEGRITY_EXTENDED_SURFACES,
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
        "replay_summary": _build_transfer_report_replay_summary(
            replay_count=replay_count,
            fixture_families={
                "reference_integrity_extended": reference_integrity_extended_fixtures,
                "cycle_policy_extended": cycle_policy_extended_fixtures,
                "deontic_conflict_extended": deontic_conflict_extended_fixtures,
            },
        ),
    }


def integrity_transfer_report_vnext_plus17_markdown(payload: dict[str, Any]) -> str:
    rendered_payload = json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True)
    lines: list[str] = [
        "# Integrity Transfer Report vNext+17",
        "",
        "Deterministic E4 transfer summary generated from persisted vNext+17 "
        "extended integrity fixtures and diagnostics.",
        "",
        "```json",
        rendered_payload,
        "```",
        "",
    ]
    return "\n".join(lines)
