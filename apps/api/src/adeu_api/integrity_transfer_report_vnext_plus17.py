from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from urm_runtime.integrity_transfer_report_shared import (
    _build_transfer_report_coverage_summary,
    _build_transfer_report_family_summary,
    _build_transfer_report_replay_summary,
    _make_transfer_report_error_adapter,
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


_AS_INTEGRITY_TRANSFER_REPORT_ERROR = _make_transfer_report_error_adapter(
    error_type=IntegrityTransferReportError,
    default_message="invalid vnext+17 transfer report input",
)


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
    return _build_transfer_report_family_summary(
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
        as_error=_AS_INTEGRITY_TRANSFER_REPORT_ERROR,
    )


def _build_cycle_policy_extended_summary(
    *,
    manifest_path: Path,
    fixtures: list[dict[str, Any]],
) -> dict[str, Any]:
    return _build_transfer_report_family_summary(
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
        as_error=_AS_INTEGRITY_TRANSFER_REPORT_ERROR,
    )


def _build_deontic_conflict_extended_summary(
    *,
    manifest_path: Path,
    fixtures: list[dict[str, Any]],
) -> dict[str, Any]:
    return _build_transfer_report_family_summary(
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
        as_error=_AS_INTEGRITY_TRANSFER_REPORT_ERROR,
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
        raise _AS_INTEGRITY_TRANSFER_REPORT_ERROR(exc) from exc

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
