from __future__ import annotations

from pathlib import Path
from typing import Any

from urm_runtime.hashing import canonical_json
from urm_runtime.integrity_transfer_report_shared import (
    _build_transfer_report_coverage_summary,
    _build_transfer_report_family_summary,
    _build_transfer_report_replay_summary,
    _make_transfer_report_error_adapter,
)
from urm_runtime.stop_gate_tools import (
    _load_vnext_plus16_manifest_payload,
    _validated_adeu_integrity_cycle_policy_payload,
    _validated_adeu_integrity_dangling_reference_payload,
    _validated_adeu_integrity_deontic_conflict_payload,
)

INTEGRITY_TRANSFER_REPORT_VNEXT_PLUS16_SCHEMA = "integrity_transfer_report.vnext_plus16@1"
_FROZEN_INTEGRITY_SURFACES: tuple[str, ...] = (
    "adeu.integrity.dangling_reference",
    "adeu.integrity.cycle_policy",
    "adeu.integrity.deontic_conflict",
)


class IntegrityTransferReportError(ValueError):
    """Raised when vNext+16 integrity transfer-report inputs are invalid."""


_AS_INTEGRITY_TRANSFER_REPORT_ERROR = _make_transfer_report_error_adapter(
    error_type=IntegrityTransferReportError,
    default_message="invalid vnext+16 transfer report input",
)


def _validate_dangling_reference_payload(path: Path) -> dict[str, Any]:
    return _validated_adeu_integrity_dangling_reference_payload(
        dangling_reference_path=path,
    )


def _validate_cycle_policy_payload(path: Path) -> dict[str, Any]:
    return _validated_adeu_integrity_cycle_policy_payload(
        cycle_policy_path=path,
    )


def _validate_deontic_conflict_payload(path: Path) -> dict[str, Any]:
    return _validated_adeu_integrity_deontic_conflict_payload(
        deontic_conflict_path=path,
    )


def _build_dangling_reference_summary(
    *,
    manifest_path: Path,
    fixtures: list[dict[str, Any]],
) -> dict[str, Any]:
    return _build_transfer_report_family_summary(
        manifest_path=manifest_path,
        fixtures=fixtures,
        run_ref_key="dangling_reference_path",
        summary_total_key="total_issues",
        summary_kind_keys=(
            "missing_node_reference",
            "missing_edge_endpoint",
        ),
        validate_payload=_validate_dangling_reference_payload,
        total_output_key="total_issues",
        counts_output_key="issue_kind_counts",
        as_error=_AS_INTEGRITY_TRANSFER_REPORT_ERROR,
    )


def _build_cycle_policy_summary(
    *,
    manifest_path: Path,
    fixtures: list[dict[str, Any]],
) -> dict[str, Any]:
    return _build_transfer_report_family_summary(
        manifest_path=manifest_path,
        fixtures=fixtures,
        run_ref_key="cycle_policy_path",
        summary_total_key="total_cycles",
        summary_kind_keys=(
            "self_cycle",
            "multi_node_cycle",
        ),
        validate_payload=_validate_cycle_policy_payload,
        total_output_key="total_cycles",
        counts_output_key="cycle_kind_counts",
        as_error=_AS_INTEGRITY_TRANSFER_REPORT_ERROR,
    )


def _build_deontic_conflict_summary(
    *,
    manifest_path: Path,
    fixtures: list[dict[str, Any]],
) -> dict[str, Any]:
    return _build_transfer_report_family_summary(
        manifest_path=manifest_path,
        fixtures=fixtures,
        run_ref_key="deontic_conflict_path",
        summary_total_key="total_conflicts",
        summary_kind_keys=("deontic_conflict",),
        validate_payload=_validate_deontic_conflict_payload,
        total_output_key="total_conflicts",
        counts_output_key="conflict_kind_counts",
        as_error=_AS_INTEGRITY_TRANSFER_REPORT_ERROR,
    )


def build_integrity_transfer_report_vnext_plus16_payload(
    *,
    vnext_plus16_manifest_path: Path,
) -> dict[str, Any]:
    try:
        manifest_payload, manifest_hash = _load_vnext_plus16_manifest_payload(
            manifest_path=vnext_plus16_manifest_path
        )
    except ValueError as exc:
        raise _AS_INTEGRITY_TRANSFER_REPORT_ERROR(exc) from exc

    dangling_reference_fixtures = manifest_payload["dangling_reference_fixtures"]
    cycle_policy_fixtures = manifest_payload["cycle_policy_fixtures"]
    deontic_conflict_fixtures = manifest_payload["deontic_conflict_fixtures"]
    replay_count = int(manifest_payload["replay_count"])
    return {
        "schema": INTEGRITY_TRANSFER_REPORT_VNEXT_PLUS16_SCHEMA,
        "vnext_plus16_manifest_hash": manifest_hash,
        "coverage_summary": _build_transfer_report_coverage_summary(
            manifest_coverage_entries=manifest_payload["coverage"],
            frozen_surface_ids=_FROZEN_INTEGRITY_SURFACES,
        ),
        "dangling_reference_summary": _build_dangling_reference_summary(
            manifest_path=vnext_plus16_manifest_path,
            fixtures=dangling_reference_fixtures,
        ),
        "cycle_policy_summary": _build_cycle_policy_summary(
            manifest_path=vnext_plus16_manifest_path,
            fixtures=cycle_policy_fixtures,
        ),
        "deontic_conflict_summary": _build_deontic_conflict_summary(
            manifest_path=vnext_plus16_manifest_path,
            fixtures=deontic_conflict_fixtures,
        ),
        "replay_summary": _build_transfer_report_replay_summary(
            replay_count=replay_count,
            fixture_families={
                "dangling_reference": dangling_reference_fixtures,
                "cycle_policy": cycle_policy_fixtures,
                "deontic_conflict": deontic_conflict_fixtures,
            },
        ),
    }


def integrity_transfer_report_vnext_plus16_markdown(payload: dict[str, Any]) -> str:
    lines: list[str] = [
        "# Integrity Transfer Report vNext+16",
        "",
        "Deterministic D4 transfer summary generated from persisted vNext+16 "
        "integrity fixtures and diagnostics.",
        "",
        "```json",
        canonical_json(payload),
        "```",
        "",
    ]
    return "\n".join(lines)
