from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from urm_runtime.hashing import canonical_json, sha256_canonical_json

from .urm_domain_conformance import (
    DOMAIN_CONFORMANCE_SCHEMA,
    VNEXT_PLUS11_MANIFEST_SCHEMA,
    validate_domain_conformance_report,
)

PORTABILITY_TRANSFER_REPORT_VNEXT_PLUS11_SCHEMA = "portability_transfer_report.vnext_plus11@1"


class PortabilityTransferReportError(ValueError):
    """Raised when transfer-report inputs fail deterministic validation."""


def _read_json_object(path: Path, *, description: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise PortabilityTransferReportError(f"{description} is not readable") from exc
    except json.JSONDecodeError as exc:
        raise PortabilityTransferReportError(f"{description} is invalid JSON") from exc
    if not isinstance(payload, dict):
        raise PortabilityTransferReportError(f"{description} must be a JSON object")
    return payload


def _load_vnext_plus11_manifest_payload(path: Path) -> tuple[dict[str, Any], str]:
    payload = _read_json_object(path, description="vnext+11 manifest")
    if payload.get("schema") != VNEXT_PLUS11_MANIFEST_SCHEMA:
        raise PortabilityTransferReportError("vnext+11 manifest schema is invalid")
    raw_manifest_hash = payload.get("manifest_hash")
    if not isinstance(raw_manifest_hash, str) or not raw_manifest_hash:
        raise PortabilityTransferReportError("vnext+11 manifest missing manifest_hash")
    hash_basis = dict(payload)
    hash_basis.pop("manifest_hash", None)
    recomputed_manifest_hash = sha256_canonical_json(hash_basis)
    if raw_manifest_hash != recomputed_manifest_hash:
        raise PortabilityTransferReportError("vnext+11 manifest_hash mismatch")
    return payload, recomputed_manifest_hash


def _normalized_coverage_summary(coverage_payload: dict[str, Any]) -> dict[str, Any]:
    entries = coverage_payload.get("entries")
    if not isinstance(entries, list):
        raise PortabilityTransferReportError("domain_conformance coverage.entries is invalid")
    normalized_entries: list[dict[str, Any]] = []
    for item in entries:
        if not isinstance(item, dict):
            raise PortabilityTransferReportError("domain_conformance coverage entry is invalid")
        surface_id = str(item.get("surface_id") or "").strip()
        fixture_ids = item.get("fixture_ids")
        if not surface_id or not isinstance(fixture_ids, list):
            raise PortabilityTransferReportError("domain_conformance coverage entry is invalid")
        normalized_entry: dict[str, Any] = {
            "surface_id": surface_id,
            "fixture_ids": sorted(str(value) for value in fixture_ids),
            "valid": bool(item.get("valid") is True),
        }
        if item.get("pressure_test") is True:
            normalized_entry["pressure_test"] = True
        normalized_entries.append(normalized_entry)
    normalized_entries = sorted(normalized_entries, key=lambda item: item["surface_id"])
    return {
        "valid": bool(coverage_payload.get("valid") is True),
        "surface_count": int(coverage_payload.get("surface_count") or 0),
        "covered_surface_count": int(coverage_payload.get("covered_surface_count") or 0),
        "coverage_pct": float(coverage_payload.get("coverage_pct") or 0.0),
        "entries": normalized_entries,
    }


def _normalized_parity_summary(artifact_parity_payload: dict[str, Any]) -> dict[str, Any]:
    fixtures = artifact_parity_payload.get("fixtures")
    if not isinstance(fixtures, list):
        raise PortabilityTransferReportError(
            "domain_conformance artifact_parity.fixtures is invalid"
        )
    normalized_fixtures: list[dict[str, Any]] = []
    for item in fixtures:
        if not isinstance(item, dict):
            raise PortabilityTransferReportError(
                "domain_conformance artifact_parity fixture is invalid"
            )
        fixture_id = str(item.get("fixture_id") or "").strip()
        artifact_schema = str(item.get("artifact_schema") or "").strip()
        if not fixture_id or not artifact_schema:
            raise PortabilityTransferReportError(
                "domain_conformance artifact_parity fixture is invalid"
            )
        normalized_fixture: dict[str, Any] = {
            "fixture_id": fixture_id,
            "artifact_schema": artifact_schema,
            "valid": bool(item.get("valid") is True),
        }
        for key in ("left_ref", "right_ref", "semantic_hash_left", "semantic_hash_right"):
            raw_value = item.get(key)
            if isinstance(raw_value, str) and raw_value:
                normalized_fixture[key] = raw_value
        normalized_fixtures.append(normalized_fixture)
    normalized_fixtures = sorted(normalized_fixtures, key=lambda item: item["fixture_id"])
    return {
        "valid": bool(artifact_parity_payload.get("valid") is True),
        "fixture_count": int(artifact_parity_payload.get("fixture_count") or 0),
        "evaluated_count": int(artifact_parity_payload.get("evaluated_count") or 0),
        "fixtures": normalized_fixtures,
    }


def build_portability_transfer_report_vnext_plus11_payload(
    *,
    vnext_plus11_manifest_path: Path,
    domain_conformance_path: Path,
) -> dict[str, Any]:
    _manifest_payload, manifest_hash = _load_vnext_plus11_manifest_payload(
        vnext_plus11_manifest_path
    )
    domain_conformance_payload = _read_json_object(
        domain_conformance_path,
        description="domain conformance report",
    )
    if domain_conformance_payload.get("schema") != DOMAIN_CONFORMANCE_SCHEMA:
        raise PortabilityTransferReportError("domain conformance schema is invalid")
    validate_domain_conformance_report(domain_conformance_payload)

    domain_conformance_hash = domain_conformance_payload.get("domain_conformance_hash")
    if not isinstance(domain_conformance_hash, str) or not domain_conformance_hash:
        raise PortabilityTransferReportError("domain conformance hash is missing")

    coverage_payload = domain_conformance_payload.get("coverage")
    if not isinstance(coverage_payload, dict):
        raise PortabilityTransferReportError("domain conformance coverage payload is missing")
    if coverage_payload.get("manifest_schema") != VNEXT_PLUS11_MANIFEST_SCHEMA:
        raise PortabilityTransferReportError(
            "domain conformance coverage manifest schema is invalid"
        )
    if coverage_payload.get("manifest_hash") != manifest_hash:
        raise PortabilityTransferReportError("domain conformance coverage manifest hash mismatch")

    artifact_parity_payload = domain_conformance_payload.get("artifact_parity")
    if not isinstance(artifact_parity_payload, dict):
        raise PortabilityTransferReportError(
            "domain conformance artifact parity payload is missing"
        )

    return {
        "schema": PORTABILITY_TRANSFER_REPORT_VNEXT_PLUS11_SCHEMA,
        "vnext_plus11_manifest_hash": manifest_hash,
        "domain_conformance_hash": domain_conformance_hash,
        "coverage_summary": _normalized_coverage_summary(coverage_payload),
        "parity_summary": _normalized_parity_summary(artifact_parity_payload),
    }


def portability_transfer_report_vnext_plus11_markdown(payload: dict[str, Any]) -> str:
    lines: list[str] = [
        "# Portability Transfer Report vNext+11",
        "",
        "Deterministic C3 transfer summary generated from persisted manifest and "
        "conformance artifacts.",
        "",
        "```json",
        canonical_json(payload),
        "```",
        "",
    ]
    return "\n".join(lines)
