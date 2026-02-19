from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from urm_runtime.hashing import canonical_json, sha256_canonical_json

PROVIDER_PARITY_TRANSFER_REPORT_VNEXT_PLUS14_SCHEMA = (
    "provider_parity_transfer_report.vnext_plus14@1"
)
VNEXT_PLUS14_MANIFEST_SCHEMA = "stop_gate.vnext_plus14_manifest@1"
PROVIDER_PARITY_MATRIX_SCHEMA = "provider_parity.vnext_plus14_matrix@1"
_FROZEN_PROVIDER_KINDS: tuple[str, ...] = ("mock", "openai", "codex")
_PROVIDER_KIND_RANK = {value: idx for idx, value in enumerate(_FROZEN_PROVIDER_KINDS)}
_FROZEN_PROVIDER_SURFACES: tuple[str, ...] = (
    "adeu.propose",
    "concepts.propose",
    "puzzles.propose",
    "concepts.tournament.live_generation",
    "concepts.tournament.replay_candidates",
)
_REQUIRED_METRIC_FIXTURE_KEYS: tuple[str, ...] = (
    "provider_route_contract_parity_fixtures",
    "codex_candidate_contract_valid_fixtures",
    "provider_parity_replay_determinism_fixtures",
)


class ProviderParityTransferReportError(ValueError):
    """Raised when provider-parity transfer report inputs are invalid."""


def _read_json_object(path: Path, *, description: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise ProviderParityTransferReportError(f"{description} is not readable") from exc
    except json.JSONDecodeError as exc:
        raise ProviderParityTransferReportError(f"{description} is invalid JSON") from exc
    if not isinstance(payload, dict):
        raise ProviderParityTransferReportError(f"{description} must be a JSON object")
    return payload


def _normalize_runs(*, runs: Any, field_name: str) -> list[dict[str, str]]:
    if not isinstance(runs, list) or not runs:
        raise ProviderParityTransferReportError(f"{field_name} runs must be a non-empty list")

    normalized_runs: list[dict[str, str]] = []
    for run_idx, run_payload in enumerate(runs):
        if not isinstance(run_payload, dict) or not run_payload:
            raise ProviderParityTransferReportError(
                f"{field_name} runs[{run_idx}] must be a non-empty object"
            )
        normalized_run: dict[str, str] = {}
        for raw_key, raw_value in sorted(run_payload.items()):
            key = str(raw_key).strip()
            value = str(raw_value).strip()
            if not key or not value:
                raise ProviderParityTransferReportError(
                    f"{field_name} runs[{run_idx}] entries must be non-empty strings"
                )
            normalized_run[key] = value
        normalized_runs.append(normalized_run)
    return normalized_runs


def _normalize_provider_list(*, providers: Any, field_name: str) -> list[str]:
    if not isinstance(providers, list) or not providers:
        raise ProviderParityTransferReportError(
            f"{field_name} must be a non-empty provider list"
        )
    normalized = [str(provider).strip() for provider in providers]
    if any(not provider for provider in normalized):
        raise ProviderParityTransferReportError(
            f"{field_name} contains an empty provider value"
        )
    if any(provider not in _PROVIDER_KIND_RANK for provider in normalized):
        raise ProviderParityTransferReportError(
            f"{field_name} contains unsupported provider values"
        )
    if len(set(normalized)) != len(normalized):
        raise ProviderParityTransferReportError(f"{field_name} contains duplicate providers")
    sorted_normalized = sorted(normalized, key=lambda value: _PROVIDER_KIND_RANK[value])
    if normalized != sorted_normalized:
        raise ProviderParityTransferReportError(
            f"{field_name} must follow canonical provider order {list(_FROZEN_PROVIDER_KINDS)}"
        )
    return sorted_normalized


def _normalize_fixture_entries(
    *,
    entries: Any,
    field_name: str,
    require_provider: bool,
    require_providers: bool,
) -> list[dict[str, Any]]:
    if not isinstance(entries, list) or not entries:
        raise ProviderParityTransferReportError(f"{field_name} must be a non-empty list")

    normalized_entries: list[dict[str, Any]] = []
    seen_fixture_ids: set[str] = set()
    for idx, raw_entry in enumerate(entries):
        if not isinstance(raw_entry, dict):
            raise ProviderParityTransferReportError(f"{field_name}[{idx}] must be an object")

        fixture_id = str(raw_entry.get("fixture_id") or "").strip()
        surface_id = str(raw_entry.get("surface_id") or "").strip()
        if not fixture_id:
            raise ProviderParityTransferReportError(f"{field_name}[{idx}] fixture_id is missing")
        if fixture_id in seen_fixture_ids:
            raise ProviderParityTransferReportError(
                f"{field_name} fixture_id is duplicated: {fixture_id}"
            )
        if surface_id not in _FROZEN_PROVIDER_SURFACES:
            raise ProviderParityTransferReportError(
                f"{field_name}[{idx}] surface_id is invalid: {surface_id!r}"
            )

        normalized_entry: dict[str, Any] = {
            "fixture_id": fixture_id,
            "surface_id": surface_id,
            "runs": _normalize_runs(runs=raw_entry.get("runs"), field_name=f"{field_name}[{idx}]"),
        }

        if require_provider:
            provider = str(raw_entry.get("provider") or "").strip()
            if provider not in _PROVIDER_KIND_RANK:
                raise ProviderParityTransferReportError(
                    f"{field_name}[{idx}] provider is invalid: {provider!r}"
                )
            normalized_entry["provider"] = provider

        if require_providers:
            normalized_entry["providers"] = _normalize_provider_list(
                providers=raw_entry.get("providers"),
                field_name=f"{field_name}[{idx}].providers",
            )

        notes = raw_entry.get("notes")
        if notes is not None:
            note_value = str(notes).strip()
            if not note_value:
                raise ProviderParityTransferReportError(
                    f"{field_name}[{idx}] notes must be non-empty when present"
                )
            normalized_entry["notes"] = note_value

        normalized_entries.append(normalized_entry)
        seen_fixture_ids.add(fixture_id)

    return sorted(normalized_entries, key=lambda item: item["fixture_id"])


def _load_vnext_plus14_manifest_payload(path: Path) -> tuple[dict[str, Any], str]:
    payload = _read_json_object(path, description="vnext+14 manifest")
    if payload.get("schema") != VNEXT_PLUS14_MANIFEST_SCHEMA:
        raise ProviderParityTransferReportError("vnext+14 manifest schema is invalid")

    replay_count = payload.get("replay_count")
    if not isinstance(replay_count, int) or replay_count <= 0:
        raise ProviderParityTransferReportError("vnext+14 manifest replay_count is invalid")

    normalized_manifest: dict[str, Any] = {
        "schema": VNEXT_PLUS14_MANIFEST_SCHEMA,
        "replay_count": replay_count,
    }
    normalized_manifest["provider_route_contract_parity_fixtures"] = _normalize_fixture_entries(
        entries=payload.get("provider_route_contract_parity_fixtures"),
        field_name="provider_route_contract_parity_fixtures",
        require_provider=False,
        require_providers=True,
    )
    normalized_manifest["codex_candidate_contract_valid_fixtures"] = _normalize_fixture_entries(
        entries=payload.get("codex_candidate_contract_valid_fixtures"),
        field_name="codex_candidate_contract_valid_fixtures",
        require_provider=True,
        require_providers=False,
    )
    normalized_manifest["provider_parity_replay_determinism_fixtures"] = _normalize_fixture_entries(
        entries=payload.get("provider_parity_replay_determinism_fixtures"),
        field_name="provider_parity_replay_determinism_fixtures",
        require_provider=True,
        require_providers=False,
    )

    fixture_id_catalog: set[str] = set()
    fixture_surface_catalog: dict[str, str] = {}
    for list_key in _REQUIRED_METRIC_FIXTURE_KEYS:
        for entry in normalized_manifest[list_key]:
            fixture_id = str(entry["fixture_id"])
            if fixture_id in fixture_id_catalog:
                raise ProviderParityTransferReportError(
                    f"vnext+14 manifest fixture_id is duplicated across lists: {fixture_id}"
                )
            fixture_id_catalog.add(fixture_id)
            fixture_surface_catalog[fixture_id] = str(entry["surface_id"])

    coverage_entries = payload.get("coverage")
    if not isinstance(coverage_entries, list) or not coverage_entries:
        raise ProviderParityTransferReportError("vnext+14 manifest coverage is invalid")
    normalized_coverage_entries: list[dict[str, Any]] = []
    seen_surface_ids: set[str] = set()
    for idx, raw_entry in enumerate(coverage_entries):
        if not isinstance(raw_entry, dict):
            raise ProviderParityTransferReportError(f"coverage[{idx}] must be an object")
        surface_id = str(raw_entry.get("surface_id") or "").strip()
        if surface_id not in _FROZEN_PROVIDER_SURFACES:
            raise ProviderParityTransferReportError(
                f"coverage[{idx}] surface_id is invalid: {surface_id!r}"
            )
        if surface_id in seen_surface_ids:
            raise ProviderParityTransferReportError(
                f"coverage surface_id is duplicated: {surface_id}"
            )
        fixture_ids = raw_entry.get("fixture_ids")
        if not isinstance(fixture_ids, list) or not fixture_ids:
            raise ProviderParityTransferReportError(
                f"coverage[{idx}] fixture_ids must be a non-empty list"
            )
        normalized_fixture_ids = sorted(str(value).strip() for value in fixture_ids)
        if any(not fixture_id for fixture_id in normalized_fixture_ids):
            raise ProviderParityTransferReportError(
                f"coverage[{idx}] fixture_ids contains an empty value"
            )
        if len(set(normalized_fixture_ids)) != len(normalized_fixture_ids):
            raise ProviderParityTransferReportError(
                f"coverage[{idx}] fixture_ids contains duplicates"
            )
        unknown_fixture_ids = sorted(
            fixture_id
            for fixture_id in normalized_fixture_ids
            if fixture_id not in fixture_id_catalog
        )
        if unknown_fixture_ids:
            raise ProviderParityTransferReportError(
                f"coverage[{idx}] references unknown fixture_ids: {unknown_fixture_ids}"
            )
        cross_surface_fixture_ids = sorted(
            fixture_id
            for fixture_id in normalized_fixture_ids
            if fixture_surface_catalog.get(fixture_id) != surface_id
        )
        if cross_surface_fixture_ids:
            raise ProviderParityTransferReportError(
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
                raise ProviderParityTransferReportError(
                    f"coverage[{idx}] notes must be non-empty when present"
                )
            normalized_entry["notes"] = note_value
        normalized_coverage_entries.append(normalized_entry)
        seen_surface_ids.add(surface_id)

    expected_surfaces = set(_FROZEN_PROVIDER_SURFACES)
    if seen_surface_ids != expected_surfaces:
        missing = sorted(expected_surfaces - seen_surface_ids)
        extra = sorted(seen_surface_ids - expected_surfaces)
        raise ProviderParityTransferReportError(
            f"coverage surface set mismatch: missing={missing}, extra={extra}"
        )

    normalized_manifest["coverage"] = sorted(
        normalized_coverage_entries, key=lambda item: str(item["surface_id"])
    )

    raw_manifest_hash = payload.get("manifest_hash")
    if not isinstance(raw_manifest_hash, str) or not raw_manifest_hash:
        raise ProviderParityTransferReportError("vnext+14 manifest missing manifest_hash")
    recomputed_manifest_hash = sha256_canonical_json(normalized_manifest)
    if raw_manifest_hash != recomputed_manifest_hash:
        raise ProviderParityTransferReportError("vnext+14 manifest_hash mismatch")

    normalized_manifest["manifest_hash"] = recomputed_manifest_hash
    return normalized_manifest, recomputed_manifest_hash


def _load_provider_matrix_payload(path: Path) -> tuple[dict[str, Any], str, dict[str, list[str]]]:
    payload = _read_json_object(path, description="provider parity matrix")
    if payload.get("schema") != PROVIDER_PARITY_MATRIX_SCHEMA:
        raise ProviderParityTransferReportError("provider parity matrix schema is invalid")
    raw_surfaces = payload.get("surfaces")
    if not isinstance(raw_surfaces, list) or not raw_surfaces:
        raise ProviderParityTransferReportError("provider parity matrix surfaces is invalid")

    normalized_surfaces: list[dict[str, Any]] = []
    by_surface: dict[str, list[str]] = {}
    for idx, raw_entry in enumerate(raw_surfaces):
        if not isinstance(raw_entry, dict):
            raise ProviderParityTransferReportError(
                f"provider parity matrix surfaces[{idx}] must be an object"
            )
        surface_id = str(raw_entry.get("surface_id") or "").strip()
        if surface_id not in _FROZEN_PROVIDER_SURFACES:
            raise ProviderParityTransferReportError(
                f"provider parity matrix surfaces[{idx}] surface_id is invalid: {surface_id!r}"
            )
        if surface_id in by_surface:
            raise ProviderParityTransferReportError(
                f"provider parity matrix surface_id is duplicated: {surface_id}"
            )
        supported_providers = _normalize_provider_list(
            providers=raw_entry.get("supported_providers"),
            field_name=f"provider parity matrix surfaces[{idx}].supported_providers",
        )
        normalized_entry: dict[str, Any] = {
            "surface_id": surface_id,
            "supported_providers": supported_providers,
        }
        notes = raw_entry.get("notes")
        if notes is not None:
            note_value = str(notes).strip()
            if not note_value:
                raise ProviderParityTransferReportError(
                    f"provider parity matrix surfaces[{idx}] notes must be non-empty when present"
                )
            normalized_entry["notes"] = note_value
        normalized_surfaces.append(normalized_entry)
        by_surface[surface_id] = supported_providers

    expected_surfaces = set(_FROZEN_PROVIDER_SURFACES)
    actual_surfaces = set(by_surface)
    if actual_surfaces != expected_surfaces:
        missing = sorted(expected_surfaces - actual_surfaces)
        extra = sorted(actual_surfaces - expected_surfaces)
        raise ProviderParityTransferReportError(
            f"provider parity matrix surface set mismatch: missing={missing}, extra={extra}"
        )

    normalized_matrix = {
        "schema": PROVIDER_PARITY_MATRIX_SCHEMA,
        "surfaces": sorted(normalized_surfaces, key=lambda item: str(item["surface_id"])),
    }
    return normalized_matrix, sha256_canonical_json(normalized_matrix), by_surface


def _build_coverage_summary(
    *,
    manifest_coverage_entries: list[dict[str, Any]],
) -> dict[str, Any]:
    entries = [
        {
            "surface_id": str(entry["surface_id"]),
            "fixture_ids": list(entry["fixture_ids"]),
            "valid": True,
            **({"notes": entry["notes"]} if "notes" in entry else {}),
        }
        for entry in manifest_coverage_entries
    ]
    surface_count = len(_FROZEN_PROVIDER_SURFACES)
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


def _build_parity_summary(
    *,
    manifest_payload: dict[str, Any],
    matrix_by_surface: dict[str, list[str]],
) -> dict[str, Any]:
    provider_route_fixtures = manifest_payload["provider_route_contract_parity_fixtures"]
    codex_fixtures = manifest_payload["codex_candidate_contract_valid_fixtures"]
    replay_fixtures = manifest_payload["provider_parity_replay_determinism_fixtures"]
    route_provider_unit_count = sum(len(entry["providers"]) for entry in provider_route_fixtures)
    matrix_provider_unit_count = sum(len(providers) for providers in matrix_by_surface.values())
    route_providers_by_surface: dict[str, list[str]] = {}
    duplicate_surface_ids: list[str] = []
    for entry in provider_route_fixtures:
        surface_id = str(entry["surface_id"])
        if surface_id in route_providers_by_surface:
            duplicate_surface_ids.append(surface_id)
        providers = [str(provider) for provider in entry["providers"]]
        route_providers_by_surface[surface_id] = providers

    mapping_mismatches: list[dict[str, Any]] = []
    for surface_id in _FROZEN_PROVIDER_SURFACES:
        route_providers = route_providers_by_surface.get(surface_id, [])
        matrix_providers = matrix_by_surface.get(surface_id, [])
        if route_providers != matrix_providers:
            mapping_mismatches.append(
                {
                    "surface_id": surface_id,
                    "route_providers": route_providers,
                    "matrix_providers": matrix_providers,
                }
            )

    return {
        "valid": len(mapping_mismatches) == 0 and not duplicate_surface_ids,
        "surface_count": len(_FROZEN_PROVIDER_SURFACES),
        "matrix_surface_count": len(matrix_by_surface),
        "matrix_provider_unit_count": matrix_provider_unit_count,
        "route_provider_unit_count": route_provider_unit_count,
        "duplicate_surface_count": len(duplicate_surface_ids),
        "duplicate_surface_ids": sorted(set(duplicate_surface_ids)),
        "mapping_mismatch_count": len(mapping_mismatches),
        "mapping_mismatches": mapping_mismatches,
        "fixture_counts": {
            "provider_route_contract_parity": len(provider_route_fixtures),
            "codex_candidate_contract_valid": len(codex_fixtures),
            "provider_parity_replay_determinism": len(replay_fixtures),
        },
    }


def build_provider_parity_transfer_report_vnext_plus14_payload(
    *,
    vnext_plus14_manifest_path: Path,
    provider_matrix_path: Path,
) -> dict[str, Any]:
    manifest_payload, manifest_hash = _load_vnext_plus14_manifest_payload(
        vnext_plus14_manifest_path
    )
    _matrix_payload, matrix_hash, matrix_by_surface = _load_provider_matrix_payload(
        provider_matrix_path
    )
    return {
        "schema": PROVIDER_PARITY_TRANSFER_REPORT_VNEXT_PLUS14_SCHEMA,
        "vnext_plus14_manifest_hash": manifest_hash,
        "provider_matrix_hash": matrix_hash,
        "parity_summary": _build_parity_summary(
            manifest_payload=manifest_payload,
            matrix_by_surface=matrix_by_surface,
        ),
        "coverage_summary": _build_coverage_summary(
            manifest_coverage_entries=manifest_payload["coverage"],
        ),
    }


def provider_parity_transfer_report_vnext_plus14_markdown(payload: dict[str, Any]) -> str:
    lines: list[str] = [
        "# Provider Parity Transfer Report vNext+14",
        "",
        "Deterministic B3 transfer summary generated from persisted provider-parity "
        "manifest and matrix artifacts.",
        "",
        "```json",
        canonical_json(payload),
        "```",
        "",
    ]
    return "\n".join(lines)
