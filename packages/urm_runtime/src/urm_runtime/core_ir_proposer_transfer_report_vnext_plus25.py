from __future__ import annotations

from pathlib import Path
from typing import Any, Mapping, cast

from .hashing import canonical_json, sha256_canonical_json
from .stop_gate_tools import (
    CORE_IR_PROPOSAL_SCHEMA,
    CORE_IR_PROPOSER_RESPONSE_SCHEMA,
    CORE_IR_PROPOSER_SURFACE_ID,
    VNEXT_PLUS25_MANIFEST_PATH,
    _compute_vnext_plus19_metrics,
    _compute_vnext_plus20_metrics,
    _compute_vnext_plus21_metrics,
    _compute_vnext_plus22_metrics,
    _compute_vnext_plus23_metrics,
    _compute_vnext_plus24_metrics,
    _compute_vnext_plus25_metrics,
    _core_ir_proposer_contract_projection,
    _discover_repo_root,
    _load_vnext_plus25_manifest_payload,
    _read_json_object,
    _resolve_manifest_relative_path,
)

CORE_IR_PROPOSER_TRANSFER_REPORT_VNEXT_PLUS25_SCHEMA = (
    "core_ir_proposer_transfer_report.vnext_plus25@1"
)
_PROVIDER_PARITY_MATRIX_SCHEMA = "provider_parity.vnext_plus25_matrix@1"
_STOP_GATE_SCHEMA = "stop_gate_metrics@1"


class CoreIRProposerTransferReportVNextPlus25Error(ValueError):
    """Raised when vNext+25 core-ir proposer transfer-report inputs are invalid."""


def _default_stop_gate_metrics_path() -> Path:
    module_path = Path(__file__).resolve()
    repo_root = _discover_repo_root(module_path)
    if repo_root is not None:
        return repo_root / "artifacts" / "stop_gate" / "metrics_v25_closeout.json"
    return module_path.parent / "metrics_v25_closeout.json"


def _default_provider_matrix_path() -> Path:
    module_path = Path(__file__).resolve()
    repo_root = _discover_repo_root(module_path)
    if repo_root is not None:
        return (
            repo_root
            / "apps"
            / "api"
            / "fixtures"
            / "provider_parity"
            / "vnext_plus25_provider_matrix.json"
        )
    return module_path.parent / "vnext_plus25_provider_matrix.json"


def _raise_error(message: str, *, context: Mapping[str, Any] | None = None) -> None:
    payload = {"message": message, "context": dict(context or {})}
    raise CoreIRProposerTransferReportVNextPlus25Error(canonical_json(payload))


def _runtime_observability_from_closeout(
    *,
    stop_gate_metrics_path: Path,
    expected_totals: Mapping[str, int],
    expected_manifest_hash: str,
    expected_contract_pct: float,
    expected_parity_pct: float,
) -> dict[str, int]:
    closeout_payload = _read_json_object(
        stop_gate_metrics_path,
        description="vnext+25 closeout stop-gate metrics",
    )
    if closeout_payload.get("schema") != _STOP_GATE_SCHEMA:
        _raise_error(
            "vnext+25 closeout stop-gate metrics schema is invalid",
            context={"path": str(stop_gate_metrics_path)},
        )

    manifest_hash = closeout_payload.get("vnext_plus25_manifest_hash")
    if manifest_hash != expected_manifest_hash:
        _raise_error(
            "vnext+25 closeout stop-gate manifest hash does not match manifest",
            context={
                "path": str(stop_gate_metrics_path),
                "expected_manifest_hash": expected_manifest_hash,
                "observed_manifest_hash": manifest_hash,
            },
        )

    metrics = closeout_payload.get("metrics")
    if not isinstance(metrics, Mapping):
        _raise_error(
            "vnext+25 closeout stop-gate metrics payload must include metrics object",
            context={"path": str(stop_gate_metrics_path)},
        )
    contract_pct = metrics.get("artifact_core_ir_proposer_contract_valid_pct")
    parity_pct = metrics.get("artifact_core_ir_proposer_provider_parity_pct")
    if contract_pct != expected_contract_pct or parity_pct != expected_parity_pct:
        _raise_error(
            "vnext+25 closeout stop-gate determinism metrics do not match computed values",
            context={
                "path": str(stop_gate_metrics_path),
                "expected_contract_pct": expected_contract_pct,
                "observed_contract_pct": contract_pct,
                "expected_parity_pct": expected_parity_pct,
                "observed_parity_pct": parity_pct,
            },
        )

    runtime_observability = closeout_payload.get("runtime_observability")
    if not isinstance(runtime_observability, Mapping):
        _raise_error(
            "vnext+25 closeout stop-gate metrics must include runtime_observability",
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
                "vnext+25 runtime_observability fields must be non-negative integers",
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
                "vnext+25 runtime_observability totals do not match computed fixture totals",
                context={
                    "path": str(stop_gate_metrics_path),
                    "field": field,
                    "expected": expected_totals[field],
                    "observed": observed[field],
                },
            )

    return observed


def _load_provider_matrix_hash(*, provider_matrix_path: Path) -> str:
    matrix_payload = _read_json_object(
        provider_matrix_path,
        description="vnext+25 provider matrix",
    )
    if matrix_payload.get("schema") != _PROVIDER_PARITY_MATRIX_SCHEMA:
        _raise_error(
            "vnext+25 provider matrix schema is invalid",
            context={"path": str(provider_matrix_path)},
        )

    surfaces = matrix_payload.get("surfaces")
    if not isinstance(surfaces, list):
        _raise_error(
            "vnext+25 provider matrix surfaces must be a list",
            context={"path": str(provider_matrix_path)},
        )
    if not any(
        isinstance(surface, Mapping) and surface.get("surface_id") == CORE_IR_PROPOSER_SURFACE_ID
        for surface in surfaces
    ):
        _raise_error(
            "vnext+25 provider matrix must include adeu_core_ir.propose",
            context={"path": str(provider_matrix_path)},
        )
    return sha256_canonical_json(matrix_payload)


def _coverage_summary(*, manifest: Mapping[str, Any]) -> dict[str, Any]:
    coverage_entries = cast(list[dict[str, Any]], manifest["coverage"])
    surfaces = [
        {
            "fixture_count": len(cast(list[str], entry["fixture_ids"])),
            "fixture_ids": sorted(cast(list[str], entry["fixture_ids"])),
            "surface_id": str(entry["surface_id"]),
        }
        for entry in sorted(coverage_entries, key=lambda item: str(item["surface_id"]))
    ]

    providers_covered = sorted(
        {
            str(run["provider"])
            for fixture_key in (
                "core_ir_proposer_contract_valid_fixtures",
                "core_ir_proposer_provider_parity_fixtures",
            )
            for fixture in cast(list[dict[str, Any]], manifest[fixture_key])
            for run in cast(list[dict[str, Any]], fixture["runs"])
        }
    )

    surface_count = 1
    covered_surface_count = len(surfaces)
    coverage_pct = round((100.0 * covered_surface_count) / float(surface_count), 6)
    return {
        "coverage_pct": coverage_pct,
        "covered_surface_count": covered_surface_count,
        "surface_count": surface_count,
        "surfaces": surfaces,
        "providers_covered": providers_covered,
        "valid": covered_surface_count == surface_count,
    }


def _contract_summary(
    *,
    manifest_path: Path,
    manifest: Mapping[str, Any],
    contract_pct: float,
) -> dict[str, Any]:
    fixtures = cast(list[dict[str, Any]], manifest["core_ir_proposer_contract_valid_fixtures"])
    run_count = 0
    providers: set[str] = set()
    response_schema_values: set[str] = set()
    proposal_packet_schema_values: set[str] = set()
    fixture_summary_values: list[tuple[str, list[dict[str, int]]]] = []

    for fixture_index, fixture in enumerate(fixtures):
        fixture_id = str(fixture.get("fixture_id") or f"contract_fixture_{fixture_index}")
        summary_values: list[dict[str, int]] = []
        runs = cast(list[dict[str, Any]], fixture["runs"])
        for run in runs:
            provider = str(run["provider"])
            providers.add(provider)
            run_count += 1
            request_path = _resolve_manifest_relative_path(
                manifest_path=manifest_path,
                raw_path=run["core_ir_proposer_request_path"],
            )
            response_path = _resolve_manifest_relative_path(
                manifest_path=manifest_path,
                raw_path=run["core_ir_proposer_response_path"],
            )
            packet_path = _resolve_manifest_relative_path(
                manifest_path=manifest_path,
                raw_path=run["core_ir_proposal_packet_path"],
            )
            _core_ir_proposer_contract_projection(
                core_ir_proposer_request_path=request_path,
                core_ir_proposer_response_path=response_path,
                core_ir_proposal_packet_path=packet_path,
                expected_provider=provider,
            )
            response_payload = _read_json_object(
                response_path,
                description="vnext+25 proposer response fixture",
            )
            packet_payload = _read_json_object(
                packet_path,
                description="vnext+25 proposal packet fixture",
            )
            response_schema_values.add(str(response_payload.get("schema")))
            proposal_packet_schema_values.add(str(packet_payload.get("schema")))
            summary = packet_payload.get("summary")
            if not isinstance(summary, Mapping):
                _raise_error(
                    "vnext+25 proposal packet summary must be an object",
                    context={"path": str(packet_path)},
                )
            summary_values.append(
                {
                    "assertion_node_count": int(summary["assertion_node_count"]),
                    "candidate_count": int(summary["candidate_count"]),
                    "integrity_ref_count": int(summary["integrity_ref_count"]),
                    "lane_ref_count": int(summary["lane_ref_count"]),
                    "logic_tree_max_depth": int(summary["logic_tree_max_depth"]),
                    "relation_edge_count": int(summary["relation_edge_count"]),
                }
            )
        fixture_summary_values.append((fixture_id, summary_values))

    if response_schema_values != {CORE_IR_PROPOSER_RESPONSE_SCHEMA}:
        _raise_error(
            "vnext+25 response schema invariants are invalid",
            context={"observed_schemas": sorted(response_schema_values)},
        )
    if proposal_packet_schema_values != {CORE_IR_PROPOSAL_SCHEMA}:
        _raise_error(
            "vnext+25 proposal packet schema invariants are invalid",
            context={"observed_schemas": sorted(proposal_packet_schema_values)},
        )

    for fixture_id, summaries in fixture_summary_values:
        first_summary = summaries[0] if summaries else {}
        if any(summary != first_summary for summary in summaries):
            _raise_error(
                "vnext+25 proposal packet summary invariants drift across providers",
                context={"fixture_id": fixture_id},
            )

    summary_invariants: dict[str, int] = {}
    if fixture_summary_values:
        summary_invariants = fixture_summary_values[0][1][0]

    return {
        "core_ir_proposer_contract_fixture_count": len(fixtures),
        "core_ir_proposer_contract_run_count": run_count,
        "artifact_core_ir_proposer_contract_valid_pct": contract_pct,
        "providers": sorted(providers),
        "response_schema": CORE_IR_PROPOSER_RESPONSE_SCHEMA,
        "proposal_packet_schema": CORE_IR_PROPOSAL_SCHEMA,
        "summary_invariants": summary_invariants,
        "valid": True,
    }


def _parity_summary(
    *,
    manifest_path: Path,
    manifest: Mapping[str, Any],
    parity_pct: float,
) -> dict[str, Any]:
    fixtures = cast(list[dict[str, Any]], manifest["core_ir_proposer_provider_parity_fixtures"])
    run_count = 0
    parity_hashes_by_provider: dict[str, list[str]] = {}

    for fixture in fixtures:
        runs = cast(list[dict[str, Any]], fixture["runs"])
        for run in runs:
            provider = str(run["provider"])
            run_count += 1
            request_path = _resolve_manifest_relative_path(
                manifest_path=manifest_path,
                raw_path=run["core_ir_proposer_request_path"],
            )
            response_path = _resolve_manifest_relative_path(
                manifest_path=manifest_path,
                raw_path=run["core_ir_proposer_response_path"],
            )
            packet_path = _resolve_manifest_relative_path(
                manifest_path=manifest_path,
                raw_path=run["core_ir_proposal_packet_path"],
            )
            _run_hash, parity_hash, _bytes = _core_ir_proposer_contract_projection(
                core_ir_proposer_request_path=request_path,
                core_ir_proposer_response_path=response_path,
                core_ir_proposal_packet_path=packet_path,
                expected_provider=provider,
            )
            parity_hashes_by_provider.setdefault(provider, []).append(parity_hash)

    all_parity_hashes = sorted(
        parity_hash
        for provider_hashes in parity_hashes_by_provider.values()
        for parity_hash in provider_hashes
    )
    parity_hash_match = len(set(all_parity_hashes)) == 1

    parity_hashes_output = {
        provider: provider_hashes[0]
        for provider, provider_hashes in sorted(parity_hashes_by_provider.items())
        if provider_hashes
    }
    return {
        "core_ir_proposer_parity_fixture_count": len(fixtures),
        "core_ir_proposer_parity_run_count": run_count,
        "artifact_core_ir_proposer_provider_parity_pct": parity_pct,
        "parity_fingerprint_hashes_by_provider": parity_hashes_output,
        "parity_fingerprint_hash_match": parity_hash_match,
        "valid": True,
    }


def build_core_ir_proposer_transfer_report_vnext_plus25_payload(
    *,
    vnext_plus25_manifest_path: Path = VNEXT_PLUS25_MANIFEST_PATH,
    provider_matrix_path: Path | None = None,
    stop_gate_metrics_path: Path | None = None,
) -> dict[str, Any]:
    manifest, manifest_hash = _load_vnext_plus25_manifest_payload(
        manifest_path=vnext_plus25_manifest_path,
    )
    provider_matrix_hash = _load_provider_matrix_hash(
        provider_matrix_path=(
            provider_matrix_path
            if provider_matrix_path is not None
            else _default_provider_matrix_path()
        )
    )

    metrics_issues: list[dict[str, Any]] = []
    vnext_plus19_metrics = _compute_vnext_plus19_metrics(manifest_path=None, issues=metrics_issues)
    vnext_plus20_metrics = _compute_vnext_plus20_metrics(manifest_path=None, issues=metrics_issues)
    vnext_plus21_metrics = _compute_vnext_plus21_metrics(manifest_path=None, issues=metrics_issues)
    vnext_plus22_metrics = _compute_vnext_plus22_metrics(manifest_path=None, issues=metrics_issues)
    vnext_plus23_metrics = _compute_vnext_plus23_metrics(manifest_path=None, issues=metrics_issues)
    vnext_plus24_metrics = _compute_vnext_plus24_metrics(manifest_path=None, issues=metrics_issues)
    vnext_plus25_metrics = _compute_vnext_plus25_metrics(
        manifest_path=vnext_plus25_manifest_path,
        issues=metrics_issues,
    )
    if metrics_issues:
        _raise_error(
            "vnext+25 stop-gate metric evidence is invalid",
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
            + int(vnext_plus25_metrics["vnext_plus25_fixture_count_total"])
        ),
        "total_replays": (
            int(vnext_plus19_metrics["vnext_plus19_replay_count_total"])
            + int(vnext_plus20_metrics["vnext_plus20_replay_count_total"])
            + int(vnext_plus21_metrics["vnext_plus21_replay_count_total"])
            + int(vnext_plus22_metrics["vnext_plus22_replay_count_total"])
            + int(vnext_plus23_metrics["vnext_plus23_replay_count_total"])
            + int(vnext_plus24_metrics["vnext_plus24_replay_count_total"])
            + int(vnext_plus25_metrics["vnext_plus25_replay_count_total"])
        ),
        "bytes_hashed_per_replay": (
            int(vnext_plus19_metrics.get("vnext_plus19_bytes_hashed_per_replay", 0))
            + int(vnext_plus20_metrics.get("vnext_plus20_bytes_hashed_per_replay", 0))
            + int(vnext_plus21_metrics.get("vnext_plus21_bytes_hashed_per_replay", 0))
            + int(vnext_plus22_metrics.get("vnext_plus22_bytes_hashed_per_replay", 0))
            + int(vnext_plus23_metrics.get("vnext_plus23_bytes_hashed_per_replay", 0))
            + int(vnext_plus24_metrics.get("vnext_plus24_bytes_hashed_per_replay", 0))
            + int(vnext_plus25_metrics.get("vnext_plus25_bytes_hashed_per_replay", 0))
        ),
        "bytes_hashed_total": (
            int(vnext_plus19_metrics.get("vnext_plus19_bytes_hashed_total", 0))
            + int(vnext_plus20_metrics.get("vnext_plus20_bytes_hashed_total", 0))
            + int(vnext_plus21_metrics.get("vnext_plus21_bytes_hashed_total", 0))
            + int(vnext_plus22_metrics.get("vnext_plus22_bytes_hashed_total", 0))
            + int(vnext_plus23_metrics.get("vnext_plus23_bytes_hashed_total", 0))
            + int(vnext_plus24_metrics.get("vnext_plus24_bytes_hashed_total", 0))
            + int(vnext_plus25_metrics.get("vnext_plus25_bytes_hashed_total", 0))
        ),
    }

    contract_pct = float(vnext_plus25_metrics["artifact_core_ir_proposer_contract_valid_pct"])
    parity_pct = float(vnext_plus25_metrics["artifact_core_ir_proposer_provider_parity_pct"])
    runtime_observability = _runtime_observability_from_closeout(
        stop_gate_metrics_path=(
            stop_gate_metrics_path
            if stop_gate_metrics_path is not None
            else _default_stop_gate_metrics_path()
        ),
        expected_totals=expected_runtime_totals,
        expected_manifest_hash=manifest_hash,
        expected_contract_pct=contract_pct,
        expected_parity_pct=parity_pct,
    )

    contract_summary = _contract_summary(
        manifest_path=vnext_plus25_manifest_path,
        manifest=manifest,
        contract_pct=contract_pct,
    )
    parity_summary = _parity_summary(
        manifest_path=vnext_plus25_manifest_path,
        manifest=manifest,
        parity_pct=parity_pct,
    )

    contract_fixtures = cast(
        list[dict[str, Any]], manifest["core_ir_proposer_contract_valid_fixtures"]
    )
    parity_fixtures = cast(
        list[dict[str, Any]], manifest["core_ir_proposer_provider_parity_fixtures"]
    )

    replay_summary = {
        "all_passed": contract_pct == 100.0 and parity_pct == 100.0,
        "determinism_pct": {
            "artifact_core_ir_proposer_contract_valid_pct": contract_pct,
            "artifact_core_ir_proposer_provider_parity_pct": parity_pct,
        },
        "fixture_counts": {
            "core_ir_proposer_contract_valid": len(contract_fixtures),
            "core_ir_proposer_provider_parity": len(parity_fixtures),
        },
        "provider_run_counts": {
            "core_ir_proposer_contract_valid": sum(
                len(cast(list[Any], fixture["runs"])) for fixture in contract_fixtures
            ),
            "core_ir_proposer_provider_parity": sum(
                len(cast(list[Any], fixture["runs"])) for fixture in parity_fixtures
            ),
        },
        "replay_count": int(manifest["replay_count"]),
        "runtime_observability": runtime_observability,
        "valid": True,
    }

    return {
        "schema": CORE_IR_PROPOSER_TRANSFER_REPORT_VNEXT_PLUS25_SCHEMA,
        "vnext_plus25_manifest_hash": manifest_hash,
        "provider_matrix_hash": provider_matrix_hash,
        "coverage_summary": _coverage_summary(manifest=manifest),
        "core_ir_proposer_contract_summary": contract_summary,
        "core_ir_proposer_parity_summary": parity_summary,
        "replay_summary": replay_summary,
    }
