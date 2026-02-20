from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from urm_runtime.hashing import canonical_json, sha256_canonical_json

INTEGRITY_TRANSFER_REPORT_VNEXT_PLUS16_SCHEMA = "integrity_transfer_report.vnext_plus16@1"
VNEXT_PLUS16_MANIFEST_SCHEMA = "stop_gate.vnext_plus16_manifest@1"
VNEXT_PLUS16_REPLAY_COUNT = 3
DANGLING_REFERENCE_SCHEMA = "adeu_integrity_dangling_reference@0.1"
CYCLE_POLICY_SCHEMA = "adeu_integrity_cycle_policy@0.1"
DEONTIC_CONFLICT_SCHEMA = "adeu_integrity_deontic_conflict@0.1"
_FROZEN_INTEGRITY_SURFACES: tuple[str, ...] = (
    "adeu.integrity.dangling_reference",
    "adeu.integrity.cycle_policy",
    "adeu.integrity.deontic_conflict",
)
_REQUIRED_METRIC_FIXTURE_KEYS: tuple[str, ...] = (
    "dangling_reference_fixtures",
    "cycle_policy_fixtures",
    "deontic_conflict_fixtures",
)


class IntegrityTransferReportError(ValueError):
    """Raised when vNext+16 integrity transfer-report inputs are invalid."""


def _read_json_object(path: Path, *, description: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise IntegrityTransferReportError(f"{description} is not readable") from exc
    except json.JSONDecodeError as exc:
        raise IntegrityTransferReportError(f"{description} is invalid JSON") from exc
    if not isinstance(payload, dict):
        raise IntegrityTransferReportError(f"{description} must be a JSON object")
    return payload


def _normalize_run_refs(
    *,
    runs: Any,
    field_name: str,
    replay_count: int,
    required_keys: tuple[str, ...],
) -> list[dict[str, str]]:
    if not isinstance(runs, list) or not runs:
        raise IntegrityTransferReportError(f"{field_name} runs must be a non-empty list")
    if len(runs) != replay_count:
        raise IntegrityTransferReportError(
            f"{field_name} runs must have exactly replay_count={replay_count} entries"
        )

    normalized_runs: list[dict[str, str]] = []
    for run_idx, raw_run in enumerate(runs):
        if not isinstance(raw_run, dict) or not raw_run:
            raise IntegrityTransferReportError(
                f"{field_name} runs[{run_idx}] must be a non-empty object"
            )
        normalized_run: dict[str, str] = {}
        for raw_key, raw_value in sorted(raw_run.items()):
            key = str(raw_key).strip()
            value = str(raw_value).strip()
            if not key or not value:
                raise IntegrityTransferReportError(
                    f"{field_name} runs[{run_idx}] entries must be non-empty strings"
                )
            normalized_run[key] = value
        missing_keys = [key for key in required_keys if key not in normalized_run]
        if missing_keys:
            raise IntegrityTransferReportError(
                f"{field_name} runs[{run_idx}] missing required refs: {missing_keys}"
            )
        normalized_runs.append(normalized_run)
    return normalized_runs


def _normalize_fixture_entries(
    *,
    entries: Any,
    field_name: str,
    replay_count: int,
    expected_surface_id: str,
    required_run_keys: tuple[str, ...],
) -> list[dict[str, Any]]:
    if not isinstance(entries, list) or not entries:
        raise IntegrityTransferReportError(f"{field_name} must be a non-empty list")

    normalized_entries: list[dict[str, Any]] = []
    seen_fixture_ids: set[str] = set()
    for idx, raw_entry in enumerate(entries):
        if not isinstance(raw_entry, dict):
            raise IntegrityTransferReportError(f"{field_name}[{idx}] must be an object")

        fixture_id = str(raw_entry.get("fixture_id") or "").strip()
        surface_id = str(raw_entry.get("surface_id") or "").strip()
        if not fixture_id:
            raise IntegrityTransferReportError(f"{field_name}[{idx}] fixture_id is missing")
        if fixture_id in seen_fixture_ids:
            raise IntegrityTransferReportError(
                f"{field_name} fixture_id is duplicated: {fixture_id}"
            )
        if surface_id != expected_surface_id:
            raise IntegrityTransferReportError(
                f"{field_name}[{idx}] surface_id must equal {expected_surface_id!r}"
            )

        normalized_entry: dict[str, Any] = {
            "fixture_id": fixture_id,
            "surface_id": surface_id,
            "runs": _normalize_run_refs(
                runs=raw_entry.get("runs"),
                field_name=f"{field_name}[{idx}]",
                replay_count=replay_count,
                required_keys=required_run_keys,
            ),
        }
        notes = raw_entry.get("notes")
        if notes is not None:
            note_value = str(notes).strip()
            if not note_value:
                raise IntegrityTransferReportError(
                    f"{field_name}[{idx}] notes must be non-empty when present"
                )
            normalized_entry["notes"] = note_value
        normalized_entries.append(normalized_entry)
        seen_fixture_ids.add(fixture_id)
    return sorted(normalized_entries, key=lambda item: str(item["fixture_id"]))


def _load_vnext_plus16_manifest_payload(path: Path) -> tuple[dict[str, Any], str]:
    payload = _read_json_object(path, description="vnext+16 manifest")
    if payload.get("schema") != VNEXT_PLUS16_MANIFEST_SCHEMA:
        raise IntegrityTransferReportError("vnext+16 manifest schema is invalid")

    replay_count = payload.get("replay_count")
    if replay_count != VNEXT_PLUS16_REPLAY_COUNT:
        raise IntegrityTransferReportError("vnext+16 manifest replay_count is invalid")

    normalized_manifest: dict[str, Any] = {
        "schema": VNEXT_PLUS16_MANIFEST_SCHEMA,
        "replay_count": VNEXT_PLUS16_REPLAY_COUNT,
    }
    normalized_manifest["dangling_reference_fixtures"] = _normalize_fixture_entries(
        entries=payload.get("dangling_reference_fixtures"),
        field_name="dangling_reference_fixtures",
        replay_count=VNEXT_PLUS16_REPLAY_COUNT,
        expected_surface_id="adeu.integrity.dangling_reference",
        required_run_keys=("dangling_reference_path",),
    )
    normalized_manifest["cycle_policy_fixtures"] = _normalize_fixture_entries(
        entries=payload.get("cycle_policy_fixtures"),
        field_name="cycle_policy_fixtures",
        replay_count=VNEXT_PLUS16_REPLAY_COUNT,
        expected_surface_id="adeu.integrity.cycle_policy",
        required_run_keys=("cycle_policy_path",),
    )
    normalized_manifest["deontic_conflict_fixtures"] = _normalize_fixture_entries(
        entries=payload.get("deontic_conflict_fixtures"),
        field_name="deontic_conflict_fixtures",
        replay_count=VNEXT_PLUS16_REPLAY_COUNT,
        expected_surface_id="adeu.integrity.deontic_conflict",
        required_run_keys=("deontic_conflict_path",),
    )

    fixture_id_catalog: set[str] = set()
    fixture_surface_catalog: dict[str, str] = {}
    for list_key in _REQUIRED_METRIC_FIXTURE_KEYS:
        for entry in normalized_manifest[list_key]:
            fixture_id = str(entry["fixture_id"])
            if fixture_id in fixture_id_catalog:
                raise IntegrityTransferReportError(
                    f"vnext+16 manifest fixture_id is duplicated across lists: {fixture_id}"
                )
            fixture_id_catalog.add(fixture_id)
            fixture_surface_catalog[fixture_id] = str(entry["surface_id"])

    coverage_entries = payload.get("coverage")
    if not isinstance(coverage_entries, list) or not coverage_entries:
        raise IntegrityTransferReportError("vnext+16 manifest coverage is invalid")

    normalized_coverage_entries: list[dict[str, Any]] = []
    seen_surface_ids: set[str] = set()
    for idx, raw_entry in enumerate(coverage_entries):
        if not isinstance(raw_entry, dict):
            raise IntegrityTransferReportError(f"coverage[{idx}] must be an object")
        surface_id = str(raw_entry.get("surface_id") or "").strip()
        if surface_id not in _FROZEN_INTEGRITY_SURFACES:
            raise IntegrityTransferReportError(
                f"coverage[{idx}] surface_id is invalid: {surface_id!r}"
            )
        if surface_id in seen_surface_ids:
            raise IntegrityTransferReportError(
                f"coverage surface_id is duplicated: {surface_id}"
            )
        fixture_ids = raw_entry.get("fixture_ids")
        if not isinstance(fixture_ids, list) or not fixture_ids:
            raise IntegrityTransferReportError(
                f"coverage[{idx}] fixture_ids must be a non-empty list"
            )
        normalized_fixture_ids = sorted(str(value).strip() for value in fixture_ids)
        if any(not fixture_id for fixture_id in normalized_fixture_ids):
            raise IntegrityTransferReportError(
                f"coverage[{idx}] fixture_ids contains an empty value"
            )
        if len(set(normalized_fixture_ids)) != len(normalized_fixture_ids):
            raise IntegrityTransferReportError(
                f"coverage[{idx}] fixture_ids contains duplicates"
            )
        unknown_fixture_ids = sorted(
            fixture_id
            for fixture_id in normalized_fixture_ids
            if fixture_id not in fixture_id_catalog
        )
        if unknown_fixture_ids:
            raise IntegrityTransferReportError(
                f"coverage[{idx}] references unknown fixture_ids: {unknown_fixture_ids}"
            )
        cross_surface_fixture_ids = sorted(
            fixture_id
            for fixture_id in normalized_fixture_ids
            if fixture_surface_catalog.get(fixture_id) != surface_id
        )
        if cross_surface_fixture_ids:
            raise IntegrityTransferReportError(
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
                raise IntegrityTransferReportError(
                    f"coverage[{idx}] notes must be non-empty when present"
                )
            normalized_entry["notes"] = note_value
        normalized_coverage_entries.append(normalized_entry)
        seen_surface_ids.add(surface_id)

    expected_surfaces = set(_FROZEN_INTEGRITY_SURFACES)
    if seen_surface_ids != expected_surfaces:
        missing = sorted(expected_surfaces - seen_surface_ids)
        extra = sorted(seen_surface_ids - expected_surfaces)
        raise IntegrityTransferReportError(
            f"coverage surface set mismatch: missing={missing}, extra={extra}"
        )
    normalized_manifest["coverage"] = sorted(
        normalized_coverage_entries, key=lambda item: str(item["surface_id"])
    )

    raw_manifest_hash = payload.get("manifest_hash")
    if not isinstance(raw_manifest_hash, str) or not raw_manifest_hash:
        raise IntegrityTransferReportError("vnext+16 manifest missing manifest_hash")
    recomputed_manifest_hash = sha256_canonical_json(normalized_manifest)
    if raw_manifest_hash != recomputed_manifest_hash:
        raise IntegrityTransferReportError("vnext+16 manifest_hash mismatch")

    normalized_manifest["manifest_hash"] = recomputed_manifest_hash
    return normalized_manifest, recomputed_manifest_hash


def _resolve_ref(*, manifest_path: Path, raw_ref: str) -> Path:
    candidate = Path(raw_ref)
    if candidate.is_absolute():
        return candidate.resolve()
    return (manifest_path.parent / candidate).resolve()


def _canonical_cycle_rotation(node_ids: list[str]) -> list[str]:
    if len(node_ids) <= 1:
        return list(node_ids)
    rotations = [node_ids[index:] + node_ids[:index] for index in range(len(node_ids))]
    return min(rotations)


def _validate_dangling_reference_artifact(path: Path) -> dict[str, Any]:
    payload = _read_json_object(path, description=f"dangling-reference artifact {path}")
    if payload.get("schema") != DANGLING_REFERENCE_SCHEMA:
        raise IntegrityTransferReportError(
            f"dangling-reference artifact has invalid schema: {path}"
        )
    source_text_hash = str(payload.get("source_text_hash") or "").strip()
    if not source_text_hash:
        raise IntegrityTransferReportError(
            f"dangling-reference artifact missing source_text_hash: {path}"
        )
    summary = payload.get("summary")
    issues = payload.get("issues")
    if not isinstance(summary, dict):
        raise IntegrityTransferReportError(
            f"dangling-reference artifact summary is invalid: {path}"
        )
    if not isinstance(issues, list):
        raise IntegrityTransferReportError(
            f"dangling-reference artifact issues is invalid: {path}"
        )

    kind_counts = {
        "missing_node_reference": 0,
        "missing_edge_endpoint": 0,
    }
    order_keys: list[tuple[str, str, str]] = []
    for issue in issues:
        if not isinstance(issue, dict):
            raise IntegrityTransferReportError(
                f"dangling-reference artifact issue is invalid: {path}"
            )
        kind = str(issue.get("kind") or "").strip()
        subject_id = str(issue.get("subject_id") or "").strip()
        related_id = issue.get("related_id")
        if related_id is None:
            related_id = ""
        if not isinstance(related_id, str):
            raise IntegrityTransferReportError(
                f"dangling-reference artifact related_id is invalid: {path}"
            )
        if kind not in kind_counts:
            raise IntegrityTransferReportError(
                f"dangling-reference artifact issue kind is invalid: {path}"
            )
        if not subject_id:
            raise IntegrityTransferReportError(
                f"dangling-reference artifact subject_id is invalid: {path}"
            )
        kind_counts[kind] += 1
        order_keys.append((kind, subject_id, related_id))

    if order_keys != sorted(order_keys):
        raise IntegrityTransferReportError(
            f"dangling-reference artifact issues are not deterministically ordered: {path}"
        )

    total_issues = summary.get("total_issues")
    if not isinstance(total_issues, int) or total_issues != len(issues):
        raise IntegrityTransferReportError(
            f"dangling-reference artifact summary.total_issues mismatch: {path}"
        )
    for kind, count in kind_counts.items():
        raw_summary_count = summary.get(kind)
        if not isinstance(raw_summary_count, int) or raw_summary_count != count:
            raise IntegrityTransferReportError(
                f"dangling-reference artifact summary.{kind} mismatch: {path}"
            )

    return {
        "source_text_hash": source_text_hash,
        "total_issues": total_issues,
        "kind_counts": kind_counts,
    }


def _validate_cycle_policy_artifact(path: Path) -> dict[str, Any]:
    payload = _read_json_object(path, description=f"cycle-policy artifact {path}")
    if payload.get("schema") != CYCLE_POLICY_SCHEMA:
        raise IntegrityTransferReportError(
            f"cycle-policy artifact has invalid schema: {path}"
        )
    source_text_hash = str(payload.get("source_text_hash") or "").strip()
    if not source_text_hash:
        raise IntegrityTransferReportError(
            f"cycle-policy artifact missing source_text_hash: {path}"
        )
    summary = payload.get("summary")
    cycles = payload.get("cycles")
    if not isinstance(summary, dict):
        raise IntegrityTransferReportError(
            f"cycle-policy artifact summary is invalid: {path}"
        )
    if not isinstance(cycles, list):
        raise IntegrityTransferReportError(
            f"cycle-policy artifact cycles is invalid: {path}"
        )

    kind_counts = {
        "self_cycle": 0,
        "multi_node_cycle": 0,
    }
    signatures: list[str] = []
    for cycle in cycles:
        if not isinstance(cycle, dict):
            raise IntegrityTransferReportError(
                f"cycle-policy artifact cycle entry is invalid: {path}"
            )
        kind = str(cycle.get("kind") or "").strip()
        signature = str(cycle.get("cycle_signature") or "").strip()
        node_ids = cycle.get("node_ids")
        if kind not in kind_counts:
            raise IntegrityTransferReportError(
                f"cycle-policy artifact cycle kind is invalid: {path}"
            )
        if not signature:
            raise IntegrityTransferReportError(
                f"cycle-policy artifact cycle_signature is invalid: {path}"
            )
        if not isinstance(node_ids, list) or not node_ids:
            raise IntegrityTransferReportError(
                f"cycle-policy artifact node_ids is invalid: {path}"
            )
        if any(not isinstance(node_id, str) or not node_id.strip() for node_id in node_ids):
            raise IntegrityTransferReportError(
                f"cycle-policy artifact node_ids contains invalid node ids: {path}"
            )
        if len(node_ids) > 1 and len(set(node_ids)) != len(node_ids):
            raise IntegrityTransferReportError(
                f"cycle-policy artifact node_ids contains duplicates: {path}"
            )
        canonical_node_ids = _canonical_cycle_rotation(node_ids)
        if node_ids != canonical_node_ids:
            raise IntegrityTransferReportError(
                f"cycle-policy artifact node_ids must use canonical cycle rotation: {path}"
            )
        expected_signature = "cycle:" + "->".join(node_ids)
        if signature != expected_signature:
            raise IntegrityTransferReportError(
                f"cycle-policy artifact cycle_signature mismatch: {path}"
            )
        expected_kind = "self_cycle" if len(node_ids) == 1 else "multi_node_cycle"
        if kind != expected_kind:
            raise IntegrityTransferReportError(
                f"cycle-policy artifact cycle kind/cardinality mismatch: {path}"
            )
        signatures.append(signature)
        kind_counts[kind] += 1

    if signatures != sorted(signatures):
        raise IntegrityTransferReportError(
            f"cycle-policy artifact cycles are not sorted by cycle_signature: {path}"
        )
    if len(set(signatures)) != len(signatures):
        raise IntegrityTransferReportError(
            f"cycle-policy artifact cycles contain duplicate signatures: {path}"
        )

    total_cycles = summary.get("total_cycles")
    if not isinstance(total_cycles, int) or total_cycles != len(cycles):
        raise IntegrityTransferReportError(
            f"cycle-policy artifact summary.total_cycles mismatch: {path}"
        )
    for kind, count in kind_counts.items():
        raw_summary_count = summary.get(kind)
        if not isinstance(raw_summary_count, int) or raw_summary_count != count:
            raise IntegrityTransferReportError(
                f"cycle-policy artifact summary.{kind} mismatch: {path}"
            )

    return {
        "source_text_hash": source_text_hash,
        "total_cycles": total_cycles,
        "kind_counts": kind_counts,
    }


def _validate_deontic_conflict_artifact(path: Path) -> dict[str, Any]:
    payload = _read_json_object(path, description=f"deontic-conflict artifact {path}")
    if payload.get("schema") != DEONTIC_CONFLICT_SCHEMA:
        raise IntegrityTransferReportError(
            f"deontic-conflict artifact has invalid schema: {path}"
        )
    source_text_hash = str(payload.get("source_text_hash") or "").strip()
    if not source_text_hash:
        raise IntegrityTransferReportError(
            f"deontic-conflict artifact missing source_text_hash: {path}"
        )
    summary = payload.get("summary")
    conflicts = payload.get("conflicts")
    if not isinstance(summary, dict):
        raise IntegrityTransferReportError(
            f"deontic-conflict artifact summary is invalid: {path}"
        )
    if not isinstance(conflicts, list):
        raise IntegrityTransferReportError(
            f"deontic-conflict artifact conflicts is invalid: {path}"
        )

    order_keys: list[tuple[str, str, str]] = []
    pair_keys: set[tuple[str, str]] = set()
    for conflict in conflicts:
        if not isinstance(conflict, dict):
            raise IntegrityTransferReportError(
                f"deontic-conflict artifact conflict entry is invalid: {path}"
            )
        kind = str(conflict.get("kind") or "").strip()
        primary_id = str(conflict.get("primary_id") or "").strip()
        related_id = conflict.get("related_id")
        if related_id is None:
            related_id = ""
        if not isinstance(related_id, str):
            raise IntegrityTransferReportError(
                f"deontic-conflict artifact related_id is invalid: {path}"
            )
        if kind != "deontic_conflict":
            raise IntegrityTransferReportError(
                f"deontic-conflict artifact kind is invalid: {path}"
            )
        if not primary_id:
            raise IntegrityTransferReportError(
                f"deontic-conflict artifact primary_id is invalid: {path}"
            )
        if related_id and primary_id > related_id:
            raise IntegrityTransferReportError(
                f"deontic-conflict artifact ids do not follow canonical orientation: {path}"
            )
        details = conflict.get("details")
        if details is not None and not isinstance(details, dict):
            raise IntegrityTransferReportError(
                f"deontic-conflict artifact details is invalid: {path}"
            )
        order_keys.append((kind, primary_id, related_id))
        pair_key = (primary_id, related_id)
        if pair_key in pair_keys:
            raise IntegrityTransferReportError(
                f"deontic-conflict artifact contains duplicate conflict pairs: {path}"
            )
        pair_keys.add(pair_key)

    if order_keys != sorted(order_keys):
        raise IntegrityTransferReportError(
            f"deontic-conflict artifact conflicts are not deterministically ordered: {path}"
        )

    total_conflicts = summary.get("total_conflicts")
    deontic_conflict = summary.get("deontic_conflict")
    if not isinstance(total_conflicts, int) or total_conflicts != len(conflicts):
        raise IntegrityTransferReportError(
            f"deontic-conflict artifact summary.total_conflicts mismatch: {path}"
        )
    if not isinstance(deontic_conflict, int) or deontic_conflict != len(conflicts):
        raise IntegrityTransferReportError(
            f"deontic-conflict artifact summary.deontic_conflict mismatch: {path}"
        )

    return {
        "source_text_hash": source_text_hash,
        "total_conflicts": total_conflicts,
    }


def _build_coverage_summary(*, manifest_coverage_entries: list[dict[str, Any]]) -> dict[str, Any]:
    entries = [
        {
            "surface_id": str(entry["surface_id"]),
            "fixture_ids": list(entry["fixture_ids"]),
            "valid": True,
            **({"notes": entry["notes"]} if "notes" in entry else {}),
        }
        for entry in manifest_coverage_entries
    ]
    surface_count = len(_FROZEN_INTEGRITY_SURFACES)
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


def _build_dangling_reference_summary(
    *,
    manifest_path: Path,
    fixtures: list[dict[str, Any]],
) -> dict[str, Any]:
    total_issues = 0
    issue_kind_counts = {
        "missing_node_reference": 0,
        "missing_edge_endpoint": 0,
    }
    run_count = 0
    for fixture in fixtures:
        for run in fixture["runs"]:
            run_count += 1
            artifact_path = _resolve_ref(
                manifest_path=manifest_path,
                raw_ref=str(run["dangling_reference_path"]),
            )
            details = _validate_dangling_reference_artifact(artifact_path)
            total_issues += int(details["total_issues"])
            for key in issue_kind_counts:
                issue_kind_counts[key] += int(details["kind_counts"][key])
    return {
        "valid": True,
        "fixture_count": len(fixtures),
        "run_count": run_count,
        "total_issues": total_issues,
        "issue_kind_counts": issue_kind_counts,
    }


def _build_cycle_policy_summary(
    *,
    manifest_path: Path,
    fixtures: list[dict[str, Any]],
) -> dict[str, Any]:
    total_cycles = 0
    cycle_kind_counts = {
        "self_cycle": 0,
        "multi_node_cycle": 0,
    }
    run_count = 0
    for fixture in fixtures:
        for run in fixture["runs"]:
            run_count += 1
            artifact_path = _resolve_ref(
                manifest_path=manifest_path,
                raw_ref=str(run["cycle_policy_path"]),
            )
            details = _validate_cycle_policy_artifact(artifact_path)
            total_cycles += int(details["total_cycles"])
            for key in cycle_kind_counts:
                cycle_kind_counts[key] += int(details["kind_counts"][key])
    return {
        "valid": True,
        "fixture_count": len(fixtures),
        "run_count": run_count,
        "total_cycles": total_cycles,
        "cycle_kind_counts": cycle_kind_counts,
    }


def _build_deontic_conflict_summary(
    *,
    manifest_path: Path,
    fixtures: list[dict[str, Any]],
) -> dict[str, Any]:
    total_conflicts = 0
    run_count = 0
    for fixture in fixtures:
        for run in fixture["runs"]:
            run_count += 1
            artifact_path = _resolve_ref(
                manifest_path=manifest_path,
                raw_ref=str(run["deontic_conflict_path"]),
            )
            details = _validate_deontic_conflict_artifact(artifact_path)
            total_conflicts += int(details["total_conflicts"])
    return {
        "valid": True,
        "fixture_count": len(fixtures),
        "run_count": run_count,
        "total_conflicts": total_conflicts,
        "conflict_kind_counts": {"deontic_conflict": total_conflicts},
    }


def _build_replay_summary(
    *,
    replay_count: int,
    dangling_reference_fixtures: list[dict[str, Any]],
    cycle_policy_fixtures: list[dict[str, Any]],
    deontic_conflict_fixtures: list[dict[str, Any]],
) -> dict[str, Any]:
    return {
        "valid": True,
        "replay_count": replay_count,
        "fixture_counts": {
            "dangling_reference": len(dangling_reference_fixtures),
            "cycle_policy": len(cycle_policy_fixtures),
            "deontic_conflict": len(deontic_conflict_fixtures),
        },
        "replay_unit_counts": {
            "dangling_reference": sum(
                len(fixture["runs"]) for fixture in dangling_reference_fixtures
            ),
            "cycle_policy": sum(len(fixture["runs"]) for fixture in cycle_policy_fixtures),
            "deontic_conflict": sum(
                len(fixture["runs"]) for fixture in deontic_conflict_fixtures
            ),
        },
    }


def build_integrity_transfer_report_vnext_plus16_payload(
    *,
    vnext_plus16_manifest_path: Path,
) -> dict[str, Any]:
    manifest_payload, manifest_hash = _load_vnext_plus16_manifest_payload(
        vnext_plus16_manifest_path
    )
    dangling_reference_fixtures = manifest_payload["dangling_reference_fixtures"]
    cycle_policy_fixtures = manifest_payload["cycle_policy_fixtures"]
    deontic_conflict_fixtures = manifest_payload["deontic_conflict_fixtures"]
    replay_count = int(manifest_payload["replay_count"])
    return {
        "schema": INTEGRITY_TRANSFER_REPORT_VNEXT_PLUS16_SCHEMA,
        "vnext_plus16_manifest_hash": manifest_hash,
        "coverage_summary": _build_coverage_summary(
            manifest_coverage_entries=manifest_payload["coverage"],
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
        "replay_summary": _build_replay_summary(
            replay_count=replay_count,
            dangling_reference_fixtures=dangling_reference_fixtures,
            cycle_policy_fixtures=cycle_policy_fixtures,
            deontic_conflict_fixtures=deontic_conflict_fixtures,
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
