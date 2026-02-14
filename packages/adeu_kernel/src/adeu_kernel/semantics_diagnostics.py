from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping, Sequence
from typing import Any

SEMANTICS_DIAGNOSTICS_SCHEMA = "semantics_diagnostics@1"

_VALIDATOR_STATUSES = frozenset(
    {
        "SAT",
        "UNSAT",
        "UNKNOWN",
        "TIMEOUT",
        "INVALID_REQUEST",
        "ERROR",
    }
)
_ASSURANCE_LEVELS = frozenset({"kernel_only", "solver_backed", "proof_checked"})
_HEX_CHARS = frozenset("0123456789abcdef")


def _canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def _sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _normalize_sha256_hash(value: Any) -> str:
    normalized = str(value).strip().lower()
    if len(normalized) == 64 and all(ch in _HEX_CHARS for ch in normalized):
        return normalized
    return _sha256_text(normalized)


def _derive_assurance(*, status: str, assurance: str | None) -> str:
    if assurance in _ASSURANCE_LEVELS:
        return assurance
    if status in {"SAT", "UNSAT", "UNKNOWN", "TIMEOUT"}:
        return "solver_backed"
    return "kernel_only"


def _normalize_witness_refs(raw_core_trace: Any) -> list[dict[str, str | None]]:
    if not isinstance(raw_core_trace, list):
        return []

    normalized: list[dict[str, str | None]] = []
    for item in raw_core_trace:
        if not isinstance(item, Mapping):
            continue
        raw_assertion_name = item.get("assertion_name")
        if raw_assertion_name is None:
            continue
        raw_object_id = item.get("object_id")
        raw_json_path = item.get("json_path")
        normalized.append(
            {
                "assertion_name": str(raw_assertion_name),
                "object_id": None if raw_object_id is None else str(raw_object_id),
                "json_path": None if raw_json_path is None else str(raw_json_path),
            }
        )

    return sorted(
        normalized,
        key=lambda item: (
            item.get("assertion_name") or "",
            item.get("object_id") or "",
            item.get("json_path") or "",
        ),
    )


def _normalized_record_from_packet(packet: Mapping[str, Any]) -> dict[str, Any] | None:
    raw_run_id = packet.get("validator_run_id")
    validator_run_id = "" if raw_run_id is None else str(raw_run_id).strip()
    if not validator_run_id:
        return None

    raw_status = str(packet.get("status", "")).strip().upper()
    status = raw_status if raw_status in _VALIDATOR_STATUSES else "ERROR"
    raw_assurance = packet.get("assurance")
    assurance = _derive_assurance(
        status=status,
        assurance=str(raw_assurance) if isinstance(raw_assurance, str) else None,
    )

    evidence_payload = packet.get("evidence")
    core_trace = (
        evidence_payload.get("core_trace")
        if isinstance(evidence_payload, Mapping)
        else None
    )
    witness_refs = _normalize_witness_refs(core_trace)

    return {
        "kind": "validator_run",
        "validator_run_id": validator_run_id,
        "formula_hash": _normalize_sha256_hash(packet.get("formula_hash", "")),
        "request_hash": _normalize_sha256_hash(packet.get("request_hash", "")),
        "status": status,
        "assurance": assurance,
        "validator_evidence_packet_ref": f"validator_evidence_packet:{validator_run_id}",
        "validator_evidence_packet_hash": _normalize_sha256_hash(
            packet.get("evidence_packet_hash", "")
        ),
        "witness_refs": witness_refs,
    }


def build_semantics_diagnostics(
    *,
    artifact_ref: str,
    validator_evidence_packets: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    records: list[dict[str, Any]] = []
    for packet in validator_evidence_packets:
        normalized = _normalized_record_from_packet(packet)
        if normalized is not None:
            records.append(normalized)

    records = sorted(
        records,
        key=lambda item: (
            str(item.get("kind", "")),
            str(item.get("formula_hash", "")),
            str(item.get("request_hash", "")),
            str(item.get("validator_run_id", "")),
        ),
    )

    payload: dict[str, Any] = {
        "schema": SEMANTICS_DIAGNOSTICS_SCHEMA,
        "artifact_ref": str(artifact_ref),
        "records": records,
    }
    payload["semantics_diagnostics_hash"] = _sha256_text(_canonical_json(payload))
    return payload
