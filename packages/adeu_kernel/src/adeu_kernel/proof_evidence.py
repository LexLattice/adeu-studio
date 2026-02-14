from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping, Sequence
from typing import Any

from adeu_ir import ProofInput

PROOF_EVIDENCE_SCHEMA = "proof_evidence@1"

# Nonsemantic fields are intentionally excluded from proof_evidence_hash.
PROOF_EVIDENCE_HASH_EXCLUDED_FIELDS = frozenset(
    {
        "proof_evidence_hash",
        "proof_id",
        "artifact_ref",
        "created_at",
        "materialized_at",
        "observed_at",
        "raw_path",
        "stderr_path",
        "operator_note",
        "operator_message",
    }
)

PROOF_EVIDENCE_HASH_EXCLUDED_FIELD_LIST = tuple(sorted(PROOF_EVIDENCE_HASH_EXCLUDED_FIELDS))


def _canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def _sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _normalize_input_item(item: ProofInput | Mapping[str, Any]) -> dict[str, str | None]:
    if isinstance(item, ProofInput):
        object_id = item.object_id
        json_path = item.json_path
        formula_hash = item.formula_hash
    else:
        raw_object_id = item.get("object_id")
        raw_json_path = item.get("json_path")
        raw_formula_hash = item.get("formula_hash")
        object_id = None if raw_object_id is None else str(raw_object_id)
        json_path = None if raw_json_path is None else str(raw_json_path)
        formula_hash = None if raw_formula_hash is None else str(raw_formula_hash)
    return {
        "object_id": object_id,
        "json_path": json_path,
        "formula_hash": formula_hash,
    }


def _normalize_inputs(
    raw_inputs: Sequence[ProofInput] | Sequence[Mapping[str, Any]],
) -> list[dict[str, str | None]]:
    normalized = [_normalize_input_item(item) for item in raw_inputs]
    return sorted(
        normalized,
        key=lambda item: (
            item["object_id"] or "",
            item["json_path"] or "",
            item["formula_hash"] or "",
        ),
    )


def _normalize_details(raw_details: Mapping[str, Any] | None) -> dict[str, Any]:
    if raw_details is None:
        return {}
    return json.loads(_canonical_json(dict(raw_details)))


def _normalize_failed_reason(*, status: str, details: Mapping[str, Any]) -> str | None:
    if status != "failed":
        return None
    error_code = details.get("error_code")
    if isinstance(error_code, str) and error_code:
        return error_code
    error_text = details.get("error")
    if isinstance(error_text, str):
        lowered = error_text.strip().lower()
        if "timeout" in lowered or "timed out" in lowered:
            return "timeout"
        if "cancel" in lowered:
            return "canceled"
    return "backend_error"


def strip_nonsemantic_proof_fields(value: Any) -> Any:
    if isinstance(value, Mapping):
        normalized: dict[str, Any] = {}
        for raw_key, raw_value in sorted(value.items(), key=lambda item: str(item[0])):
            key = str(raw_key)
            if key in PROOF_EVIDENCE_HASH_EXCLUDED_FIELDS:
                continue
            if key.endswith("_raw"):
                continue
            normalized[key] = strip_nonsemantic_proof_fields(raw_value)
        return normalized
    if isinstance(value, list):
        return [strip_nonsemantic_proof_fields(item) for item in value]
    return value


def proof_evidence_hash(payload: Mapping[str, Any]) -> str:
    return _sha256_text(_canonical_json(strip_nonsemantic_proof_fields(payload)))


def build_proof_evidence_packet(
    *,
    proof_id: str,
    artifact_id: str,
    created_at: str | None,
    backend: str,
    theorem_id: str,
    status: str,
    proof_hash: str,
    inputs: Sequence[ProofInput] | Sequence[Mapping[str, Any]],
    details: Mapping[str, Any] | None,
) -> dict[str, Any]:
    normalized_details = _normalize_details(details)
    packet: dict[str, Any] = {
        "schema": PROOF_EVIDENCE_SCHEMA,
        "proof_id": str(proof_id),
        "artifact_id": str(artifact_id),
        "artifact_ref": f"proof:{proof_id}",
        "backend": str(backend),
        "theorem_id": str(theorem_id),
        "status": str(status),
        "proof_hash": str(proof_hash),
        "inputs": _normalize_inputs(inputs),
        "details": normalized_details,
        "hash_excluded_fields": list(PROOF_EVIDENCE_HASH_EXCLUDED_FIELD_LIST),
    }
    if created_at is not None:
        packet["created_at"] = str(created_at)
    failed_reason = _normalize_failed_reason(status=str(status), details=normalized_details)
    if failed_reason is not None:
        packet["failed"] = {"reason": failed_reason}
    packet["proof_evidence_hash"] = proof_evidence_hash(packet)
    return packet
