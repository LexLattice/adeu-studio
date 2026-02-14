from __future__ import annotations

import hashlib
import json
import math
from collections.abc import Mapping, Sequence
from typing import Any

from adeu_ir import SolverEvidence, ValidatorAtomRef

VALIDATOR_EVIDENCE_PACKET_SCHEMA = "validator_evidence_packet@1"

# Nonsemantic fields are intentionally excluded from evidence_packet_hash.
VALIDATOR_EVIDENCE_HASH_EXCLUDED_FIELDS = frozenset(
    {
        "evidence_packet_hash",
        "validator_run_id",
        "materialized_at",
        "observed_at",
        "raw_path",
        "stderr_path",
        "operator_note",
        "operator_message",
    }
)


def _canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def _sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _normalize_model(raw_model: Any) -> dict[str, str]:
    pairs: list[tuple[str, str]] = []
    if isinstance(raw_model, Mapping):
        for key, value in raw_model.items():
            pairs.append((str(key), str(value)))
    elif isinstance(raw_model, list):
        for item in raw_model:
            if not isinstance(item, Mapping):
                continue
            key = item.get("symbol_name", item.get("symbol", item.get("name")))
            value = item.get("value_repr", item.get("value"))
            if key is None or value is None:
                continue
            pairs.append((str(key), str(value)))
    return {key: value for key, value in sorted(pairs)}


def _normalize_unsat_core(raw_unsat_core: Any) -> list[str]:
    if not isinstance(raw_unsat_core, list):
        return []
    return sorted(str(item) for item in raw_unsat_core)


def _normalize_stat_value(value: Any) -> int | bool | str:
    if isinstance(value, bool):
        return value
    if isinstance(value, int):
        return value
    if isinstance(value, str):
        return value
    if isinstance(value, float):
        if math.isnan(value):
            return "nan"
        if math.isinf(value):
            return "inf" if value > 0 else "-inf"
        return format(value, ".17g")
    if isinstance(value, (dict, list, tuple)):
        return _canonical_json(value)
    return str(value)


def _normalize_stats(raw_stats: Any) -> dict[str, int | bool | str]:
    if not isinstance(raw_stats, Mapping):
        return {}
    normalized: dict[str, int | bool | str] = {}
    for raw_key, raw_value in sorted(raw_stats.items(), key=lambda item: str(item[0])):
        key = str(raw_key)
        normalized[key] = _normalize_stat_value(raw_value)
    return normalized


def _normalize_atom_map(
    atom_map: Mapping[str, Any] | Sequence[ValidatorAtomRef] | None,
) -> dict[str, dict[str, str | None]]:
    normalized: dict[str, dict[str, str | None]] = {}
    if atom_map is None:
        return normalized
    if isinstance(atom_map, Mapping):
        for raw_name, ref in sorted(atom_map.items(), key=lambda item: str(item[0])):
            assertion_name = str(raw_name)
            object_id: str | None = None
            json_path: str | None = None
            if isinstance(ref, Mapping):
                raw_object_id = ref.get("object_id")
                raw_json_path = ref.get("json_path")
                object_id = None if raw_object_id is None else str(raw_object_id)
                json_path = None if raw_json_path is None else str(raw_json_path)
            else:
                object_id = (
                    None
                    if getattr(ref, "object_id", None) is None
                    else str(getattr(ref, "object_id"))
                )
                json_path = (
                    None
                    if getattr(ref, "json_path", None) is None
                    else str(getattr(ref, "json_path"))
                )
            normalized[assertion_name] = {
                "object_id": object_id,
                "json_path": json_path,
            }
        return normalized

    for ref in atom_map:
        assertion_name = str(ref.assertion_name)
        normalized[assertion_name] = {
            "object_id": ref.object_id,
            "json_path": ref.json_path,
        }
    return {name: normalized[name] for name in sorted(normalized)}


def _normalize_core_trace_from_raw(raw_core_trace: Any) -> list[dict[str, str | None]]:
    if not isinstance(raw_core_trace, list):
        return []
    normalized: list[dict[str, str | None]] = []
    for item in raw_core_trace:
        if isinstance(item, ValidatorAtomRef):
            assertion_name = str(item.assertion_name)
            object_id = item.object_id
            json_path = item.json_path
        elif isinstance(item, Mapping):
            raw_name = item.get("assertion_name")
            if raw_name is None:
                continue
            assertion_name = str(raw_name)
            raw_object_id = item.get("object_id")
            raw_json_path = item.get("json_path")
            object_id = None if raw_object_id is None else str(raw_object_id)
            json_path = None if raw_json_path is None else str(raw_json_path)
        else:
            continue
        normalized.append(
            {
                "assertion_name": assertion_name,
                "object_id": object_id,
                "json_path": json_path,
            }
        )
    return sorted(normalized, key=lambda item: item["assertion_name"] or "")


def _core_trace_from_unsat_core(
    *,
    unsat_core: list[str],
    atom_map: dict[str, dict[str, str | None]],
) -> list[dict[str, str | None]]:
    trace: list[dict[str, str | None]] = []
    for assertion_name in unsat_core:
        ref = atom_map.get(assertion_name)
        if ref is None:
            continue
        trace.append(
            {
                "assertion_name": assertion_name,
                "object_id": ref.get("object_id"),
                "json_path": ref.get("json_path"),
            }
        )
    return sorted(trace, key=lambda item: item["assertion_name"] or "")


def _normalize_options(raw_options: Mapping[str, Any] | None) -> dict[str, Any]:
    if raw_options is None:
        return {}
    if not isinstance(raw_options, Mapping):
        return {}
    return json.loads(_canonical_json(dict(raw_options)))


def _strip_nonsemantic_fields(value: Any) -> Any:
    if isinstance(value, Mapping):
        normalized: dict[str, Any] = {}
        for raw_key, raw_value in sorted(value.items(), key=lambda item: str(item[0])):
            key = str(raw_key)
            if key in VALIDATOR_EVIDENCE_HASH_EXCLUDED_FIELDS:
                continue
            if key.endswith("_raw"):
                continue
            normalized[key] = _strip_nonsemantic_fields(raw_value)
        return normalized
    if isinstance(value, list):
        return [_strip_nonsemantic_fields(item) for item in value]
    return value


def _evidence_packet_hash(payload: Mapping[str, Any]) -> str:
    hash_basis = _strip_nonsemantic_fields(payload)
    return _sha256_text(_canonical_json(hash_basis))


def build_validator_evidence_packet(
    *,
    validator_run_id: str,
    backend: str,
    backend_version: str | None,
    timeout_ms: int,
    options: Mapping[str, Any] | None,
    request_hash: str,
    formula_hash: str,
    status: str,
    evidence: Mapping[str, Any] | SolverEvidence,
    atom_map: Mapping[str, Any] | Sequence[ValidatorAtomRef] | None,
    assurance: str | None = None,
) -> dict[str, Any]:
    evidence_payload = (
        evidence.model_dump(mode="json", exclude_none=True)
        if isinstance(evidence, SolverEvidence)
        else dict(evidence)
    )
    normalized_atom_map = _normalize_atom_map(atom_map)
    unsat_core = _normalize_unsat_core(evidence_payload.get("unsat_core"))
    raw_core_trace = _normalize_core_trace_from_raw(evidence_payload.get("core_trace"))
    if raw_core_trace:
        core_trace = raw_core_trace
    else:
        core_trace = _core_trace_from_unsat_core(
            unsat_core=unsat_core,
            atom_map=normalized_atom_map,
        )

    normalized_evidence: dict[str, Any] = {
        "model": _normalize_model(evidence_payload.get("model")),
        "unsat_core": unsat_core,
        "core_trace": core_trace,
        "stats": _normalize_stats(evidence_payload.get("stats")),
    }
    error = evidence_payload.get("error")
    if isinstance(error, str) and error:
        normalized_evidence["error"] = error

    packet: dict[str, Any] = {
        "schema": VALIDATOR_EVIDENCE_PACKET_SCHEMA,
        "validator_run_id": str(validator_run_id),
        "backend": str(backend),
        "backend_version": None if backend_version is None else str(backend_version),
        "timeout_ms": int(timeout_ms),
        "options": _normalize_options(options),
        "request_hash": str(request_hash),
        "formula_hash": str(formula_hash),
        "status": str(status),
        "evidence": normalized_evidence,
    }
    if assurance is not None:
        packet["assurance"] = str(assurance)
    packet["evidence_packet_hash"] = _evidence_packet_hash(packet)
    return packet
