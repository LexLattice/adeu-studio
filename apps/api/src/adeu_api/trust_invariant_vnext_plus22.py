from __future__ import annotations

import json
from collections import Counter
from collections.abc import Iterator, Mapping
from contextlib import contextmanager
from contextvars import ContextVar
from functools import lru_cache
from pathlib import Path
from typing import Any, Literal

from adeu_core_ir import AdeuNormativeAdvicePacket, AdeuTrustInvariantPacket
from pydantic import BaseModel, ConfigDict, Field, model_validator

from .cross_ir_bridge_vnext_plus20 import (
    CrossIRBridgeVnextPlus20Error,
    build_cross_ir_bridge_manifest_vnext_plus20,
    canonical_bridge_manifest_hash_vnext_plus20,
)
from .cross_ir_coherence_vnext_plus20 import AdeuCrossIRCoherenceDiagnostics
from .hashing import canonical_json, sha256_text

VNEXT_PLUS20_STOP_GATE_MANIFEST_SCHEMA = "stop_gate.vnext_plus20_manifest@1"
VNEXT_PLUS21_STOP_GATE_MANIFEST_SCHEMA = "stop_gate.vnext_plus21_manifest@1"
VNEXT_PLUS20_STOP_GATE_MANIFEST_PATH = (
    Path(__file__).resolve().parents[2] / "fixtures" / "stop_gate" / "vnext_plus20_manifest.json"
)
VNEXT_PLUS21_STOP_GATE_MANIFEST_PATH = (
    Path(__file__).resolve().parents[2] / "fixtures" / "stop_gate" / "vnext_plus21_manifest.json"
)
TRUST_INVARIANT_PACKET_SCHEMA = "adeu_trust_invariant_packet@0.1"
_COHERENCE_SURFACE_ID = "adeu.cross_ir.coherence_diagnostics"
_NORMATIVE_ADVICE_PACKET_SURFACE_ID = "adeu.normative_advice.packet"
_TRUST_INVARIANT_NON_ENFORCEMENT_CONTEXT: ContextVar[bool] = ContextVar(
    "trust_invariant_non_enforcement_context",
    default=False,
)


class TrustInvariantVnextPlus22Error(ValueError):
    def __init__(self, *, code: str, reason: str, context: Mapping[str, Any] | None = None) -> None:
        super().__init__(reason)
        self.code = code
        self.reason = reason
        self.context = dict(context or {})


class _CrossIRCoherenceRun(BaseModel):
    model_config = ConfigDict(extra="ignore")

    cross_ir_coherence_diagnostics_path: str = Field(min_length=1)


class _CrossIRCoherenceFixture(BaseModel):
    model_config = ConfigDict(extra="ignore")

    source_text_hash: str = Field(min_length=1)
    core_ir_artifact_id: str = Field(min_length=1)
    concept_artifact_id: str = Field(min_length=1)
    fixture_id: str = Field(min_length=1)
    surface_id: Literal["adeu.cross_ir.coherence_diagnostics"] = _COHERENCE_SURFACE_ID
    runs: list[_CrossIRCoherenceRun] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "_CrossIRCoherenceFixture":
        if not self.runs:
            raise ValueError("coherence fixture must include at least one run")
        run_paths = [run.cross_ir_coherence_diagnostics_path for run in self.runs]
        if len(set(run_paths)) != len(run_paths):
            raise ValueError("coherence fixture run paths must be unique")
        return self


class _VnextPlus20StopGateManifest(BaseModel):
    model_config = ConfigDict(extra="ignore")

    schema: Literal["stop_gate.vnext_plus20_manifest@1"] = VNEXT_PLUS20_STOP_GATE_MANIFEST_SCHEMA
    cross_ir_coherence_diagnostics_fixtures: list[_CrossIRCoherenceFixture] = Field(
        default_factory=list
    )


class _NormativeAdvicePacketRun(BaseModel):
    model_config = ConfigDict(extra="ignore")

    normative_advice_packet_path: str = Field(min_length=1)


class _NormativeAdvicePacketFixture(BaseModel):
    model_config = ConfigDict(extra="ignore")

    source_text_hash: str = Field(min_length=1)
    core_ir_artifact_id: str = Field(min_length=1)
    concept_artifact_id: str = Field(min_length=1)
    fixture_id: str = Field(min_length=1)
    surface_id: Literal["adeu.normative_advice.packet"] = _NORMATIVE_ADVICE_PACKET_SURFACE_ID
    runs: list[_NormativeAdvicePacketRun] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "_NormativeAdvicePacketFixture":
        if not self.runs:
            raise ValueError("normative-advice packet fixture must include at least one run")
        run_paths = [run.normative_advice_packet_path for run in self.runs]
        if len(set(run_paths)) != len(run_paths):
            raise ValueError("normative-advice packet fixture run paths must be unique")
        return self


class _VnextPlus21StopGateManifest(BaseModel):
    model_config = ConfigDict(extra="ignore")

    schema: Literal["stop_gate.vnext_plus21_manifest@1"] = VNEXT_PLUS21_STOP_GATE_MANIFEST_SCHEMA
    normative_advice_packet_fixtures: list[_NormativeAdvicePacketFixture] = Field(
        default_factory=list
    )


def _trust_invariant_error(
    *,
    code: str,
    reason: str,
    context: Mapping[str, Any] | None = None,
) -> TrustInvariantVnextPlus22Error:
    return TrustInvariantVnextPlus22Error(code=code, reason=reason, context=context)


@contextmanager
def trust_invariant_non_enforcement_context() -> Iterator[None]:
    token = _TRUST_INVARIANT_NON_ENFORCEMENT_CONTEXT.set(True)
    try:
        yield
    finally:
        _TRUST_INVARIANT_NON_ENFORCEMENT_CONTEXT.reset(token)


def _require_trust_invariant_non_enforcement_context(*, operation: str) -> None:
    if _TRUST_INVARIANT_NON_ENFORCEMENT_CONTEXT.get():
        return
    raise _trust_invariant_error(
        code="URM_ADEU_TRUST_INVARIANT_REQUEST_INVALID",
        reason="trust-invariant runtime non-enforcement context is not active",
        context={"operation": operation},
    )


def _resolved_manifest_path(path: Path | None, *, default: Path) -> Path:
    selected = default if path is None else Path(path)
    return selected.resolve()


def _cross_ir_error_to_trust(
    exc: CrossIRBridgeVnextPlus20Error,
) -> TrustInvariantVnextPlus22Error:
    mapped_code = {
        "URM_ADEU_CROSS_IR_REQUEST_INVALID": "URM_ADEU_TRUST_INVARIANT_REQUEST_INVALID",
        "URM_ADEU_CROSS_IR_ARTIFACT_NOT_FOUND": "URM_ADEU_TRUST_INVARIANT_ARTIFACT_NOT_FOUND",
        "URM_ADEU_CROSS_IR_PAYLOAD_INVALID": "URM_ADEU_TRUST_INVARIANT_PAYLOAD_INVALID",
        "URM_ADEU_CROSS_IR_FIXTURE_INVALID": "URM_ADEU_TRUST_INVARIANT_FIXTURE_INVALID",
    }.get(exc.code, "URM_ADEU_TRUST_INVARIANT_PAYLOAD_INVALID")
    return _trust_invariant_error(
        code=mapped_code,
        reason=exc.reason,
        context=exc.context,
    )


def _strip_created_at_recursive(value: Any) -> Any:
    if isinstance(value, Mapping):
        normalized: dict[str, Any] = {}
        for key in sorted(str(item) for item in value.keys()):
            if key == "created_at":
                continue
            normalized[key] = _strip_created_at_recursive(value[key])
        return normalized
    if isinstance(value, list):
        return [_strip_created_at_recursive(item) for item in value]
    return value


def _sha256_created_at_stripped(payload: Any) -> str:
    return sha256_text(canonical_json(_strip_created_at_recursive(payload)))


def _proof_id(
    *,
    invariant_code: str,
    status: str,
    justification_refs: list[str],
    expected_hash: str | None = None,
    observed_hash: str | None = None,
) -> str:
    payload: dict[str, Any] = {
        "invariant_code": invariant_code,
        "status": status,
        "justification_refs": justification_refs,
    }
    if expected_hash is not None:
        payload["expected_hash"] = expected_hash
    if observed_hash is not None:
        payload["observed_hash"] = observed_hash
    return sha256_text(canonical_json(payload))[:16]


def _proof_sort_key(item: Mapping[str, Any]) -> tuple[str, str]:
    return (str(item.get("invariant_code") or ""), str(item.get("proof_id") or ""))


def _artifact_ref(
    *,
    schema: str,
    source_text_hash: str,
    core_ir_artifact_id: str,
    concept_artifact_id: str,
) -> str:
    return (
        "artifact:"
        f"{schema}:{source_text_hash}:{core_ir_artifact_id}:{concept_artifact_id}"
    )


@lru_cache(maxsize=8)
def _coherence_fixture_index_for_manifest(
    manifest_path_value: str,
) -> dict[tuple[str, str, str], tuple[Path, ...]]:
    manifest_path = Path(manifest_path_value)
    try:
        raw_payload = manifest_path.read_text(encoding="utf-8")
    except FileNotFoundError as exc:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_FIXTURE_INVALID",
            reason="vnext+20 stop-gate manifest fixture is missing",
            context={"path": str(manifest_path)},
        ) from exc
    except OSError as exc:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_FIXTURE_INVALID",
            reason="vnext+20 stop-gate manifest fixture is unreadable",
            context={"path": str(manifest_path), "error": str(exc)},
        ) from exc

    try:
        parsed = json.loads(raw_payload)
    except json.JSONDecodeError as exc:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_FIXTURE_INVALID",
            reason="vnext+20 stop-gate manifest JSON is invalid",
            context={"path": str(manifest_path), "error": exc.msg},
        ) from exc

    try:
        manifest = _VnextPlus20StopGateManifest.model_validate(parsed)
    except Exception as exc:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_FIXTURE_INVALID",
            reason="vnext+20 stop-gate manifest payload failed schema validation",
            context={"path": str(manifest_path), "error": str(exc)},
        ) from exc

    by_identity: dict[tuple[str, str, str], tuple[Path, ...]] = {}
    for fixture in manifest.cross_ir_coherence_diagnostics_fixtures:
        identity = (
            fixture.source_text_hash,
            fixture.core_ir_artifact_id,
            fixture.concept_artifact_id,
        )
        if identity in by_identity:
            raise _trust_invariant_error(
                code="URM_ADEU_TRUST_INVARIANT_REQUEST_INVALID",
                reason="coherence fixture set contains duplicate pair identity",
                context={
                    "source_text_hash": fixture.source_text_hash,
                    "core_ir_artifact_id": fixture.core_ir_artifact_id,
                    "concept_artifact_id": fixture.concept_artifact_id,
                },
            )
        resolved_run_paths: list[Path] = []
        for run_path in sorted(run.cross_ir_coherence_diagnostics_path for run in fixture.runs):
            selected_path = Path(run_path)
            if not selected_path.is_absolute():
                selected_path = manifest_path.parent / selected_path
            resolved_run_paths.append(selected_path.resolve())
        by_identity[identity] = tuple(resolved_run_paths)
    return by_identity


@lru_cache(maxsize=8)
def _normative_advice_fixture_index_for_manifest(
    manifest_path_value: str,
) -> dict[tuple[str, str, str], tuple[tuple[str, tuple[Path, ...]], ...]]:
    manifest_path = Path(manifest_path_value)
    try:
        raw_payload = manifest_path.read_text(encoding="utf-8")
    except FileNotFoundError as exc:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_FIXTURE_INVALID",
            reason="vnext+21 stop-gate manifest fixture is missing",
            context={"path": str(manifest_path)},
        ) from exc
    except OSError as exc:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_FIXTURE_INVALID",
            reason="vnext+21 stop-gate manifest fixture is unreadable",
            context={"path": str(manifest_path), "error": str(exc)},
        ) from exc

    try:
        parsed = json.loads(raw_payload)
    except json.JSONDecodeError as exc:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_FIXTURE_INVALID",
            reason="vnext+21 stop-gate manifest JSON is invalid",
            context={"path": str(manifest_path), "error": exc.msg},
        ) from exc

    try:
        manifest = _VnextPlus21StopGateManifest.model_validate(parsed)
    except Exception as exc:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_FIXTURE_INVALID",
            reason="vnext+21 stop-gate manifest payload failed schema validation",
            context={"path": str(manifest_path), "error": str(exc)},
        ) from exc

    by_identity: dict[tuple[str, str, str], list[tuple[str, tuple[Path, ...]]]] = {}
    for fixture in manifest.normative_advice_packet_fixtures:
        identity = (
            fixture.source_text_hash,
            fixture.core_ir_artifact_id,
            fixture.concept_artifact_id,
        )
        resolved_run_paths: list[Path] = []
        for run_path in sorted(run.normative_advice_packet_path for run in fixture.runs):
            selected_path = Path(run_path)
            if not selected_path.is_absolute():
                selected_path = manifest_path.parent / selected_path
            resolved_run_paths.append(selected_path.resolve())
        by_identity.setdefault(identity, []).append((fixture.fixture_id, tuple(resolved_run_paths)))

    final_index: dict[tuple[str, str, str], tuple[tuple[str, tuple[Path, ...]], ...]] = {}
    for identity, fixture_runs in by_identity.items():
        fixture_runs = sorted(fixture_runs, key=lambda item: item[0])
        fixture_ids = [fixture_id for fixture_id, _ in fixture_runs]
        if len(set(fixture_ids)) != len(fixture_ids):
            raise _trust_invariant_error(
                code="URM_ADEU_TRUST_INVARIANT_FIXTURE_INVALID",
                reason=(
                    "normative-advice fixture set contains duplicate fixture_id "
                    "for pair identity"
                ),
                context={
                    "source_text_hash": identity[0],
                    "core_ir_artifact_id": identity[1],
                    "concept_artifact_id": identity[2],
                },
            )
        final_index[identity] = tuple(fixture_runs)
    return final_index


def _validate_pair_payload_identity(
    *,
    payload: Mapping[str, Any],
    source_text_hash: str,
    core_ir_artifact_id: str,
    concept_artifact_id: str,
    payload_name: str,
) -> None:
    if payload.get("source_text_hash") != source_text_hash:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_PAYLOAD_INVALID",
            reason=f"{payload_name} source_text_hash does not match pair identity",
            context={
                "source_text_hash": source_text_hash,
                "payload_source_text_hash": payload.get("source_text_hash"),
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
            },
        )
    if payload.get("core_ir_artifact_id") != core_ir_artifact_id:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_PAYLOAD_INVALID",
            reason=f"{payload_name} core_ir_artifact_id does not match pair identity",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "payload_core_ir_artifact_id": payload.get("core_ir_artifact_id"),
                "concept_artifact_id": concept_artifact_id,
            },
        )
    if payload.get("concept_artifact_id") != concept_artifact_id:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_PAYLOAD_INVALID",
            reason=f"{payload_name} concept_artifact_id does not match pair identity",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "payload_concept_artifact_id": payload.get("concept_artifact_id"),
            },
        )


def _load_and_validate_coherence_payload(
    *,
    path: Path,
    source_text_hash: str,
    core_ir_artifact_id: str,
    concept_artifact_id: str,
) -> dict[str, Any]:
    try:
        raw_payload = path.read_text(encoding="utf-8")
    except FileNotFoundError as exc:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_ARTIFACT_NOT_FOUND",
            reason="matched coherence diagnostics artifact fixture is missing",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
            },
        ) from exc
    except OSError as exc:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_FIXTURE_INVALID",
            reason="matched coherence diagnostics artifact fixture is unreadable",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
                "error": str(exc),
            },
        ) from exc

    try:
        parsed = json.loads(raw_payload)
    except json.JSONDecodeError as exc:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_PAYLOAD_INVALID",
            reason="matched coherence diagnostics artifact JSON is invalid",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
                "error": exc.msg,
            },
        ) from exc
    if not isinstance(parsed, dict) or not parsed:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_PAYLOAD_INVALID",
            reason="matched coherence diagnostics artifact payload must be a non-empty object",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
            },
        )

    try:
        normalized = AdeuCrossIRCoherenceDiagnostics.model_validate(parsed)
    except Exception as exc:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_PAYLOAD_INVALID",
            reason="matched coherence diagnostics payload failed schema validation",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
                "error": str(exc),
            },
        ) from exc

    payload = normalized.model_dump(mode="json", by_alias=True, exclude_none=True)
    _validate_pair_payload_identity(
        payload=payload,
        source_text_hash=source_text_hash,
        core_ir_artifact_id=core_ir_artifact_id,
        concept_artifact_id=concept_artifact_id,
        payload_name="coherence payload",
    )
    return payload


def _load_and_validate_normative_advice_payload(
    *,
    path: Path,
    source_text_hash: str,
    core_ir_artifact_id: str,
    concept_artifact_id: str,
) -> dict[str, Any]:
    try:
        raw_payload = path.read_text(encoding="utf-8")
    except FileNotFoundError as exc:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_ARTIFACT_NOT_FOUND",
            reason="matched normative-advice packet artifact fixture is missing",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
            },
        ) from exc
    except OSError as exc:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_FIXTURE_INVALID",
            reason="matched normative-advice packet artifact fixture is unreadable",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
                "error": str(exc),
            },
        ) from exc

    try:
        parsed = json.loads(raw_payload)
    except json.JSONDecodeError as exc:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_PAYLOAD_INVALID",
            reason="matched normative-advice packet artifact JSON is invalid",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
                "error": exc.msg,
            },
        ) from exc
    if not isinstance(parsed, dict) or not parsed:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_PAYLOAD_INVALID",
            reason="matched normative-advice packet artifact payload must be a non-empty object",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
            },
        )

    try:
        normalized = AdeuNormativeAdvicePacket.model_validate(parsed)
    except Exception as exc:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_PAYLOAD_INVALID",
            reason="matched normative-advice packet payload failed schema validation",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
                "error": str(exc),
            },
        ) from exc

    payload = normalized.model_dump(mode="json", by_alias=True, exclude_none=True)
    _validate_pair_payload_identity(
        payload=payload,
        source_text_hash=source_text_hash,
        core_ir_artifact_id=core_ir_artifact_id,
        concept_artifact_id=concept_artifact_id,
        payload_name="normative-advice payload",
    )
    return payload


def _coherence_payload_for_pair(
    *,
    source_text_hash: str,
    core_ir_artifact_id: str,
    concept_artifact_id: str,
    coherence_manifest_path: Path | None = None,
) -> dict[str, Any]:
    manifest_path = _resolved_manifest_path(
        coherence_manifest_path, default=VNEXT_PLUS20_STOP_GATE_MANIFEST_PATH
    )
    identity = (source_text_hash, core_ir_artifact_id, concept_artifact_id)
    by_identity = _coherence_fixture_index_for_manifest(str(manifest_path))
    coherence_paths = by_identity.get(identity)
    if coherence_paths is None:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_ARTIFACT_NOT_FOUND",
            reason="matched coherence diagnostics artifact not found for pair identity",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "manifest_path": str(manifest_path),
            },
        )

    payload_by_path: dict[str, dict[str, Any]] = {}
    hash_by_path: dict[str, str] = {}
    for coherence_path in coherence_paths:
        payload = _load_and_validate_coherence_payload(
            path=coherence_path,
            source_text_hash=source_text_hash,
            core_ir_artifact_id=core_ir_artifact_id,
            concept_artifact_id=concept_artifact_id,
        )
        path_key = str(coherence_path)
        payload_by_path[path_key] = payload
        hash_by_path[path_key] = _sha256_created_at_stripped(payload)

    if len(set(hash_by_path.values())) > 1:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_DIAGNOSTIC_DRIFT",
            reason="coherence replay run payloads drift for pair identity",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "coherence_run_hashes_by_path": hash_by_path,
            },
        )

    selected_path = min(payload_by_path.keys())
    return payload_by_path[selected_path]


def _normative_advice_payload_for_pair(
    *,
    source_text_hash: str,
    core_ir_artifact_id: str,
    concept_artifact_id: str,
    normative_advice_manifest_path: Path | None = None,
) -> dict[str, Any]:
    manifest_path = _resolved_manifest_path(
        normative_advice_manifest_path, default=VNEXT_PLUS21_STOP_GATE_MANIFEST_PATH
    )
    identity = (source_text_hash, core_ir_artifact_id, concept_artifact_id)
    by_identity = _normative_advice_fixture_index_for_manifest(str(manifest_path))
    fixture_runs = by_identity.get(identity)
    if fixture_runs is None:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_ARTIFACT_NOT_FOUND",
            reason="matched normative-advice packet artifact not found for pair identity",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "manifest_path": str(manifest_path),
            },
        )
    selected_fixture_id, selected_run_paths = fixture_runs[0]

    payload_by_path: dict[str, dict[str, Any]] = {}
    hash_by_path: dict[str, str] = {}
    for packet_path in selected_run_paths:
        payload = _load_and_validate_normative_advice_payload(
            path=packet_path,
            source_text_hash=source_text_hash,
            core_ir_artifact_id=core_ir_artifact_id,
            concept_artifact_id=concept_artifact_id,
        )
        path_key = str(packet_path)
        payload_by_path[path_key] = payload
        hash_by_path[path_key] = _sha256_created_at_stripped(payload)

    if len(set(hash_by_path.values())) > 1:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_DIAGNOSTIC_DRIFT",
            reason="normative-advice replay run payloads drift for pair identity",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "selected_fixture_id": selected_fixture_id,
                "normative_advice_run_hashes_by_path": hash_by_path,
            },
        )

    selected_path = min(payload_by_path.keys())
    return payload_by_path[selected_path]


def _require_payload_keys(
    *,
    payload: Mapping[str, Any],
    required_keys: tuple[str, ...],
    code: str,
    reason: str,
    context: Mapping[str, Any],
) -> None:
    missing = [key for key in required_keys if key not in payload]
    if missing:
        raise _trust_invariant_error(
            code=code,
            reason=reason,
            context={**context, "missing_keys": missing},
        )


def _build_proof_item(
    *,
    invariant_code: str,
    status: str,
    justification_refs: list[str],
    message: str,
    expected_hash: str | None = None,
    observed_hash: str | None = None,
) -> dict[str, Any]:
    refs = sorted(justification_refs)
    item: dict[str, Any] = {
        "proof_id": _proof_id(
            invariant_code=invariant_code,
            status=status,
            justification_refs=refs,
            expected_hash=expected_hash,
            observed_hash=observed_hash,
        ),
        "invariant_code": invariant_code,
        "status": status,
        "justification_refs": refs,
        "message": message,
    }
    if expected_hash is not None:
        item["expected_hash"] = expected_hash
    if observed_hash is not None:
        item["observed_hash"] = observed_hash
    return item


def _counts_by_status(items: list[dict[str, Any]]) -> dict[str, int]:
    counts = Counter(str(item["status"]) for item in items)
    return {status: counts[status] for status in sorted(counts)}


def _counts_by_invariant_code(items: list[dict[str, Any]]) -> dict[str, int]:
    counts = Counter(str(item["invariant_code"]) for item in items)
    return {code: counts[code] for code in sorted(counts)}


def build_trust_invariant_packet_vnext_plus22(
    *,
    source_text_hash: str,
    core_ir_artifact_id: str,
    concept_artifact_id: str,
    catalog_path: Path | None = None,
    coherence_manifest_path: Path | None = None,
    normative_advice_manifest_path: Path | None = None,
) -> dict[str, Any]:
    _require_trust_invariant_non_enforcement_context(
        operation="build_trust_invariant_packet_vnext_plus22"
    )
    try:
        bridge_manifest = build_cross_ir_bridge_manifest_vnext_plus20(
            source_text_hash=source_text_hash,
            core_ir_artifact_id=core_ir_artifact_id,
            concept_artifact_id=concept_artifact_id,
            catalog_path=catalog_path,
        )
    except CrossIRBridgeVnextPlus20Error as exc:
        raise _cross_ir_error_to_trust(exc) from exc

    bridge_manifest_hash = canonical_bridge_manifest_hash_vnext_plus20(bridge_manifest)
    coherence_payload = _coherence_payload_for_pair(
        source_text_hash=source_text_hash,
        core_ir_artifact_id=core_ir_artifact_id,
        concept_artifact_id=concept_artifact_id,
        coherence_manifest_path=coherence_manifest_path,
    )
    normative_payload = _normative_advice_payload_for_pair(
        source_text_hash=source_text_hash,
        core_ir_artifact_id=core_ir_artifact_id,
        concept_artifact_id=concept_artifact_id,
        normative_advice_manifest_path=normative_advice_manifest_path,
    )

    _require_payload_keys(
        payload=coherence_payload,
        required_keys=(
            "schema",
            "source_text_hash",
            "core_ir_artifact_id",
            "concept_artifact_id",
            "bridge_manifest_hash",
            "issue_summary",
            "issues",
        ),
        code="URM_ADEU_TRUST_INVARIANT_PAYLOAD_INVALID",
        reason="coherence payload missing required top-level fields",
        context={
            "source_text_hash": source_text_hash,
            "core_ir_artifact_id": core_ir_artifact_id,
            "concept_artifact_id": concept_artifact_id,
        },
    )
    _require_payload_keys(
        payload=normative_payload,
        required_keys=(
            "schema",
            "source_text_hash",
            "core_ir_artifact_id",
            "concept_artifact_id",
            "bridge_manifest_hash",
            "advice_summary",
            "advice_items",
        ),
        code="URM_ADEU_TRUST_INVARIANT_PAYLOAD_INVALID",
        reason="normative-advice payload missing required top-level fields",
        context={
            "source_text_hash": source_text_hash,
            "core_ir_artifact_id": core_ir_artifact_id,
            "concept_artifact_id": concept_artifact_id,
        },
    )

    normative_advice_packet_hash = _sha256_created_at_stripped(normative_payload)

    coherence_ref = _artifact_ref(
        schema="adeu_cross_ir_coherence_diagnostics@0.1",
        source_text_hash=source_text_hash,
        core_ir_artifact_id=core_ir_artifact_id,
        concept_artifact_id=concept_artifact_id,
    )
    normative_ref = _artifact_ref(
        schema="adeu_normative_advice_packet@0.1",
        source_text_hash=source_text_hash,
        core_ir_artifact_id=core_ir_artifact_id,
        concept_artifact_id=concept_artifact_id,
    )
    trust_ref = _artifact_ref(
        schema="adeu_trust_invariant_packet@0.1",
        source_text_hash=source_text_hash,
        core_ir_artifact_id=core_ir_artifact_id,
        concept_artifact_id=concept_artifact_id,
    )

    proof_items: list[dict[str, Any]] = []

    proof_items.append(
        _build_proof_item(
            invariant_code="CANONICAL_JSON_CONFORMANCE",
            status="pass",
            justification_refs=[coherence_ref, normative_ref],
            message=(
                "canonical-json conformance checks passed for coherence and normative-advice "
                "payloads"
            ),
        )
    )

    recomputed_normative_advice_hash = _sha256_created_at_stripped(normative_payload)
    recomputed_bridge_manifest_hash = canonical_bridge_manifest_hash_vnext_plus20(bridge_manifest)
    emitted_normative_advice_hash = normative_advice_packet_hash
    emitted_bridge_manifest_hash = bridge_manifest_hash

    hash_recompute_ok = (
        recomputed_normative_advice_hash == emitted_normative_advice_hash
        and recomputed_bridge_manifest_hash == emitted_bridge_manifest_hash
    )
    if recomputed_normative_advice_hash != emitted_normative_advice_hash:
        selected_target = "normative_advice_packet_hash"
        expected_hash = recomputed_normative_advice_hash
        observed_hash = emitted_normative_advice_hash
    elif recomputed_bridge_manifest_hash != emitted_bridge_manifest_hash:
        selected_target = "bridge_manifest_hash"
        expected_hash = recomputed_bridge_manifest_hash
        observed_hash = emitted_bridge_manifest_hash
    else:
        selected_target = "normative_advice_packet_hash"
        expected_hash = recomputed_normative_advice_hash
        observed_hash = emitted_normative_advice_hash
    hash_recompute_message = (
        "hash recompute checks passed"
        if hash_recompute_ok
        else f"hash recompute mismatch detected for {selected_target}"
    )
    proof_items.append(
        _build_proof_item(
            invariant_code="HASH_RECOMPUTE_MATCH",
            status="pass" if hash_recompute_ok else "fail",
            justification_refs=[normative_ref],
            message=hash_recompute_message,
            expected_hash=expected_hash,
            observed_hash=observed_hash,
        )
    )

    coherence_bridge_manifest_hash = str(coherence_payload.get("bridge_manifest_hash") or "")
    normative_bridge_manifest_hash = str(normative_payload.get("bridge_manifest_hash") or "")
    emitted_packet_bridge_manifest_hash = bridge_manifest_hash

    pair_binding_ok = (
        coherence_payload.get("source_text_hash") == source_text_hash
        and coherence_payload.get("core_ir_artifact_id") == core_ir_artifact_id
        and coherence_payload.get("concept_artifact_id") == concept_artifact_id
        and normative_payload.get("source_text_hash") == source_text_hash
        and normative_payload.get("core_ir_artifact_id") == core_ir_artifact_id
        and normative_payload.get("concept_artifact_id") == concept_artifact_id
    )
    manifest_chain_ok = (
        pair_binding_ok
        and recomputed_bridge_manifest_hash == coherence_bridge_manifest_hash
        and coherence_bridge_manifest_hash == normative_bridge_manifest_hash
        and normative_bridge_manifest_hash == emitted_packet_bridge_manifest_hash
    )
    if recomputed_bridge_manifest_hash != coherence_bridge_manifest_hash:
        observed_chain_hash = coherence_bridge_manifest_hash
    elif coherence_bridge_manifest_hash != normative_bridge_manifest_hash:
        observed_chain_hash = normative_bridge_manifest_hash
    elif normative_bridge_manifest_hash != emitted_packet_bridge_manifest_hash:
        observed_chain_hash = emitted_packet_bridge_manifest_hash
    else:
        observed_chain_hash = recomputed_bridge_manifest_hash
    proof_items.append(
        _build_proof_item(
            invariant_code="MANIFEST_CHAIN_STABILITY",
            status="pass" if manifest_chain_ok else "fail",
            justification_refs=[coherence_ref, normative_ref],
            message=(
                "manifest chain checks passed"
                if manifest_chain_ok
                else "manifest chain mismatch detected"
            ),
            expected_hash=recomputed_bridge_manifest_hash,
            observed_hash=observed_chain_hash,
        )
    )

    packet_basis_without_replay = {
        "schema": TRUST_INVARIANT_PACKET_SCHEMA,
        "source_text_hash": source_text_hash,
        "core_ir_artifact_id": core_ir_artifact_id,
        "concept_artifact_id": concept_artifact_id,
        "bridge_manifest_hash": bridge_manifest_hash,
        "normative_advice_packet_hash": normative_advice_packet_hash,
        "proof_items": sorted(proof_items, key=_proof_sort_key),
    }
    replay_hashes = [
        _sha256_created_at_stripped(packet_basis_without_replay)
        for _ in range(3)
    ]
    replay_hash_stable = len(set(replay_hashes)) == 1
    replay_hash = replay_hashes[0]
    proof_items.append(
        _build_proof_item(
            invariant_code="REPLAY_HASH_STABILITY",
            status="pass" if replay_hash_stable else "fail",
            justification_refs=[trust_ref],
            message=(
                "replay hash stability checks passed"
                if replay_hash_stable
                else "replay hash stability mismatch detected across replay runs"
            ),
            observed_hash=replay_hash,
        )
    )

    proof_items = sorted(proof_items, key=_proof_sort_key)
    counts_by_status = _counts_by_status(proof_items)
    counts_by_invariant_code = _counts_by_invariant_code(proof_items)
    packet_payload = {
        "schema": TRUST_INVARIANT_PACKET_SCHEMA,
        "source_text_hash": source_text_hash,
        "core_ir_artifact_id": core_ir_artifact_id,
        "concept_artifact_id": concept_artifact_id,
        "bridge_manifest_hash": bridge_manifest_hash,
        "normative_advice_packet_hash": normative_advice_packet_hash,
        "proof_summary": {
            "total_checks": len(proof_items),
            "passed_checks": counts_by_status.get("pass", 0),
            "failed_checks": counts_by_status.get("fail", 0),
            "counts_by_invariant_code": counts_by_invariant_code,
            "counts_by_status": counts_by_status,
        },
        "proof_items": proof_items,
    }
    try:
        normalized = AdeuTrustInvariantPacket.model_validate(packet_payload)
    except Exception as exc:
        raise _trust_invariant_error(
            code="URM_ADEU_TRUST_INVARIANT_PAYLOAD_INVALID",
            reason="trust-invariant packet payload failed schema validation",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "error": str(exc),
            },
        ) from exc

    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)
