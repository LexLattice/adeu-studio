from __future__ import annotations

import json
from collections import Counter
from collections.abc import Mapping
from functools import lru_cache
from pathlib import Path
from typing import Any, Literal

from adeu_core_ir import AdeuNormativeAdvicePacket
from pydantic import BaseModel, ConfigDict, Field, model_validator

from .cross_ir_bridge_vnext_plus20 import (
    CrossIRBridgeVnextPlus20Error,
    build_cross_ir_bridge_manifest_vnext_plus20,
    canonical_bridge_manifest_hash_vnext_plus20,
    load_cross_ir_pair_artifacts_vnext_plus20,
)
from .cross_ir_coherence_vnext_plus20 import AdeuCrossIRCoherenceDiagnostics
from .hashing import canonical_json, sha256_text

VNEXT_PLUS20_STOP_GATE_MANIFEST_SCHEMA = "stop_gate.vnext_plus20_manifest@1"
VNEXT_PLUS20_STOP_GATE_MANIFEST_PATH = (
    Path(__file__).resolve().parents[2] / "fixtures" / "stop_gate" / "vnext_plus20_manifest.json"
)
NORMATIVE_ADVICE_PACKET_SCHEMA = "adeu_normative_advice_packet@0.1"
_COHERENCE_SURFACE_ID = "adeu.cross_ir.coherence_diagnostics"

NormativeAdviceCode = Literal[
    "MAPPING_GAP_REVIEW",
    "SOURCE_DIVERGENCE_REVIEW",
    "TOPOLOGY_ALIGNMENT_REVIEW",
    "CLAIM_PROJECTION_REVIEW",
    "TRUST_ALIGNMENT_REVIEW",
]

_ISSUE_CODE_TO_ADVICE_CODE: dict[str, NormativeAdviceCode] = {
    "MISSING_CONCEPT_MAPPING": "MAPPING_GAP_REVIEW",
    "MISSING_CORE_IR_MAPPING": "MAPPING_GAP_REVIEW",
    "SOURCE_HASH_MISMATCH": "SOURCE_DIVERGENCE_REVIEW",
    "TOPOLOGY_DRIFT": "TOPOLOGY_ALIGNMENT_REVIEW",
    "LINK_KIND_DRIFT": "TOPOLOGY_ALIGNMENT_REVIEW",
    "CLAIM_PROJECTION_GAP": "CLAIM_PROJECTION_REVIEW",
    "TRUST_LABEL_MISMATCH": "TRUST_ALIGNMENT_REVIEW",
}
_ADVICE_PRIORITY_BY_CODE: dict[NormativeAdviceCode, str] = {
    "MAPPING_GAP_REVIEW": "medium",
    "SOURCE_DIVERGENCE_REVIEW": "high",
    "TOPOLOGY_ALIGNMENT_REVIEW": "medium",
    "CLAIM_PROJECTION_REVIEW": "high",
    "TRUST_ALIGNMENT_REVIEW": "medium",
}
_ADVICE_MESSAGE_BY_CODE: dict[NormativeAdviceCode, str] = {
    "MAPPING_GAP_REVIEW": (
        "review unmapped concept/core-ir coverage and reconcile missing mappings"
    ),
    "SOURCE_DIVERGENCE_REVIEW": (
        "review source-hash divergence between concept and core-ir evidence"
    ),
    "TOPOLOGY_ALIGNMENT_REVIEW": (
        "review topology/link-kind alignment between concept and core-ir structures"
    ),
    "CLAIM_PROJECTION_REVIEW": (
        "review claim projection coverage into claim-like core-ir targets"
    ),
    "TRUST_ALIGNMENT_REVIEW": (
        "review trust-label alignment across mapped concept/core-ir evidence"
    ),
}
_HEX16_RE = frozenset("0123456789abcdef")


class NormativeAdviceVnextPlus21Error(ValueError):
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


def _normative_advice_error(
    *,
    code: str,
    reason: str,
    context: Mapping[str, Any] | None = None,
) -> NormativeAdviceVnextPlus21Error:
    return NormativeAdviceVnextPlus21Error(code=code, reason=reason, context=context)


def _resolved_manifest_path(path: Path | None) -> Path:
    selected = VNEXT_PLUS20_STOP_GATE_MANIFEST_PATH if path is None else Path(path)
    return selected.resolve()


def _cross_ir_error_to_normative(
    exc: CrossIRBridgeVnextPlus20Error,
) -> NormativeAdviceVnextPlus21Error:
    mapped_code = {
        "URM_ADEU_CROSS_IR_REQUEST_INVALID": "URM_ADEU_NORMATIVE_ADVICE_REQUEST_INVALID",
        "URM_ADEU_CROSS_IR_ARTIFACT_NOT_FOUND": "URM_ADEU_NORMATIVE_ADVICE_ARTIFACT_NOT_FOUND",
        "URM_ADEU_CROSS_IR_PAYLOAD_INVALID": "URM_ADEU_NORMATIVE_ADVICE_PAYLOAD_INVALID",
        "URM_ADEU_CROSS_IR_FIXTURE_INVALID": "URM_ADEU_NORMATIVE_ADVICE_FIXTURE_INVALID",
    }.get(exc.code, "URM_ADEU_NORMATIVE_ADVICE_PAYLOAD_INVALID")
    return _normative_advice_error(
        code=mapped_code,
        reason=exc.reason,
        context=exc.context,
    )


def _advice_id(
    *,
    advice_code: NormativeAdviceCode,
    concept_refs: list[str],
    core_ir_refs: list[str],
    justification_refs: list[str],
) -> str:
    return sha256_text(
        canonical_json(
            {
                "advice_code": advice_code,
                "concept_refs": concept_refs,
                "core_ir_refs": core_ir_refs,
                "justification_refs": justification_refs,
            }
        )
    )[:16]


def _advice_sort_key(item: Mapping[str, Any]) -> tuple[str, str, str, str]:
    concept_refs = item.get("concept_refs")
    core_ir_refs = item.get("core_ir_refs")
    return (
        str(item.get("advice_code") or ""),
        str(concept_refs[0]) if isinstance(concept_refs, list) and concept_refs else "",
        str(core_ir_refs[0]) if isinstance(core_ir_refs, list) and core_ir_refs else "",
        str(item.get("advice_id") or ""),
    )


def _is_hex16(value: str) -> bool:
    return len(value) == 16 and all(char in _HEX16_RE for char in value)


def _issue_id_from_justification_ref(value: str) -> str | None:
    prefix = "coherence_issue:"
    if not value.startswith(prefix):
        return None
    issue_id = value[len(prefix) :]
    if not _is_hex16(issue_id):
        return None
    return issue_id


@lru_cache(maxsize=8)
def _coherence_fixture_index_for_manifest(
    manifest_path_value: str,
) -> dict[tuple[str, str, str], Path]:
    manifest_path = Path(manifest_path_value)
    try:
        raw_payload = manifest_path.read_text(encoding="utf-8")
    except FileNotFoundError as exc:
        raise _normative_advice_error(
            code="URM_ADEU_NORMATIVE_ADVICE_FIXTURE_INVALID",
            reason="vnext+20 stop-gate manifest fixture is missing",
            context={"path": str(manifest_path)},
        ) from exc
    except OSError as exc:
        raise _normative_advice_error(
            code="URM_ADEU_NORMATIVE_ADVICE_FIXTURE_INVALID",
            reason="vnext+20 stop-gate manifest fixture is unreadable",
            context={"path": str(manifest_path), "error": str(exc)},
        ) from exc

    try:
        parsed = json.loads(raw_payload)
    except json.JSONDecodeError as exc:
        raise _normative_advice_error(
            code="URM_ADEU_NORMATIVE_ADVICE_FIXTURE_INVALID",
            reason="vnext+20 stop-gate manifest JSON is invalid",
            context={"path": str(manifest_path), "error": exc.msg},
        ) from exc

    if not isinstance(parsed, dict):
        raise _normative_advice_error(
            code="URM_ADEU_NORMATIVE_ADVICE_FIXTURE_INVALID",
            reason="vnext+20 stop-gate manifest payload must be an object",
            context={"path": str(manifest_path)},
        )

    try:
        manifest = _VnextPlus20StopGateManifest.model_validate(parsed)
    except Exception as exc:
        raise _normative_advice_error(
            code="URM_ADEU_NORMATIVE_ADVICE_FIXTURE_INVALID",
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
            raise _normative_advice_error(
                code="URM_ADEU_NORMATIVE_ADVICE_REQUEST_INVALID",
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
        raise _normative_advice_error(
            code="URM_ADEU_NORMATIVE_ADVICE_ARTIFACT_NOT_FOUND",
            reason="matched coherence diagnostics artifact fixture is missing",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
            },
        ) from exc
    except OSError as exc:
        raise _normative_advice_error(
            code="URM_ADEU_NORMATIVE_ADVICE_FIXTURE_INVALID",
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
        raise _normative_advice_error(
            code="URM_ADEU_NORMATIVE_ADVICE_PAYLOAD_INVALID",
            reason="matched coherence diagnostics artifact JSON is invalid",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
                "error": exc.msg,
            },
        ) from exc
    if not isinstance(parsed, dict):
        raise _normative_advice_error(
            code="URM_ADEU_NORMATIVE_ADVICE_PAYLOAD_INVALID",
            reason="matched coherence diagnostics artifact payload must be an object",
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
        raise _normative_advice_error(
            code="URM_ADEU_NORMATIVE_ADVICE_PAYLOAD_INVALID",
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
    if payload["source_text_hash"] != source_text_hash:
        raise _normative_advice_error(
            code="URM_ADEU_NORMATIVE_ADVICE_PAYLOAD_INVALID",
            reason="coherence payload source_text_hash does not match pair identity",
            context={
                "source_text_hash": source_text_hash,
                "payload_source_text_hash": payload["source_text_hash"],
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
            },
        )
    if payload["core_ir_artifact_id"] != core_ir_artifact_id:
        raise _normative_advice_error(
            code="URM_ADEU_NORMATIVE_ADVICE_PAYLOAD_INVALID",
            reason="coherence payload core_ir_artifact_id does not match pair identity",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "payload_core_ir_artifact_id": payload["core_ir_artifact_id"],
                "concept_artifact_id": concept_artifact_id,
            },
        )
    if payload["concept_artifact_id"] != concept_artifact_id:
        raise _normative_advice_error(
            code="URM_ADEU_NORMATIVE_ADVICE_PAYLOAD_INVALID",
            reason="coherence payload concept_artifact_id does not match pair identity",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "payload_concept_artifact_id": payload["concept_artifact_id"],
            },
        )
    return payload


def _coherence_payload_for_pair(
    *,
    source_text_hash: str,
    core_ir_artifact_id: str,
    concept_artifact_id: str,
    coherence_manifest_path: Path | None = None,
) -> dict[str, Any]:
    manifest_path = _resolved_manifest_path(coherence_manifest_path)
    by_identity = _coherence_fixture_index_for_manifest(str(manifest_path))
    identity = (source_text_hash, core_ir_artifact_id, concept_artifact_id)
    coherence_paths = by_identity.get(identity)
    if coherence_paths is None:
        raise _normative_advice_error(
            code="URM_ADEU_NORMATIVE_ADVICE_ARTIFACT_NOT_FOUND",
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
        hash_by_path[path_key] = sha256_text(canonical_json(payload))

    if len(set(hash_by_path.values())) > 1:
        raise _normative_advice_error(
            code="URM_ADEU_NORMATIVE_ADVICE_DIAGNOSTIC_DRIFT",
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


def _issue_is_intentional_asymmetry_only(
    *,
    issue: Mapping[str, Any],
    intentional_concept_only_object_ids: set[str],
    intentional_core_ir_only_object_ids: set[str],
) -> bool:
    issue_code = issue.get("issue_code")
    concept_refs = issue.get("concept_refs")
    core_ir_refs = issue.get("core_ir_refs")
    if not isinstance(concept_refs, list) or not isinstance(core_ir_refs, list):
        return False
    if issue_code == "MISSING_CONCEPT_MAPPING":
        return (
            bool(concept_refs)
            and not core_ir_refs
            and set(concept_refs).issubset(intentional_concept_only_object_ids)
        )
    if issue_code == "MISSING_CORE_IR_MAPPING":
        return (
            bool(core_ir_refs)
            and not concept_refs
            and set(core_ir_refs).issubset(intentional_core_ir_only_object_ids)
        )
    return False


def build_normative_advice_packet_vnext_plus21(
    *,
    source_text_hash: str,
    core_ir_artifact_id: str,
    concept_artifact_id: str,
    catalog_path: Path | None = None,
    coherence_manifest_path: Path | None = None,
    include_source_issue_snapshot: bool = False,
) -> dict[str, Any]:
    try:
        pair_artifacts = load_cross_ir_pair_artifacts_vnext_plus20(
            source_text_hash=source_text_hash,
            core_ir_artifact_id=core_ir_artifact_id,
            concept_artifact_id=concept_artifact_id,
            catalog_path=catalog_path,
        )
        bridge_manifest = build_cross_ir_bridge_manifest_vnext_plus20(
            source_text_hash=source_text_hash,
            core_ir_artifact_id=core_ir_artifact_id,
            concept_artifact_id=concept_artifact_id,
            catalog_path=catalog_path,
        )
    except CrossIRBridgeVnextPlus20Error as exc:
        raise _cross_ir_error_to_normative(exc) from exc

    bridge_manifest_hash = canonical_bridge_manifest_hash_vnext_plus20(bridge_manifest)
    coherence_payload = _coherence_payload_for_pair(
        source_text_hash=source_text_hash,
        core_ir_artifact_id=core_ir_artifact_id,
        concept_artifact_id=concept_artifact_id,
        coherence_manifest_path=coherence_manifest_path,
    )
    if coherence_payload["bridge_manifest_hash"] != bridge_manifest_hash:
        raise _normative_advice_error(
            code="URM_ADEU_NORMATIVE_ADVICE_PAYLOAD_INVALID",
            reason="coherence bridge_manifest_hash does not match canonical bridge manifest hash",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "expected_bridge_manifest_hash": bridge_manifest_hash,
                "payload_bridge_manifest_hash": coherence_payload["bridge_manifest_hash"],
            },
        )

    intentional_concept_only = set(pair_artifacts.intentional_concept_only_object_ids)
    intentional_core_ir_only = set(pair_artifacts.intentional_core_ir_only_object_ids)

    advice_items: list[dict[str, Any]] = []
    issues = coherence_payload.get("issues")
    if not isinstance(issues, list):
        raise _normative_advice_error(
            code="URM_ADEU_NORMATIVE_ADVICE_PAYLOAD_INVALID",
            reason="coherence payload issues must be a list",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
            },
        )
    for issue_raw in issues:
        if not isinstance(issue_raw, Mapping):
            continue
        issue = dict(issue_raw)
        issue_code = issue.get("issue_code")
        severity = issue.get("severity")
        if issue_code not in _ISSUE_CODE_TO_ADVICE_CODE:
            continue
        if severity not in {"warn", "error"}:
            continue
        if _issue_is_intentional_asymmetry_only(
            issue=issue,
            intentional_concept_only_object_ids=intentional_concept_only,
            intentional_core_ir_only_object_ids=intentional_core_ir_only,
        ):
            continue

        concept_refs = issue.get("concept_refs")
        core_ir_refs = issue.get("core_ir_refs")
        issue_id = issue.get("issue_id")
        if (
            not isinstance(concept_refs, list)
            or not all(isinstance(ref, str) for ref in concept_refs)
            or not isinstance(core_ir_refs, list)
            or not all(isinstance(ref, str) for ref in core_ir_refs)
            or not isinstance(issue_id, str)
            or not _is_hex16(issue_id)
        ):
            raise _normative_advice_error(
                code="URM_ADEU_NORMATIVE_ADVICE_PAYLOAD_INVALID",
                reason="coherence issue payload is invalid for normative advice derivation",
                context={
                    "source_text_hash": source_text_hash,
                    "core_ir_artifact_id": core_ir_artifact_id,
                    "concept_artifact_id": concept_artifact_id,
                    "issue_code": issue_code,
                },
            )

        advice_code = _ISSUE_CODE_TO_ADVICE_CODE[str(issue_code)]
        justification_ref = f"coherence_issue:{issue_id}"
        justification_refs = [justification_ref]
        advice_item: dict[str, Any] = {
            "advice_id": _advice_id(
                advice_code=advice_code,
                concept_refs=concept_refs,
                core_ir_refs=core_ir_refs,
                justification_refs=justification_refs,
            ),
            "advice_code": advice_code,
            "priority": _ADVICE_PRIORITY_BY_CODE[advice_code],
            "concept_refs": concept_refs,
            "core_ir_refs": core_ir_refs,
            "justification_refs": justification_refs,
            "message": _ADVICE_MESSAGE_BY_CODE[advice_code],
        }
        if include_source_issue_snapshot:
            advice_item["source_issue_snapshot"] = {
                "issue_id": issue_id,
                "issue_code": issue["issue_code"],
                "severity": issue["severity"],
                "message": issue["message"],
                "evidence": issue["evidence"],
            }
        advice_items.append(advice_item)

    advice_items = sorted(advice_items, key=_advice_sort_key)
    counts_by_code = Counter(item["advice_code"] for item in advice_items)
    counts_by_priority = Counter(item["priority"] for item in advice_items)
    packet_payload = {
        "schema": NORMATIVE_ADVICE_PACKET_SCHEMA,
        "source_text_hash": source_text_hash,
        "core_ir_artifact_id": core_ir_artifact_id,
        "concept_artifact_id": concept_artifact_id,
        "bridge_manifest_hash": bridge_manifest_hash,
        "advice_summary": {
            "total_advice": len(advice_items),
            "counts_by_code": {code: counts_by_code[code] for code in sorted(counts_by_code)},
            "counts_by_priority": {
                priority: counts_by_priority[priority] for priority in sorted(counts_by_priority)
            },
        },
        "advice_items": advice_items,
    }
    try:
        normalized = AdeuNormativeAdvicePacket.model_validate(packet_payload)
    except Exception as exc:
        raise _normative_advice_error(
            code="URM_ADEU_NORMATIVE_ADVICE_PAYLOAD_INVALID",
            reason="normative advice packet payload failed schema validation",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "error": str(exc),
            },
        ) from exc

    # Defensive assertion: emitted ids must remain recoverable from justification refs.
    for item in normalized.advice_items:
        issue_id = _issue_id_from_justification_ref(item.justification_refs[0])
        if issue_id is None:
            raise _normative_advice_error(
                code="URM_ADEU_NORMATIVE_ADVICE_PAYLOAD_INVALID",
                reason="justification_refs entry is not a stable coherence_issue reference",
                context={
                    "source_text_hash": source_text_hash,
                    "core_ir_artifact_id": core_ir_artifact_id,
                    "concept_artifact_id": concept_artifact_id,
                    "advice_id": item.advice_id,
                },
            )

    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)
