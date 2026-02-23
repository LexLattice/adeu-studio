from __future__ import annotations

import json
from collections import Counter
from collections.abc import Iterator, Mapping
from contextlib import contextmanager
from contextvars import ContextVar
from functools import lru_cache
from pathlib import Path
from typing import Any, Literal, cast

from adeu_core_ir import (
    AdeuSemanticsV4CandidatePacket,
    AdeuTrustInvariantPacket,
    build_semantics_v4_candidate_comparison_id,
)
from pydantic import BaseModel, ConfigDict, Field, ValidationError, model_validator

from .cross_ir_bridge_vnext_plus20 import (
    CrossIRBridgeVnextPlus20Error,
    build_cross_ir_bridge_manifest_vnext_plus20,
    list_cross_ir_catalog_pairs_vnext_plus20,
)
from .hashing import canonical_json, sha256_text

VNEXT_PLUS22_STOP_GATE_MANIFEST_SCHEMA = "stop_gate.vnext_plus22_manifest@1"
VNEXT_PLUS23_STOP_GATE_MANIFEST_SCHEMA = "stop_gate.vnext_plus23_manifest@1"
VNEXT_PLUS22_STOP_GATE_MANIFEST_PATH = (
    Path(__file__).resolve().parents[2] / "fixtures" / "stop_gate" / "vnext_plus22_manifest.json"
)
VNEXT_PLUS23_STOP_GATE_MANIFEST_PATH = (
    Path(__file__).resolve().parents[2] / "fixtures" / "stop_gate" / "vnext_plus23_manifest.json"
)
SEMANTICS_V4_CANDIDATE_PACKET_SCHEMA = "adeu_semantics_v4_candidate_packet@0.1"
SEMANTICS_V4_CANDIDATE_PROJECTION_SCHEMA = "semantics_v4_candidate_projection.vnext_plus23@1"

_TRUST_PACKET_SURFACE_ID = "adeu.trust_invariant.packet"
_SEMANTICS_V4_PACKET_SURFACE_ID = "adeu.semantics_v4_candidate.packet"

_STATUS_VALUES = frozenset({"SAT", "UNSAT", "UNKNOWN", "TIMEOUT", "INVALID_REQUEST", "ERROR"})
_ASSURANCE_VALUES = frozenset({"kernel_only", "solver_backed", "proof_checked"})

_STATUS_SET_CONTINUITY_REVIEW = "STATUS_SET_CONTINUITY_REVIEW"
_ASSURANCE_SET_CONTINUITY_REVIEW = "ASSURANCE_SET_CONTINUITY_REVIEW"
_REQUEST_FORMULA_HASH_CONTINUITY_REVIEW = "REQUEST_FORMULA_HASH_CONTINUITY_REVIEW"
_WITNESS_REF_STRUCTURE_REVIEW = "WITNESS_REF_STRUCTURE_REVIEW"

_STATUS_TOKEN_NORMALIZATION = {
    "UNKNOWN": "UNKNOWN_OR_TIMEOUT",
    "TIMEOUT": "UNKNOWN_OR_TIMEOUT",
}

_COMPARISON_MESSAGE_BY_CODE: dict[str, str] = {
    _STATUS_SET_CONTINUITY_REVIEW: "status-set continuity comparison between v3 and v4 candidate",
    _ASSURANCE_SET_CONTINUITY_REVIEW: (
        "assurance-set continuity comparison between v3 and v4 candidate"
    ),
    _REQUEST_FORMULA_HASH_CONTINUITY_REVIEW: (
        "request/formula hash continuity comparison between v3 and v4 candidate"
    ),
    _WITNESS_REF_STRUCTURE_REVIEW: (
        "witness-ref structure continuity comparison between v3 and v4 candidate"
    ),
}

_COMPARISON_SEVERITY_BY_CODE_STATUS: dict[tuple[str, str], str] = {
    (_STATUS_SET_CONTINUITY_REVIEW, "compatible"): "low",
    (_STATUS_SET_CONTINUITY_REVIEW, "drift"): "high",
    (_ASSURANCE_SET_CONTINUITY_REVIEW, "compatible"): "low",
    (_ASSURANCE_SET_CONTINUITY_REVIEW, "drift"): "medium",
    (_REQUEST_FORMULA_HASH_CONTINUITY_REVIEW, "compatible"): "low",
    (_REQUEST_FORMULA_HASH_CONTINUITY_REVIEW, "drift"): "high",
    (_WITNESS_REF_STRUCTURE_REVIEW, "compatible"): "low",
    (_WITNESS_REF_STRUCTURE_REVIEW, "drift"): "medium",
}

_SEMANTICS_V4_CANDIDATE_NON_ENFORCEMENT_CONTEXT: ContextVar[bool] = ContextVar(
    "semantics_v4_candidate_non_enforcement_context",
    default=False,
)


class SemanticsV4CandidateVnextPlus23Error(ValueError):
    def __init__(self, *, code: str, reason: str, context: Mapping[str, Any] | None = None) -> None:
        super().__init__(reason)
        self.code = code
        self.reason = reason
        self.context = dict(context or {})


class _TrustInvariantPacketRun(BaseModel):
    model_config = ConfigDict(extra="ignore")

    trust_invariant_packet_path: str = Field(min_length=1)


class _TrustInvariantPacketFixture(BaseModel):
    model_config = ConfigDict(extra="ignore")

    source_text_hash: str = Field(min_length=1)
    core_ir_artifact_id: str = Field(min_length=1)
    concept_artifact_id: str = Field(min_length=1)
    fixture_id: str = Field(min_length=1)
    surface_id: Literal["adeu.trust_invariant.packet"] = _TRUST_PACKET_SURFACE_ID
    runs: list[_TrustInvariantPacketRun] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "_TrustInvariantPacketFixture":
        if not self.runs:
            raise ValueError("trust-invariant packet fixture must include at least one run")
        run_paths = [run.trust_invariant_packet_path for run in self.runs]
        if len(set(run_paths)) != len(run_paths):
            raise ValueError("trust-invariant packet fixture run paths must be unique")
        return self


class _VnextPlus22StopGateManifest(BaseModel):
    model_config = ConfigDict(extra="ignore")

    schema: Literal["stop_gate.vnext_plus22_manifest@1"] = VNEXT_PLUS22_STOP_GATE_MANIFEST_SCHEMA
    trust_invariant_packet_fixtures: list[_TrustInvariantPacketFixture] = Field(
        default_factory=list
    )


class _SemanticsV4CandidatePacketRun(BaseModel):
    model_config = ConfigDict(extra="ignore")

    semantics_v4_candidate_packet_path: str = Field(min_length=1)


class _SemanticsV4CandidatePacketFixture(BaseModel):
    model_config = ConfigDict(extra="ignore")

    source_text_hash: str = Field(min_length=1)
    core_ir_artifact_id: str = Field(min_length=1)
    concept_artifact_id: str = Field(min_length=1)
    fixture_id: str = Field(min_length=1)
    surface_id: Literal["adeu.semantics_v4_candidate.packet"] = _SEMANTICS_V4_PACKET_SURFACE_ID
    semantics_v3_path: str = Field(min_length=1)
    semantics_v4_candidate_path: str = Field(min_length=1)
    semantics_v3_source_lane: Literal["v3_default"] = "v3_default"
    semantics_v4_candidate_source_lane: Literal["v4_candidate"] = "v4_candidate"
    runs: list[_SemanticsV4CandidatePacketRun] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "_SemanticsV4CandidatePacketFixture":
        if not self.runs:
            raise ValueError("semantics-v4 candidate packet fixture must include at least one run")
        run_paths = [run.semantics_v4_candidate_packet_path for run in self.runs]
        if len(set(run_paths)) != len(run_paths):
            raise ValueError("semantics-v4 candidate packet fixture run paths must be unique")
        return self


class _VnextPlus23StopGateManifest(BaseModel):
    model_config = ConfigDict(extra="ignore")

    schema: Literal["stop_gate.vnext_plus23_manifest@1"] = VNEXT_PLUS23_STOP_GATE_MANIFEST_SCHEMA
    semantics_v4_candidate_packet_fixtures: list[_SemanticsV4CandidatePacketFixture] = Field(
        default_factory=list
    )


class SemanticsV4CandidateProjectionVnextPlus23(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: Literal["semantics_v4_candidate_projection.vnext_plus23@1"] = (
        SEMANTICS_V4_CANDIDATE_PROJECTION_SCHEMA
    )
    bridge_pair_count: int = Field(ge=0)
    comparison_item_count: int = Field(ge=0)
    comparison_counts_by_code: dict[str, int] = Field(default_factory=dict)
    comparison_counts_by_status: dict[str, int] = Field(default_factory=dict)
    comparison_counts_by_severity: dict[str, int] = Field(default_factory=dict)

    @model_validator(mode="after")
    def _validate_contract(self) -> "SemanticsV4CandidateProjectionVnextPlus23":
        for field_name, valid_keys, unsupported_key_error in (
            (
                "comparison_counts_by_code",
                set(_COMPARISON_MESSAGE_BY_CODE),
                "comparison_counts_by_code contains unsupported comparison_code",
            ),
            (
                "comparison_counts_by_status",
                {"compatible", "drift"},
                "comparison_counts_by_status contains unsupported status value",
            ),
            (
                "comparison_counts_by_severity",
                {"high", "low", "medium"},
                "comparison_counts_by_severity contains unsupported severity value",
            ),
        ):
            counts_dict = cast(dict[str, int], getattr(self, field_name))
            if list(counts_dict.keys()) != sorted(counts_dict.keys()):
                raise ValueError(f"{field_name} keys must be lexicographically sorted")
            if any(key not in valid_keys for key in counts_dict):
                raise ValueError(unsupported_key_error)
            if any(value < 0 for value in counts_dict.values()):
                raise ValueError(f"{field_name} values must be non-negative integers")

        if self.comparison_item_count != sum(self.comparison_counts_by_code.values()):
            raise ValueError(
                "comparison_item_count must equal sum(comparison_counts_by_code.values())"
            )
        if self.comparison_item_count != sum(self.comparison_counts_by_status.values()):
            raise ValueError(
                "comparison_item_count must equal sum(comparison_counts_by_status.values())"
            )
        if self.comparison_item_count != sum(self.comparison_counts_by_severity.values()):
            raise ValueError(
                "comparison_item_count must equal sum(comparison_counts_by_severity.values())"
            )
        return self


class _SemanticsDiagnosticsWitnessRef(BaseModel):
    model_config = ConfigDict(extra="forbid")

    assertion_name: str = Field(min_length=1)
    object_id: str | None = None
    json_path: str | None = None


class _SemanticsDiagnosticsRecord(BaseModel):
    model_config = ConfigDict(extra="forbid")

    kind: Literal["validator_run"]
    validator_run_id: str = Field(min_length=1)
    formula_hash: str = Field(min_length=64, max_length=64, pattern=r"^[a-f0-9]{64}$")
    request_hash: str = Field(min_length=64, max_length=64, pattern=r"^[a-f0-9]{64}$")
    status: Literal["SAT", "UNSAT", "UNKNOWN", "TIMEOUT", "INVALID_REQUEST", "ERROR"]
    assurance: Literal["kernel_only", "solver_backed", "proof_checked"]
    validator_evidence_packet_ref: str = Field(min_length=1)
    validator_evidence_packet_hash: str = Field(
        min_length=64,
        max_length=64,
        pattern=r"^[a-f0-9]{64}$",
    )
    witness_refs: list[_SemanticsDiagnosticsWitnessRef] = Field(default_factory=list)


class _SemanticsDiagnosticsPayload(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: Literal["semantics_diagnostics@1"]
    artifact_ref: str = Field(min_length=1)
    records: list[_SemanticsDiagnosticsRecord] = Field(default_factory=list)
    semantics_diagnostics_hash: str = Field(
        min_length=64,
        max_length=64,
        pattern=r"^[a-f0-9]{64}$",
    )


def _semantics_v4_candidate_error(
    *,
    code: str,
    reason: str,
    context: Mapping[str, Any] | None = None,
) -> SemanticsV4CandidateVnextPlus23Error:
    return SemanticsV4CandidateVnextPlus23Error(code=code, reason=reason, context=context)


@contextmanager
def semantics_v4_candidate_non_enforcement_context() -> Iterator[None]:
    token = _SEMANTICS_V4_CANDIDATE_NON_ENFORCEMENT_CONTEXT.set(True)
    try:
        yield
    finally:
        _SEMANTICS_V4_CANDIDATE_NON_ENFORCEMENT_CONTEXT.reset(token)


def _require_semantics_v4_candidate_non_enforcement_context(*, operation: str) -> None:
    if _SEMANTICS_V4_CANDIDATE_NON_ENFORCEMENT_CONTEXT.get():
        return
    raise _semantics_v4_candidate_error(
        code="URM_ADEU_SEMANTICS_V4_REQUEST_INVALID",
        reason="semantics-v4 candidate runtime non-enforcement context is not active",
        context={"operation": operation},
    )


def _resolved_manifest_path(path: Path | None, *, default: Path) -> Path:
    selected = default if path is None else Path(path)
    return selected.resolve()


def _cross_ir_error_to_semantics_v4(
    exc: CrossIRBridgeVnextPlus20Error,
) -> SemanticsV4CandidateVnextPlus23Error:
    mapped_code = {
        "URM_ADEU_CROSS_IR_REQUEST_INVALID": "URM_ADEU_SEMANTICS_V4_REQUEST_INVALID",
        "URM_ADEU_CROSS_IR_ARTIFACT_NOT_FOUND": "URM_ADEU_SEMANTICS_V4_ARTIFACT_NOT_FOUND",
        "URM_ADEU_CROSS_IR_PAYLOAD_INVALID": "URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID",
        "URM_ADEU_CROSS_IR_FIXTURE_INVALID": "URM_ADEU_SEMANTICS_V4_FIXTURE_INVALID",
    }.get(exc.code, "URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID")
    return _semantics_v4_candidate_error(
        code=mapped_code,
        reason=exc.reason,
        context=exc.context,
    )


def _strip_created_at_recursive(value: Any) -> Any:
    if isinstance(value, Mapping):
        normalized: dict[str, Any] = {}
        for raw_key, raw_value in value.items():
            key = str(raw_key)
            if key == "created_at":
                continue
            normalized[key] = _strip_created_at_recursive(raw_value)
        return normalized
    if isinstance(value, list):
        return [_strip_created_at_recursive(item) for item in value]
    return value


def _sha256_created_at_stripped(payload: Any) -> str:
    return sha256_text(canonical_json(_strip_created_at_recursive(payload)))


def _artifact_ref(
    *,
    schema: str,
    source_text_hash: str,
    core_ir_artifact_id: str,
    concept_artifact_id: str,
    lane: str | None = None,
) -> str:
    if lane is None:
        return (
            "artifact:"
            f"{schema}:{source_text_hash}:{core_ir_artifact_id}:{concept_artifact_id}"
        )
    return (
        "artifact:"
        f"{schema}:{lane}:{source_text_hash}:{core_ir_artifact_id}:{concept_artifact_id}"
    )


def _semantics_diagnostics_hash(payload: Mapping[str, Any]) -> str:
    basis = {
        key: payload[key]
        for key in sorted(payload.keys())
        if key != "semantics_diagnostics_hash"
    }
    return sha256_text(canonical_json(basis))


@lru_cache(maxsize=8)
def _trust_packet_fixture_index_for_manifest(
    manifest_path_value: str,
) -> dict[tuple[str, str, str], tuple[tuple[str, tuple[Path, ...]], ...]]:
    manifest_path = Path(manifest_path_value)
    try:
        raw_payload = manifest_path.read_text(encoding="utf-8")
    except FileNotFoundError as exc:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_FIXTURE_INVALID",
            reason="vnext+22 stop-gate manifest fixture is missing",
            context={"path": str(manifest_path)},
        ) from exc
    except OSError as exc:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_FIXTURE_INVALID",
            reason="vnext+22 stop-gate manifest fixture is unreadable",
            context={"path": str(manifest_path), "error": str(exc)},
        ) from exc

    try:
        parsed = json.loads(raw_payload)
    except json.JSONDecodeError as exc:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_FIXTURE_INVALID",
            reason="vnext+22 stop-gate manifest JSON is invalid",
            context={"path": str(manifest_path), "error": exc.msg},
        ) from exc

    try:
        manifest = _VnextPlus22StopGateManifest.model_validate(parsed)
    except ValidationError as exc:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_FIXTURE_INVALID",
            reason="vnext+22 stop-gate manifest payload failed schema validation",
            context={"path": str(manifest_path), "error": str(exc)},
        ) from exc

    by_identity: dict[tuple[str, str, str], list[tuple[str, tuple[Path, ...]]]] = {}
    for fixture in manifest.trust_invariant_packet_fixtures:
        identity = (
            fixture.source_text_hash,
            fixture.core_ir_artifact_id,
            fixture.concept_artifact_id,
        )
        resolved_run_paths: list[Path] = []
        for run_path in sorted(run.trust_invariant_packet_path for run in fixture.runs):
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
            raise _semantics_v4_candidate_error(
                code="URM_ADEU_SEMANTICS_V4_FIXTURE_INVALID",
                reason=(
                    "trust-invariant fixture set contains duplicate fixture_id for pair identity"
                ),
                context={
                    "source_text_hash": identity[0],
                    "core_ir_artifact_id": identity[1],
                    "concept_artifact_id": identity[2],
                },
            )
        final_index[identity] = tuple(fixture_runs)
    return final_index


@lru_cache(maxsize=8)
def _semantics_fixture_index_for_manifest(
    manifest_path_value: str,
) -> dict[tuple[str, str, str], tuple[tuple[str, Path, Path], ...]]:
    manifest_path = Path(manifest_path_value)
    try:
        raw_payload = manifest_path.read_text(encoding="utf-8")
    except FileNotFoundError as exc:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_FIXTURE_INVALID",
            reason="vnext+23 stop-gate manifest fixture is missing",
            context={"path": str(manifest_path)},
        ) from exc
    except OSError as exc:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_FIXTURE_INVALID",
            reason="vnext+23 stop-gate manifest fixture is unreadable",
            context={"path": str(manifest_path), "error": str(exc)},
        ) from exc

    try:
        parsed = json.loads(raw_payload)
    except json.JSONDecodeError as exc:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_FIXTURE_INVALID",
            reason="vnext+23 stop-gate manifest JSON is invalid",
            context={"path": str(manifest_path), "error": exc.msg},
        ) from exc

    try:
        manifest = _VnextPlus23StopGateManifest.model_validate(parsed)
    except ValidationError as exc:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_FIXTURE_INVALID",
            reason="vnext+23 stop-gate manifest payload failed schema validation",
            context={"path": str(manifest_path), "error": str(exc)},
        ) from exc

    by_identity: dict[tuple[str, str, str], list[tuple[str, Path, Path]]] = {}
    for fixture in manifest.semantics_v4_candidate_packet_fixtures:
        identity = (
            fixture.source_text_hash,
            fixture.core_ir_artifact_id,
            fixture.concept_artifact_id,
        )

        baseline_path = Path(fixture.semantics_v3_path)
        if not baseline_path.is_absolute():
            baseline_path = manifest_path.parent / baseline_path
        candidate_path = Path(fixture.semantics_v4_candidate_path)
        if not candidate_path.is_absolute():
            candidate_path = manifest_path.parent / candidate_path

        by_identity.setdefault(identity, []).append(
            (fixture.fixture_id, baseline_path.resolve(), candidate_path.resolve())
        )

    final_index: dict[tuple[str, str, str], tuple[tuple[str, Path, Path], ...]] = {}
    for identity, fixture_items in by_identity.items():
        fixture_items = sorted(fixture_items, key=lambda item: item[0])
        fixture_ids = [fixture_id for fixture_id, _, _ in fixture_items]
        if len(set(fixture_ids)) != len(fixture_ids):
            raise _semantics_v4_candidate_error(
                code="URM_ADEU_SEMANTICS_V4_FIXTURE_INVALID",
                reason="semantics-v4 fixture set contains duplicate fixture_id for pair identity",
                context={
                    "source_text_hash": identity[0],
                    "core_ir_artifact_id": identity[1],
                    "concept_artifact_id": identity[2],
                },
            )
        if len(fixture_items) != 1:
            raise _semantics_v4_candidate_error(
                code="URM_ADEU_SEMANTICS_V4_FIXTURE_INVALID",
                reason=(
                    "semantics-v4 fixture set must resolve to exactly one baseline/candidate "
                    "artifact pair for pair identity"
                ),
                context={
                    "source_text_hash": identity[0],
                    "core_ir_artifact_id": identity[1],
                    "concept_artifact_id": identity[2],
                    "fixture_ids": fixture_ids,
                },
            )
        final_index[identity] = tuple(fixture_items)
    return final_index


def _load_and_validate_trust_payload(
    *,
    path: Path,
    source_text_hash: str,
    core_ir_artifact_id: str,
    concept_artifact_id: str,
) -> dict[str, Any]:
    try:
        raw_payload = path.read_text(encoding="utf-8")
    except FileNotFoundError as exc:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_ARTIFACT_NOT_FOUND",
            reason="matched trust-invariant packet artifact fixture is missing",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
            },
        ) from exc
    except OSError as exc:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_FIXTURE_INVALID",
            reason="matched trust-invariant packet artifact fixture is unreadable",
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
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID",
            reason="matched trust-invariant packet artifact JSON is invalid",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
                "error": exc.msg,
            },
        ) from exc

    if not isinstance(parsed, dict) or not parsed:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID",
            reason="matched trust-invariant packet artifact payload must be a non-empty object",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
            },
        )

    try:
        normalized = AdeuTrustInvariantPacket.model_validate(parsed)
    except ValidationError as exc:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID",
            reason="matched trust-invariant packet payload failed schema validation",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
                "error": str(exc),
            },
        ) from exc

    payload = normalized.model_dump(mode="json", by_alias=True, exclude_none=True)
    if payload.get("source_text_hash") != source_text_hash:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID",
            reason="trust-invariant payload source_text_hash does not match pair identity",
            context={
                "source_text_hash": source_text_hash,
                "payload_source_text_hash": payload.get("source_text_hash"),
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
            },
        )
    if payload.get("core_ir_artifact_id") != core_ir_artifact_id:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID",
            reason="trust-invariant payload core_ir_artifact_id does not match pair identity",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "payload_core_ir_artifact_id": payload.get("core_ir_artifact_id"),
                "concept_artifact_id": concept_artifact_id,
            },
        )
    if payload.get("concept_artifact_id") != concept_artifact_id:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID",
            reason="trust-invariant payload concept_artifact_id does not match pair identity",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "payload_concept_artifact_id": payload.get("concept_artifact_id"),
            },
        )
    return payload


def _load_and_validate_semantics_payload(
    *,
    path: Path,
    source_text_hash: str,
    core_ir_artifact_id: str,
    concept_artifact_id: str,
    payload_label: str,
) -> dict[str, Any]:
    try:
        raw_payload = path.read_text(encoding="utf-8")
    except FileNotFoundError as exc:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_ARTIFACT_NOT_FOUND",
            reason=f"matched {payload_label} semantics artifact fixture is missing",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
            },
        ) from exc
    except OSError as exc:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_FIXTURE_INVALID",
            reason=f"matched {payload_label} semantics artifact fixture is unreadable",
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
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID",
            reason=f"matched {payload_label} semantics artifact JSON is invalid",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
                "error": exc.msg,
            },
        ) from exc

    if not isinstance(parsed, dict) or not parsed:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID",
            reason=f"matched {payload_label} semantics artifact payload must be a non-empty object",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
            },
        )

    try:
        normalized = _SemanticsDiagnosticsPayload.model_validate(parsed)
    except ValidationError as exc:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID",
            reason=f"matched {payload_label} semantics payload failed schema validation",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
                "error": str(exc),
            },
        ) from exc

    payload = normalized.model_dump(mode="json", by_alias=True, exclude_none=True)

    recomputed_hash = _semantics_diagnostics_hash(payload)
    embedded_hash = str(payload.get("semantics_diagnostics_hash") or "")
    if recomputed_hash != embedded_hash:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID",
            reason=(
                f"{payload_label} semantics_diagnostics_hash does not match "
                "recomputed canonical hash"
            ),
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "path": str(path),
                "expected_hash": recomputed_hash,
                "observed_hash": embedded_hash,
            },
        )

    return payload


def _trust_payload_for_pair(
    *,
    source_text_hash: str,
    core_ir_artifact_id: str,
    concept_artifact_id: str,
    trust_manifest_path: Path | None = None,
) -> dict[str, Any]:
    manifest_path = _resolved_manifest_path(
        trust_manifest_path,
        default=VNEXT_PLUS22_STOP_GATE_MANIFEST_PATH,
    )
    identity = (source_text_hash, core_ir_artifact_id, concept_artifact_id)
    by_identity = _trust_packet_fixture_index_for_manifest(str(manifest_path))
    fixture_runs = by_identity.get(identity)
    if fixture_runs is None:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_ARTIFACT_NOT_FOUND",
            reason="matched trust-invariant packet artifact not found for pair identity",
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
        payload = _load_and_validate_trust_payload(
            path=packet_path,
            source_text_hash=source_text_hash,
            core_ir_artifact_id=core_ir_artifact_id,
            concept_artifact_id=concept_artifact_id,
        )
        path_key = str(packet_path)
        payload_by_path[path_key] = payload
        hash_by_path[path_key] = _sha256_created_at_stripped(payload)

    if len(set(hash_by_path.values())) > 1:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_DIAGNOSTIC_DRIFT",
            reason="trust-invariant replay run payloads drift for pair identity",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "selected_fixture_id": selected_fixture_id,
                "trust_packet_run_hashes_by_path": hash_by_path,
            },
        )

    selected_path = min(payload_by_path.keys())
    return payload_by_path[selected_path]


def _semantics_payloads_for_pair(
    *,
    source_text_hash: str,
    core_ir_artifact_id: str,
    concept_artifact_id: str,
    semantics_manifest_path: Path | None = None,
) -> tuple[dict[str, Any], dict[str, Any]]:
    manifest_path = _resolved_manifest_path(
        semantics_manifest_path,
        default=VNEXT_PLUS23_STOP_GATE_MANIFEST_PATH,
    )
    identity = (source_text_hash, core_ir_artifact_id, concept_artifact_id)
    by_identity = _semantics_fixture_index_for_manifest(str(manifest_path))
    fixture_paths = by_identity.get(identity)
    if fixture_paths is None:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_ARTIFACT_NOT_FOUND",
            reason="matched semantics-v4 candidate artifact not found for pair identity",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "manifest_path": str(manifest_path),
            },
        )

    _, baseline_path, candidate_path = fixture_paths[0]

    baseline_payload = _load_and_validate_semantics_payload(
        path=baseline_path,
        source_text_hash=source_text_hash,
        core_ir_artifact_id=core_ir_artifact_id,
        concept_artifact_id=concept_artifact_id,
        payload_label="baseline",
    )
    candidate_payload = _load_and_validate_semantics_payload(
        path=candidate_path,
        source_text_hash=source_text_hash,
        core_ir_artifact_id=core_ir_artifact_id,
        concept_artifact_id=concept_artifact_id,
        payload_label="candidate",
    )

    baseline_artifact_ref = str(baseline_payload.get("artifact_ref") or "")
    candidate_artifact_ref = str(candidate_payload.get("artifact_ref") or "")
    if baseline_artifact_ref != candidate_artifact_ref:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID",
            reason="baseline and candidate semantics payloads must share identical artifact_ref",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "baseline_artifact_ref": baseline_artifact_ref,
                "candidate_artifact_ref": candidate_artifact_ref,
            },
        )

    return baseline_payload, candidate_payload


def _status_keys(payload: Mapping[str, Any]) -> list[str]:
    records = payload.get("records")
    if not isinstance(records, list):
        return []

    keys: list[str] = []
    for record in records:
        if not isinstance(record, Mapping):
            continue
        status = str(record.get("status") or "")
        if status not in _STATUS_VALUES:
            continue
        keys.append(_STATUS_TOKEN_NORMALIZATION.get(status, status))
    return sorted(keys)


def _assurance_keys(payload: Mapping[str, Any]) -> list[str]:
    records = payload.get("records")
    if not isinstance(records, list):
        return []

    keys: list[str] = []
    for record in records:
        if not isinstance(record, Mapping):
            continue
        assurance = str(record.get("assurance") or "")
        if assurance not in _ASSURANCE_VALUES:
            continue
        keys.append(assurance)
    return sorted(keys)


def _request_formula_keys(payload: Mapping[str, Any]) -> list[tuple[str, str]]:
    records = payload.get("records")
    if not isinstance(records, list):
        return []

    keys: list[tuple[str, str]] = []
    for record in records:
        if not isinstance(record, Mapping):
            continue
        request_hash = str(record.get("request_hash") or "")
        formula_hash = str(record.get("formula_hash") or "")
        keys.append((request_hash, formula_hash))
    return sorted(keys)


def _witness_keys(payload: Mapping[str, Any]) -> list[tuple[str, str, str]]:
    records = payload.get("records")
    if not isinstance(records, list):
        return []

    keys: list[tuple[str, str, str]] = []
    for record in records:
        if not isinstance(record, Mapping):
            continue
        witness_refs = record.get("witness_refs")
        if not isinstance(witness_refs, list):
            continue
        deduped_within_record: set[tuple[str, str, str]] = set()
        for witness_ref in witness_refs:
            if not isinstance(witness_ref, Mapping):
                continue
            assertion_name = str(witness_ref.get("assertion_name") or "")
            object_id_raw = witness_ref.get("object_id")
            json_path_raw = witness_ref.get("json_path")
            object_id = "" if object_id_raw is None else str(object_id_raw)
            json_path = "" if json_path_raw is None else str(json_path_raw)
            deduped_within_record.add((assertion_name, object_id, json_path))
        keys.extend(sorted(deduped_within_record))
    return sorted(keys)


def _comparison_status_and_severity(
    *,
    comparison_code: str,
    baseline_keys: list[Any],
    candidate_keys: list[Any],
) -> tuple[str, str]:
    status = "compatible" if baseline_keys == candidate_keys else "drift"
    severity = _COMPARISON_SEVERITY_BY_CODE_STATUS[(comparison_code, status)]
    return status, severity


def _hash_key_payload(
    *,
    comparison_code: str,
    keys: list[Any],
) -> list[Any]:
    if comparison_code in {
        _STATUS_SET_CONTINUITY_REVIEW,
        _ASSURANCE_SET_CONTINUITY_REVIEW,
    }:
        return [str(value) for value in keys]
    if comparison_code == _REQUEST_FORMULA_HASH_CONTINUITY_REVIEW:
        return [[str(item[0]), str(item[1])] for item in keys]
    if comparison_code == _WITNESS_REF_STRUCTURE_REVIEW:
        return [[str(item[0]), str(item[1]), str(item[2])] for item in keys]
    raise _semantics_v4_candidate_error(
        code="URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID",
        reason="unsupported comparison_code for hash-key payload projection",
        context={"comparison_code": comparison_code},
    )


def _build_comparison_item(
    *,
    comparison_code: str,
    baseline_keys: list[Any],
    candidate_keys: list[Any],
    justification_refs: list[str],
) -> dict[str, Any]:
    status, severity = _comparison_status_and_severity(
        comparison_code=comparison_code,
        baseline_keys=baseline_keys,
        candidate_keys=candidate_keys,
    )

    expected_hash: str | None
    observed_hash: str | None
    if status == "drift":
        expected_hash = sha256_text(
            canonical_json(_hash_key_payload(comparison_code=comparison_code, keys=baseline_keys))
        )
        observed_hash = sha256_text(
            canonical_json(_hash_key_payload(comparison_code=comparison_code, keys=candidate_keys))
        )
    else:
        expected_hash = None
        observed_hash = None

    refs = sorted(justification_refs)
    item: dict[str, Any] = {
        "comparison_id": build_semantics_v4_candidate_comparison_id(
            comparison_code=comparison_code,
            status=status,
            severity=severity,
            justification_refs=refs,
            expected_hash=expected_hash,
            observed_hash=observed_hash,
        ),
        "comparison_code": comparison_code,
        "status": status,
        "severity": severity,
        "justification_refs": refs,
        "message": _COMPARISON_MESSAGE_BY_CODE[comparison_code],
    }
    if expected_hash is not None:
        item["expected_hash"] = expected_hash
    if observed_hash is not None:
        item["observed_hash"] = observed_hash
    return item


def build_semantics_v4_candidate_packet_vnext_plus23(
    *,
    source_text_hash: str,
    core_ir_artifact_id: str,
    concept_artifact_id: str,
    catalog_path: Path | None = None,
    trust_manifest_path: Path | None = None,
    semantics_manifest_path: Path | None = None,
) -> dict[str, Any]:
    _require_semantics_v4_candidate_non_enforcement_context(
        operation="build_semantics_v4_candidate_packet_vnext_plus23"
    )

    try:
        build_cross_ir_bridge_manifest_vnext_plus20(
            source_text_hash=source_text_hash,
            core_ir_artifact_id=core_ir_artifact_id,
            concept_artifact_id=concept_artifact_id,
            catalog_path=catalog_path,
        )
    except CrossIRBridgeVnextPlus20Error as exc:
        raise _cross_ir_error_to_semantics_v4(exc) from exc

    trust_payload = _trust_payload_for_pair(
        source_text_hash=source_text_hash,
        core_ir_artifact_id=core_ir_artifact_id,
        concept_artifact_id=concept_artifact_id,
        trust_manifest_path=trust_manifest_path,
    )
    baseline_payload, candidate_payload = _semantics_payloads_for_pair(
        source_text_hash=source_text_hash,
        core_ir_artifact_id=core_ir_artifact_id,
        concept_artifact_id=concept_artifact_id,
        semantics_manifest_path=semantics_manifest_path,
    )

    trust_hash = _sha256_created_at_stripped(trust_payload)
    baseline_hash = _sha256_created_at_stripped(baseline_payload)
    candidate_hash = _sha256_created_at_stripped(candidate_payload)

    trust_ref = _artifact_ref(
        schema="adeu_trust_invariant_packet@0.1",
        source_text_hash=source_text_hash,
        core_ir_artifact_id=core_ir_artifact_id,
        concept_artifact_id=concept_artifact_id,
    )
    v3_ref = _artifact_ref(
        schema="semantics_diagnostics@1",
        lane="v3",
        source_text_hash=source_text_hash,
        core_ir_artifact_id=core_ir_artifact_id,
        concept_artifact_id=concept_artifact_id,
    )
    v4_ref = _artifact_ref(
        schema="semantics_diagnostics@1",
        lane="v4_candidate",
        source_text_hash=source_text_hash,
        core_ir_artifact_id=core_ir_artifact_id,
        concept_artifact_id=concept_artifact_id,
    )

    comparison_items = [
        _build_comparison_item(
            comparison_code=_STATUS_SET_CONTINUITY_REVIEW,
            baseline_keys=_status_keys(baseline_payload),
            candidate_keys=_status_keys(candidate_payload),
            justification_refs=[v3_ref, v4_ref],
        ),
        _build_comparison_item(
            comparison_code=_ASSURANCE_SET_CONTINUITY_REVIEW,
            baseline_keys=_assurance_keys(baseline_payload),
            candidate_keys=_assurance_keys(candidate_payload),
            justification_refs=[v3_ref, v4_ref],
        ),
        _build_comparison_item(
            comparison_code=_REQUEST_FORMULA_HASH_CONTINUITY_REVIEW,
            baseline_keys=_request_formula_keys(baseline_payload),
            candidate_keys=_request_formula_keys(candidate_payload),
            justification_refs=[v3_ref, v4_ref],
        ),
        _build_comparison_item(
            comparison_code=_WITNESS_REF_STRUCTURE_REVIEW,
            baseline_keys=_witness_keys(baseline_payload),
            candidate_keys=_witness_keys(candidate_payload),
            justification_refs=[trust_ref, v3_ref, v4_ref],
        ),
    ]

    comparison_items = sorted(
        comparison_items,
        key=lambda item: (str(item["comparison_code"]), str(item["comparison_id"])),
    )

    status_counts = Counter(str(item["status"]) for item in comparison_items)
    code_counts = Counter(str(item["comparison_code"]) for item in comparison_items)
    severity_counts = Counter(str(item["severity"]) for item in comparison_items)

    packet_payload = {
        "schema": SEMANTICS_V4_CANDIDATE_PACKET_SCHEMA,
        "source_text_hash": source_text_hash,
        "core_ir_artifact_id": core_ir_artifact_id,
        "concept_artifact_id": concept_artifact_id,
        "trust_invariant_packet_hash": trust_hash,
        "baseline_semantics_hash": baseline_hash,
        "candidate_semantics_hash": candidate_hash,
        "comparison_summary": {
            "total_comparisons": len(comparison_items),
            "compatible_checks": status_counts.get("compatible", 0),
            "drift_checks": status_counts.get("drift", 0),
            "counts_by_code": {code: code_counts[code] for code in sorted(code_counts)},
            "counts_by_severity": {
                severity: severity_counts[severity]
                for severity in sorted(severity_counts)
            },
            "counts_by_status": {
                status: status_counts[status]
                for status in sorted(status_counts)
            },
        },
        "comparison_items": comparison_items,
    }

    try:
        normalized = AdeuSemanticsV4CandidatePacket.model_validate(packet_payload)
    except ValidationError as exc:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID",
            reason="semantics-v4 candidate packet payload failed schema validation",
            context={
                "source_text_hash": source_text_hash,
                "core_ir_artifact_id": core_ir_artifact_id,
                "concept_artifact_id": concept_artifact_id,
                "error": str(exc),
            },
        ) from exc

    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


def build_semantics_v4_candidate_projection_vnext_plus23(
    *,
    catalog_path: Path | None = None,
    trust_manifest_path: Path | None = None,
    semantics_manifest_path: Path | None = None,
) -> SemanticsV4CandidateProjectionVnextPlus23:
    _require_semantics_v4_candidate_non_enforcement_context(
        operation="build_semantics_v4_candidate_projection_vnext_plus23"
    )
    try:
        pairs = list_cross_ir_catalog_pairs_vnext_plus20(catalog_path=catalog_path)
    except CrossIRBridgeVnextPlus20Error as exc:
        raise _cross_ir_error_to_semantics_v4(exc) from exc

    pair_tuples: list[tuple[str, str, str]] = []
    for pair in pairs:
        source_text_hash = pair.get("source_text_hash")
        core_ir_artifact_id = pair.get("core_ir_artifact_id")
        concept_artifact_id = pair.get("concept_artifact_id")
        if (
            not isinstance(source_text_hash, str)
            or not source_text_hash
            or not isinstance(core_ir_artifact_id, str)
            or not core_ir_artifact_id
            or not isinstance(concept_artifact_id, str)
            or not concept_artifact_id
        ):
            raise _semantics_v4_candidate_error(
                code="URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID",
                reason="catalog pair entry is invalid for semantics-v4 candidate projection",
                context={"pair": dict(pair)},
            )
        pair_tuples.append((source_text_hash, core_ir_artifact_id, concept_artifact_id))

    pair_tuples = sorted(pair_tuples)

    comparison_item_count = 0
    comparison_counts_by_code: Counter[str] = Counter()
    comparison_counts_by_status: Counter[str] = Counter()
    comparison_counts_by_severity: Counter[str] = Counter()
    for source_text_hash, core_ir_artifact_id, concept_artifact_id in pair_tuples:
        packet = build_semantics_v4_candidate_packet_vnext_plus23(
            source_text_hash=source_text_hash,
            core_ir_artifact_id=core_ir_artifact_id,
            concept_artifact_id=concept_artifact_id,
            catalog_path=catalog_path,
            trust_manifest_path=trust_manifest_path,
            semantics_manifest_path=semantics_manifest_path,
        )
        comparison_items = packet["comparison_items"]
        comparison_item_count += len(comparison_items)
        for comparison_item in comparison_items:
            comparison_counts_by_code[str(comparison_item["comparison_code"])] += 1
            comparison_counts_by_status[str(comparison_item["status"])] += 1
            comparison_counts_by_severity[str(comparison_item["severity"])] += 1

    projection_payload = {
        "schema": SEMANTICS_V4_CANDIDATE_PROJECTION_SCHEMA,
        "bridge_pair_count": len(pair_tuples),
        "comparison_item_count": comparison_item_count,
        "comparison_counts_by_code": {
            code: comparison_counts_by_code[code] for code in sorted(comparison_counts_by_code)
        },
        "comparison_counts_by_status": {
            status: comparison_counts_by_status[status]
            for status in sorted(comparison_counts_by_status)
        },
        "comparison_counts_by_severity": {
            severity: comparison_counts_by_severity[severity]
            for severity in sorted(comparison_counts_by_severity)
        },
    }
    try:
        normalized = SemanticsV4CandidateProjectionVnextPlus23.model_validate(projection_payload)
    except ValidationError as exc:
        raise _semantics_v4_candidate_error(
            code="URM_ADEU_SEMANTICS_V4_PAYLOAD_INVALID",
            reason="semantics-v4 candidate projection payload failed schema validation",
            context={"error": str(exc)},
        ) from exc
    return normalized
