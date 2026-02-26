from __future__ import annotations

import json
import re
from collections import Counter
from collections.abc import Iterator, Mapping
from contextlib import contextmanager
from contextvars import ContextVar
from functools import lru_cache
from pathlib import Path
from typing import Any, Literal, NamedTuple, cast

from adeu_core_ir import (
    AdeuProjectionAlignment,
    AdeuProjectionAlignmentFidelity,
    AdeuProjectionAlignmentFidelityInput,
    build_projection_alignment_fidelity_id,
)
from pydantic import BaseModel, ConfigDict, Field, model_validator

from .hashing import canonical_json, sha256_text, strip_created_at_recursive

VNEXT_PLUS24_CATALOG_SCHEMA = "extraction_fidelity.vnext_plus24_catalog@1"
VNEXT_PLUS24_CATALOG_PATH = (
    Path(__file__).resolve().parents[2]
    / "fixtures"
    / "extraction_fidelity"
    / "vnext_plus24_catalog.json"
)

_EXTRACTION_FIDELITY_PACKET_SCHEMA = "adeu_projection_alignment_fidelity@0.1"
_EXTRACTION_FIDELITY_PROJECTION_SCHEMA = "projection_alignment_fidelity_projection.vnext_plus24@1"
_ADEU_PROJECTION_ALIGNMENT_SCHEMA = "adeu_projection_alignment@0.1"
_ADEU_PROJECTION_ALIGNMENT_FIDELITY_INPUT_SCHEMA = "adeu_projection_alignment_fidelity_input@0.1"
_FROZEN_FIDELITY_CODES = (
    "label_text_mismatch",
    "span_mismatch",
    "score_mismatch",
)
_FROZEN_FIDELITY_STATUSES = ("compatible", "drift")
_FROZEN_FIDELITY_SEVERITIES = ("high", "low", "medium")
_SCORE_DELTA_MILLI_THRESHOLD = 50
_ASCII_WHITESPACE_RE = re.compile(r"[ \t\n\r\f\v]+")
_EXTRACTION_FIDELITY_NON_ENFORCEMENT_CONTEXT: ContextVar[bool] = ContextVar(
    "extraction_fidelity_non_enforcement_context",
    default=False,
)


class ExtractionFidelityVnextPlus24Error(ValueError):
    def __init__(self, *, code: str, reason: str, context: Mapping[str, Any] | None = None) -> None:
        super().__init__(reason)
        self.code = code
        self.reason = reason
        self.context = dict(context or {})


class ExtractionFidelityCatalogEntry(BaseModel):
    model_config = ConfigDict(extra="forbid")

    source_text_hash: str = Field(min_length=1)
    projection_alignment_path: str = Field(min_length=1)
    projection_alignment_fidelity_input_path: str = Field(min_length=1)
    created_at: str | None = None
    domain_id: str | None = None
    document_ref: str | None = None


class ExtractionFidelityCatalog(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: Literal["extraction_fidelity.vnext_plus24_catalog@1"] = VNEXT_PLUS24_CATALOG_SCHEMA
    entries: list[ExtractionFidelityCatalogEntry] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "ExtractionFidelityCatalog":
        source_hashes = [entry.source_text_hash for entry in self.entries]
        if source_hashes != sorted(source_hashes):
            raise ValueError("catalog entries must be sorted by source_text_hash")
        return self


class ProjectionAlignmentFidelityProjectionVnextPlus24(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: Literal["projection_alignment_fidelity_projection.vnext_plus24@1"] = (
        _EXTRACTION_FIDELITY_PROJECTION_SCHEMA
    )
    source_count: int = Field(ge=0)
    fidelity_item_count: int = Field(ge=0)
    fidelity_counts_by_code: dict[str, int] = Field(default_factory=dict)
    fidelity_counts_by_status: dict[str, int] = Field(default_factory=dict)
    fidelity_counts_by_severity: dict[str, int] = Field(default_factory=dict)

    @model_validator(mode="after")
    def _validate_contract(self) -> "ProjectionAlignmentFidelityProjectionVnextPlus24":
        for field_name, valid_keys, unsupported_key_error in (
            (
                "fidelity_counts_by_code",
                set(_FROZEN_FIDELITY_CODES),
                "fidelity_counts_by_code contains unsupported fidelity_code",
            ),
            (
                "fidelity_counts_by_status",
                set(_FROZEN_FIDELITY_STATUSES),
                "fidelity_counts_by_status contains unsupported status value",
            ),
            (
                "fidelity_counts_by_severity",
                set(_FROZEN_FIDELITY_SEVERITIES),
                "fidelity_counts_by_severity contains unsupported severity value",
            ),
        ):
            counts_dict = cast(dict[str, int], getattr(self, field_name))
            if list(counts_dict.keys()) != sorted(counts_dict.keys()):
                raise ValueError(f"{field_name} keys must be lexicographically sorted")
            if any(key not in valid_keys for key in counts_dict):
                raise ValueError(unsupported_key_error)
            if any(value < 0 for value in counts_dict.values()):
                raise ValueError(f"{field_name} values must be non-negative integers")

        if self.fidelity_item_count != sum(self.fidelity_counts_by_code.values()):
            raise ValueError(
                "fidelity_item_count must equal sum(fidelity_counts_by_code.values())"
            )
        if self.fidelity_item_count != sum(self.fidelity_counts_by_status.values()):
            raise ValueError(
                "fidelity_item_count must equal sum(fidelity_counts_by_status.values())"
            )
        if self.fidelity_item_count != sum(self.fidelity_counts_by_severity.values()):
            raise ValueError(
                "fidelity_item_count must equal sum(fidelity_counts_by_severity.values())"
            )
        return self


class ExtractionFidelitySourceArtifactsVnextPlus24(NamedTuple):
    source_text_hash: str
    projection_alignment_path: Path
    projection_alignment_payload: dict[str, Any]
    projection_alignment_fidelity_input_path: Path
    projection_alignment_fidelity_input_payload: dict[str, Any]


class _ExtractionFidelityCatalogIndex(NamedTuple):
    catalog_path: Path
    entries_by_source_text_hash: dict[str, ExtractionFidelityCatalogEntry]


def _extraction_fidelity_error(
    *,
    code: str,
    reason: str,
    context: Mapping[str, Any] | None = None,
) -> ExtractionFidelityVnextPlus24Error:
    return ExtractionFidelityVnextPlus24Error(code=code, reason=reason, context=context)


@contextmanager
def extraction_fidelity_non_enforcement_context() -> Iterator[None]:
    token = _EXTRACTION_FIDELITY_NON_ENFORCEMENT_CONTEXT.set(True)
    try:
        yield
    finally:
        _EXTRACTION_FIDELITY_NON_ENFORCEMENT_CONTEXT.reset(token)


def _require_extraction_fidelity_non_enforcement_context(*, operation: str) -> None:
    if _EXTRACTION_FIDELITY_NON_ENFORCEMENT_CONTEXT.get():
        return
    raise _extraction_fidelity_error(
        code="URM_ADEU_EXTRACTION_FIDELITY_REQUEST_INVALID",
        reason="extraction-fidelity runtime non-enforcement context is not active",
        context={"operation": operation},
    )


def _resolved_catalog_path(catalog_path: Path | None) -> Path:
    selected = VNEXT_PLUS24_CATALOG_PATH if catalog_path is None else Path(catalog_path)
    return selected.resolve()


def _resolve_artifact_path(*, catalog_path: Path, artifact_path: str) -> Path:
    candidate = Path(artifact_path)
    if not candidate.is_absolute():
        candidate = catalog_path.parent / candidate
    return candidate.resolve()


def _read_json_object(
    *,
    path: Path,
    not_found_code: str,
    not_found_reason: str,
    invalid_code: str,
    invalid_reason: str,
    context: Mapping[str, Any],
) -> dict[str, Any]:
    try:
        raw = path.read_text(encoding="utf-8")
    except (FileNotFoundError, OSError) as exc:
        raise _extraction_fidelity_error(
            code=not_found_code,
            reason=not_found_reason,
            context={
                **context,
                "path": str(path),
                "error": str(exc),
            },
        ) from exc

    try:
        payload = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise _extraction_fidelity_error(
            code=invalid_code,
            reason=invalid_reason,
            context={
                **context,
                "path": str(path),
                "error": exc.msg,
            },
        ) from exc

    if not isinstance(payload, dict):
        raise _extraction_fidelity_error(
            code=invalid_code,
            reason=f"{invalid_reason} (payload must be an object)",
            context={
                **context,
                "path": str(path),
            },
        )
    return payload


@lru_cache(maxsize=8)
def _catalog_index_for_path(catalog_path_value: str) -> _ExtractionFidelityCatalogIndex:
    catalog_path = Path(catalog_path_value)
    parsed = _read_json_object(
        path=catalog_path,
        not_found_code="URM_ADEU_EXTRACTION_FIDELITY_FIXTURE_INVALID",
        not_found_reason="extraction-fidelity catalog fixture is missing",
        invalid_code="URM_ADEU_EXTRACTION_FIDELITY_FIXTURE_INVALID",
        invalid_reason="extraction-fidelity catalog JSON is invalid",
        context={},
    )

    try:
        catalog = ExtractionFidelityCatalog.model_validate(parsed)
    except Exception as exc:
        raise _extraction_fidelity_error(
            code="URM_ADEU_EXTRACTION_FIDELITY_FIXTURE_INVALID",
            reason="extraction-fidelity catalog payload failed schema validation",
            context={"path": str(catalog_path), "error": str(exc)},
        ) from exc

    entries_by_source_text_hash: dict[str, ExtractionFidelityCatalogEntry] = {}
    for entry in catalog.entries:
        if entry.source_text_hash in entries_by_source_text_hash:
            raise _extraction_fidelity_error(
                code="URM_ADEU_EXTRACTION_FIDELITY_REQUEST_INVALID",
                reason="catalog contains duplicate source_text_hash entries",
                context={
                    "path": str(catalog_path),
                    "source_text_hash": entry.source_text_hash,
                },
            )
        entries_by_source_text_hash[entry.source_text_hash] = entry

    return _ExtractionFidelityCatalogIndex(
        catalog_path=catalog_path,
        entries_by_source_text_hash=entries_by_source_text_hash,
    )


def _catalog_index(*, catalog_path: Path | None = None) -> _ExtractionFidelityCatalogIndex:
    resolved_catalog_path = _resolved_catalog_path(catalog_path)
    return _catalog_index_for_path(str(resolved_catalog_path))


def _sha256_created_at_stripped(
    payload: Mapping[str, Any],
    *,
    top_level_excluded_fields: tuple[str, ...] = (),
) -> str:
    normalized_payload = strip_created_at_recursive(payload)
    if isinstance(normalized_payload, Mapping):
        filtered_payload: dict[str, Any] = {}
        for key in sorted(str(item) for item in normalized_payload.keys()):
            if key in top_level_excluded_fields:
                continue
            filtered_payload[key] = normalized_payload[key]
        normalized_payload = filtered_payload
    return sha256_text(canonical_json(normalized_payload))


def _normalize_label_text(value: str) -> str:
    trimmed = value.strip(" \t\n\r\f\v")
    return _ASCII_WHITESPACE_RE.sub(" ", trimmed)


def _justification_refs(*, source_text_hash: str) -> list[str]:
    refs = [
        f"artifact:adeu_projection_alignment@0.1:{source_text_hash}",
        (f"artifact:adeu_projection_alignment_fidelity_input@0.1:{source_text_hash}"),
    ]
    return sorted(refs)


def _status_for_score_mismatch(*, projection_keys: list[int], extraction_keys: list[int]) -> str:
    for projection_score, extraction_score in zip(projection_keys, extraction_keys):
        if abs(projection_score - extraction_score) > _SCORE_DELTA_MILLI_THRESHOLD:
            return "drift"
    return "compatible"


def _severity_for_item(*, fidelity_code: str, status: str) -> str:
    if fidelity_code == "span_mismatch":
        return "low" if status == "compatible" else "high"
    if fidelity_code == "label_text_mismatch":
        return "low" if status == "compatible" else "medium"
    return "low" if status == "compatible" else "medium"


def _fidelity_item(
    *,
    source_text_hash: str,
    fidelity_code: str,
    projection_keys: list[Any],
    extraction_keys: list[Any],
    message: str,
) -> dict[str, Any]:
    if fidelity_code == "score_mismatch":
        status = _status_for_score_mismatch(
            projection_keys=projection_keys,
            extraction_keys=extraction_keys,
        )
    else:
        status = "compatible" if projection_keys == extraction_keys else "drift"
    severity = _severity_for_item(fidelity_code=fidelity_code, status=status)

    expected_hash: str | None = None
    observed_hash: str | None = None
    if status == "drift":
        expected_hash = sha256_text(canonical_json(projection_keys))
        observed_hash = sha256_text(canonical_json(extraction_keys))

    justification_refs = _justification_refs(source_text_hash=source_text_hash)
    fidelity_id = build_projection_alignment_fidelity_id(
        fidelity_code=fidelity_code,
        status=status,
        severity=severity,
        justification_refs=justification_refs,
        expected_hash=expected_hash,
        observed_hash=observed_hash,
    )

    payload: dict[str, Any] = {
        "fidelity_id": fidelity_id,
        "fidelity_code": fidelity_code,
        "status": status,
        "severity": severity,
        "justification_refs": justification_refs,
        "message": message,
    }
    if expected_hash is not None:
        payload["expected_hash"] = expected_hash
    if observed_hash is not None:
        payload["observed_hash"] = observed_hash
    return payload


def load_extraction_fidelity_source_artifacts_vnext_plus24(
    *,
    source_text_hash: str,
    catalog_path: Path | None = None,
) -> ExtractionFidelitySourceArtifactsVnextPlus24:
    index = _catalog_index(catalog_path=catalog_path)
    entry = index.entries_by_source_text_hash.get(source_text_hash)
    if entry is None:
        raise _extraction_fidelity_error(
            code="URM_ADEU_EXTRACTION_FIDELITY_ARTIFACT_NOT_FOUND",
            reason="source_text_hash not found in extraction-fidelity catalog",
            context={"source_text_hash": source_text_hash},
        )

    projection_alignment_path = _resolve_artifact_path(
        catalog_path=index.catalog_path,
        artifact_path=entry.projection_alignment_path,
    )
    projection_alignment_payload = _read_json_object(
        path=projection_alignment_path,
        not_found_code="URM_ADEU_EXTRACTION_FIDELITY_ARTIFACT_NOT_FOUND",
        not_found_reason="projection-alignment artifact is missing",
        invalid_code="URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID",
        invalid_reason="projection-alignment artifact JSON is invalid",
        context={"source_text_hash": source_text_hash},
    )

    fidelity_input_path = _resolve_artifact_path(
        catalog_path=index.catalog_path,
        artifact_path=entry.projection_alignment_fidelity_input_path,
    )
    fidelity_input_payload = _read_json_object(
        path=fidelity_input_path,
        not_found_code="URM_ADEU_EXTRACTION_FIDELITY_ARTIFACT_NOT_FOUND",
        not_found_reason="projection-alignment-fidelity input artifact is missing",
        invalid_code="URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID",
        invalid_reason="projection-alignment-fidelity input artifact JSON is invalid",
        context={"source_text_hash": source_text_hash},
    )

    if projection_alignment_payload.get("schema") != _ADEU_PROJECTION_ALIGNMENT_SCHEMA:
        raise _extraction_fidelity_error(
            code="URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID",
            reason="projection-alignment payload schema mismatch",
            context={
                "source_text_hash": source_text_hash,
                "path": str(projection_alignment_path),
                "payload_schema": projection_alignment_payload.get("schema"),
            },
        )
    if fidelity_input_payload.get("schema") != _ADEU_PROJECTION_ALIGNMENT_FIDELITY_INPUT_SCHEMA:
        raise _extraction_fidelity_error(
            code="URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID",
            reason="projection-alignment-fidelity-input payload schema mismatch",
            context={
                "source_text_hash": source_text_hash,
                "path": str(fidelity_input_path),
                "payload_schema": fidelity_input_payload.get("schema"),
            },
        )

    try:
        normalized_alignment_payload = AdeuProjectionAlignment.model_validate(
            projection_alignment_payload
        ).model_dump(mode="json", by_alias=True, exclude_none=True)
    except Exception as exc:
        raise _extraction_fidelity_error(
            code="URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID",
            reason="projection-alignment payload failed schema validation",
            context={
                "source_text_hash": source_text_hash,
                "path": str(projection_alignment_path),
                "error": str(exc),
            },
        ) from exc

    try:
        normalized_fidelity_input_payload = AdeuProjectionAlignmentFidelityInput.model_validate(
            fidelity_input_payload
        ).model_dump(mode="json", by_alias=True, exclude_none=True)
    except Exception as exc:
        raise _extraction_fidelity_error(
            code="URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID",
            reason="projection-alignment-fidelity-input payload failed schema validation",
            context={
                "source_text_hash": source_text_hash,
                "path": str(fidelity_input_path),
                "error": str(exc),
            },
        ) from exc

    if normalized_alignment_payload.get("source_text_hash") != source_text_hash:
        raise _extraction_fidelity_error(
            code="URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID",
            reason="projection-alignment payload source_text_hash mismatch",
            context={
                "source_text_hash": source_text_hash,
                "projection_alignment_source_text_hash": normalized_alignment_payload.get(
                    "source_text_hash"
                ),
                "path": str(projection_alignment_path),
            },
        )

    if normalized_fidelity_input_payload.get("source_text_hash") != source_text_hash:
        raise _extraction_fidelity_error(
            code="URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID",
            reason="projection-alignment-fidelity-input payload source_text_hash mismatch",
            context={
                "source_text_hash": source_text_hash,
                "fidelity_input_source_text_hash": normalized_fidelity_input_payload.get(
                    "source_text_hash"
                ),
                "path": str(fidelity_input_path),
            },
        )

    return ExtractionFidelitySourceArtifactsVnextPlus24(
        source_text_hash=source_text_hash,
        projection_alignment_path=projection_alignment_path,
        projection_alignment_payload=normalized_alignment_payload,
        projection_alignment_fidelity_input_path=fidelity_input_path,
        projection_alignment_fidelity_input_payload=normalized_fidelity_input_payload,
    )


def build_extraction_fidelity_packet_vnext_plus24(
    *,
    source_text_hash: str,
    catalog_path: Path | None = None,
) -> dict[str, Any]:
    _require_extraction_fidelity_non_enforcement_context(
        operation="build_extraction_fidelity_packet_vnext_plus24"
    )

    artifacts = load_extraction_fidelity_source_artifacts_vnext_plus24(
        source_text_hash=source_text_hash,
        catalog_path=catalog_path,
    )
    matched_nodes = sorted(
        artifacts.projection_alignment_fidelity_input_payload["matched_nodes"],
        key=lambda item: str(item["match_id"]),
    )

    label_projection_keys = [
        _normalize_label_text(str(node["projection_label_text"])) for node in matched_nodes
    ]
    label_extraction_keys = [
        _normalize_label_text(str(node["extraction_label_text"])) for node in matched_nodes
    ]

    span_projection_keys = [
        [int(node["projection_span"]["start"]), int(node["projection_span"]["end"])]
        for node in matched_nodes
    ]
    span_extraction_keys = [
        [int(node["extraction_span"]["start"]), int(node["extraction_span"]["end"])]
        for node in matched_nodes
    ]

    score_projection_keys = [int(node["projection_score_milli"]) for node in matched_nodes]
    score_extraction_keys = [int(node["extraction_score_milli"]) for node in matched_nodes]

    fidelity_items = [
        _fidelity_item(
            source_text_hash=source_text_hash,
            fidelity_code="label_text_mismatch",
            projection_keys=label_projection_keys,
            extraction_keys=label_extraction_keys,
            message="label-text continuity comparison between projection and extraction",
        ),
        _fidelity_item(
            source_text_hash=source_text_hash,
            fidelity_code="score_mismatch",
            projection_keys=score_projection_keys,
            extraction_keys=score_extraction_keys,
            message="score continuity comparison between projection and extraction",
        ),
        _fidelity_item(
            source_text_hash=source_text_hash,
            fidelity_code="span_mismatch",
            projection_keys=span_projection_keys,
            extraction_keys=span_extraction_keys,
            message="span continuity comparison between projection and extraction",
        ),
    ]

    fidelity_items = sorted(
        fidelity_items,
        key=lambda item: (str(item["fidelity_code"]), str(item["fidelity_id"])),
    )

    code_counts = Counter(str(item["fidelity_code"]) for item in fidelity_items)
    status_counts = Counter(str(item["status"]) for item in fidelity_items)
    severity_counts = Counter(str(item["severity"]) for item in fidelity_items)

    fidelity_summary = {
        "total_checks": len(fidelity_items),
        "compatible_checks": status_counts["compatible"],
        "drift_checks": status_counts["drift"],
        "counts_by_code": {code: code_counts[code] for code in sorted(_FROZEN_FIDELITY_CODES)},
        "counts_by_status": {
            "compatible": status_counts["compatible"],
            "drift": status_counts["drift"],
        },
        "counts_by_severity": {
            "high": severity_counts["high"],
            "low": severity_counts["low"],
            "medium": severity_counts["medium"],
        },
    }

    payload: dict[str, Any] = {
        "schema": _EXTRACTION_FIDELITY_PACKET_SCHEMA,
        "source_text_hash": source_text_hash,
        "projection_alignment_hash": _sha256_created_at_stripped(
            artifacts.projection_alignment_payload,
            top_level_excluded_fields=("projection_alignment_hash", "artifact_hash"),
        ),
        "fidelity_input_hash": _sha256_created_at_stripped(
            artifacts.projection_alignment_fidelity_input_payload,
            top_level_excluded_fields=("fidelity_input_hash", "artifact_hash"),
        ),
        "fidelity_summary": fidelity_summary,
        "fidelity_items": fidelity_items,
    }

    try:
        normalized = AdeuProjectionAlignmentFidelity.model_validate(payload)
    except Exception as exc:
        raise _extraction_fidelity_error(
            code="URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID",
            reason="extraction-fidelity packet payload failed schema validation",
            context={"source_text_hash": source_text_hash, "error": str(exc)},
        ) from exc
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


def build_extraction_fidelity_projection_vnext_plus24(
    *,
    catalog_path: Path | None = None,
) -> ProjectionAlignmentFidelityProjectionVnextPlus24:
    _require_extraction_fidelity_non_enforcement_context(
        operation="build_extraction_fidelity_projection_vnext_plus24"
    )

    index = _catalog_index(catalog_path=catalog_path)
    source_text_hashes = sorted(index.entries_by_source_text_hash.keys())
    if not source_text_hashes:
        raise _extraction_fidelity_error(
            code="URM_ADEU_EXTRACTION_FIDELITY_ARTIFACT_NOT_FOUND",
            reason="extraction-fidelity projection catalog has no source entries",
            context={"path": str(index.catalog_path)},
        )

    packets = [
        build_extraction_fidelity_packet_vnext_plus24(
            source_text_hash=source_text_hash,
            catalog_path=index.catalog_path,
        )
        for source_text_hash in source_text_hashes
    ]

    fidelity_code_counts = Counter[str]()
    fidelity_status_counts = Counter[str]()
    fidelity_severity_counts = Counter[str]()
    fidelity_item_count = 0
    for packet in packets:
        packet_items = packet.get("fidelity_items")
        if not isinstance(packet_items, list):
            raise _extraction_fidelity_error(
                code="URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID",
                reason="extraction-fidelity packet payload missing fidelity_items list",
                context={"source_text_hash": packet.get("source_text_hash")},
            )
        fidelity_item_count += len(packet_items)
        for item in packet_items:
            if not isinstance(item, Mapping):
                raise _extraction_fidelity_error(
                    code="URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID",
                    reason="extraction-fidelity packet item must be an object",
                    context={"source_text_hash": packet.get("source_text_hash")},
                )
            fidelity_code_counts[str(item.get("fidelity_code"))] += 1
            fidelity_status_counts[str(item.get("status"))] += 1
            fidelity_severity_counts[str(item.get("severity"))] += 1

    payload: dict[str, Any] = {
        "schema": _EXTRACTION_FIDELITY_PROJECTION_SCHEMA,
        "source_count": len(source_text_hashes),
        "fidelity_item_count": fidelity_item_count,
        "fidelity_counts_by_code": {
            key: fidelity_code_counts[key] for key in sorted(_FROZEN_FIDELITY_CODES)
        },
        "fidelity_counts_by_status": {
            key: fidelity_status_counts[key] for key in sorted(_FROZEN_FIDELITY_STATUSES)
        },
        "fidelity_counts_by_severity": {
            key: fidelity_severity_counts[key] for key in sorted(_FROZEN_FIDELITY_SEVERITIES)
        },
    }

    try:
        return ProjectionAlignmentFidelityProjectionVnextPlus24.model_validate(payload)
    except Exception as exc:
        raise _extraction_fidelity_error(
            code="URM_ADEU_EXTRACTION_FIDELITY_PAYLOAD_INVALID",
            reason="extraction-fidelity projection payload failed schema validation",
            context={"error": str(exc)},
        ) from exc
