from __future__ import annotations

import hashlib
import json
import re
from collections import Counter
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

ProjectionAlignmentFidelityInputSchemaVersion = Literal[
    "adeu_projection_alignment_fidelity_input@0.1"
]
ProjectionAlignmentFidelityPacketSchemaVersion = Literal["adeu_projection_alignment_fidelity@0.1"]
ProjectionAlignmentFidelityCode = Literal[
    "label_text_mismatch",
    "span_mismatch",
    "score_mismatch",
]
ProjectionAlignmentFidelityStatus = Literal["compatible", "drift"]
ProjectionAlignmentFidelitySeverity = Literal["low", "medium", "high"]

ADEU_PROJECTION_ALIGNMENT_FIDELITY_INPUT_SCHEMA = "adeu_projection_alignment_fidelity_input@0.1"
ADEU_PROJECTION_ALIGNMENT_FIDELITY_SCHEMA = "adeu_projection_alignment_fidelity@0.1"
MAX_MATCHED_NODES_PER_SOURCE = 5000

_HEX16_CHARS = frozenset("0123456789abcdef")
_HEX64_CHARS = frozenset("0123456789abcdef")
_FROZEN_FIDELITY_CODES = (
    "label_text_mismatch",
    "span_mismatch",
    "score_mismatch",
)
_ALLOWED_SEVERITIES = ("high", "low", "medium")
_ALLOWED_STATUSES = ("compatible", "drift")
_FIDELITY_SOURCE_REF_RE = re.compile(r"^artifact:(?P<schema>[^:]+):(?P<source_text_hash>[^:]+)$")
_EXPECTED_SEVERITY_BY_CODE_STATUS: dict[
    tuple[ProjectionAlignmentFidelityCode, ProjectionAlignmentFidelityStatus],
    ProjectionAlignmentFidelitySeverity,
] = {
    ("label_text_mismatch", "compatible"): "low",
    ("label_text_mismatch", "drift"): "medium",
    ("span_mismatch", "compatible"): "low",
    ("span_mismatch", "drift"): "high",
    ("score_mismatch", "compatible"): "low",
    ("score_mismatch", "drift"): "medium",
}
_EXPECTED_JUSTIFICATION_SCHEMAS = (
    "adeu_projection_alignment@0.1",
    "adeu_projection_alignment_fidelity_input@0.1",
)


def _is_hex16(value: str) -> bool:
    return len(value) == 16 and all(char in _HEX16_CHARS for char in value)


def _is_hex64(value: str) -> bool:
    return len(value) == 64 and all(char in _HEX64_CHARS for char in value)


def _ref_schema_and_source(value: str) -> tuple[str, str] | None:
    match = _FIDELITY_SOURCE_REF_RE.fullmatch(value)
    if match is None:
        return None
    schema = match.group("schema")
    source_text_hash = match.group("source_text_hash")
    if not schema or not source_text_hash:
        return None
    return (schema, source_text_hash)


def build_projection_alignment_fidelity_id(
    *,
    fidelity_code: ProjectionAlignmentFidelityCode,
    status: ProjectionAlignmentFidelityStatus,
    severity: ProjectionAlignmentFidelitySeverity,
    justification_refs: list[str],
    expected_hash: str | None,
    observed_hash: str | None,
) -> str:
    payload: dict[str, Any] = {
        "fidelity_code": fidelity_code,
        "status": status,
        "severity": severity,
        "justification_refs": justification_refs,
    }
    if expected_hash is not None:
        payload["expected_hash"] = expected_hash
    if observed_hash is not None:
        payload["observed_hash"] = observed_hash

    canonical_json = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(canonical_json.encode("utf-8")).hexdigest()[:16]


class ProjectionAlignmentFidelitySpan(BaseModel):
    model_config = ConfigDict(extra="forbid")

    start: int = Field(ge=0)
    end: int = Field(ge=0)

    @model_validator(mode="after")
    def _validate_bounds(self) -> "ProjectionAlignmentFidelitySpan":
        if self.start > self.end:
            raise ValueError("span start may not exceed span end")
        return self


class ProjectionAlignmentFidelityMatchedNode(BaseModel):
    model_config = ConfigDict(extra="forbid")

    match_id: str = Field(min_length=1)
    projection_label_text: str
    extraction_label_text: str
    projection_span: ProjectionAlignmentFidelitySpan
    extraction_span: ProjectionAlignmentFidelitySpan
    projection_score_milli: int = Field(ge=0, le=1000)
    extraction_score_milli: int = Field(ge=0, le=1000)


class AdeuProjectionAlignmentFidelityInput(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: ProjectionAlignmentFidelityInputSchemaVersion = (
        ADEU_PROJECTION_ALIGNMENT_FIDELITY_INPUT_SCHEMA
    )
    source_text_hash: str = Field(min_length=1)
    matched_nodes: list[ProjectionAlignmentFidelityMatchedNode]

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuProjectionAlignmentFidelityInput":
        if len(self.matched_nodes) > MAX_MATCHED_NODES_PER_SOURCE:
            raise ValueError(
                "matched_nodes may not exceed max_matched_nodes_per_source="
                f"{MAX_MATCHED_NODES_PER_SOURCE}"
            )

        match_ids = [node.match_id for node in self.matched_nodes]
        if len(set(match_ids)) != len(match_ids):
            raise ValueError("matched_nodes may not contain duplicate match_id values")
        return self


class ProjectionAlignmentFidelitySummary(BaseModel):
    model_config = ConfigDict(extra="forbid")

    total_checks: int = Field(ge=0)
    compatible_checks: int = Field(ge=0)
    drift_checks: int = Field(ge=0)
    counts_by_code: dict[str, int] = Field(default_factory=dict)
    counts_by_status: dict[str, int] = Field(default_factory=dict)
    counts_by_severity: dict[str, int] = Field(default_factory=dict)

    @model_validator(mode="after")
    def _validate_contract(self) -> "ProjectionAlignmentFidelitySummary":
        if list(self.counts_by_code.keys()) != sorted(self.counts_by_code.keys()):
            raise ValueError("counts_by_code keys must be lexicographically sorted")
        if tuple(self.counts_by_code.keys()) != tuple(sorted(_FROZEN_FIDELITY_CODES)):
            raise ValueError("counts_by_code must include exactly the frozen fidelity_code keys")
        if any(value < 0 for value in self.counts_by_code.values()):
            raise ValueError("counts_by_code values must be non-negative integers")

        if list(self.counts_by_status.keys()) != sorted(self.counts_by_status.keys()):
            raise ValueError("counts_by_status keys must be lexicographically sorted")
        if tuple(self.counts_by_status.keys()) != tuple(_ALLOWED_STATUSES):
            raise ValueError("counts_by_status must include exactly the frozen status keys")
        if any(value < 0 for value in self.counts_by_status.values()):
            raise ValueError("counts_by_status values must be non-negative integers")

        if list(self.counts_by_severity.keys()) != sorted(self.counts_by_severity.keys()):
            raise ValueError("counts_by_severity keys must be lexicographically sorted")
        if any(key not in _ALLOWED_SEVERITIES for key in self.counts_by_severity):
            raise ValueError("counts_by_severity contains unsupported severity value")
        if any(value < 0 for value in self.counts_by_severity.values()):
            raise ValueError("counts_by_severity values must be non-negative integers")

        if self.compatible_checks + self.drift_checks != self.total_checks:
            raise ValueError("compatible_checks + drift_checks must equal total_checks")
        if sum(self.counts_by_code.values()) != self.total_checks:
            raise ValueError("sum(counts_by_code.values()) must equal total_checks")
        if sum(self.counts_by_status.values()) != self.total_checks:
            raise ValueError("sum(counts_by_status.values()) must equal total_checks")
        if sum(self.counts_by_severity.values()) != self.total_checks:
            raise ValueError("sum(counts_by_severity.values()) must equal total_checks")
        return self


class ProjectionAlignmentFidelityItem(BaseModel):
    model_config = ConfigDict(extra="forbid")

    fidelity_id: str = Field(min_length=16, max_length=16)
    fidelity_code: ProjectionAlignmentFidelityCode
    status: ProjectionAlignmentFidelityStatus
    severity: ProjectionAlignmentFidelitySeverity
    justification_refs: list[str] = Field(default_factory=list)
    expected_hash: str | None = None
    observed_hash: str | None = None
    message: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "ProjectionAlignmentFidelityItem":
        if self.justification_refs != sorted(self.justification_refs):
            raise ValueError("justification_refs must be lexicographically sorted")
        if len(set(self.justification_refs)) != len(self.justification_refs):
            raise ValueError("justification_refs may not contain duplicates")
        if len(self.justification_refs) != 2:
            raise ValueError("fidelity items must include exactly two justification_refs")

        parsed_refs: list[tuple[str, str]] = []
        for ref in self.justification_refs:
            parsed = _ref_schema_and_source(ref)
            if parsed is None:
                raise ValueError(
                    "justification_refs must match artifact:{schema}:{source_text_hash} format"
                )
            parsed_refs.append(parsed)

        schemas = tuple(schema for schema, _ in parsed_refs)
        if schemas != _EXPECTED_JUSTIFICATION_SCHEMAS:
            raise ValueError("justification_refs must match frozen cardinality and schema order")
        source_text_hashes = {source_text_hash for _, source_text_hash in parsed_refs}
        if len(source_text_hashes) != 1:
            raise ValueError("justification_refs must bind to exactly one source_text_hash")

        expected_severity = _EXPECTED_SEVERITY_BY_CODE_STATUS[(self.fidelity_code, self.status)]
        if self.severity != expected_severity:
            raise ValueError("severity must match frozen fidelity_code/status mapping")

        if self.status == "compatible":
            if self.expected_hash is not None or self.observed_hash is not None:
                raise ValueError(
                    "compatible fidelity items must omit expected_hash and observed_hash"
                )
        else:
            if self.expected_hash is None or self.observed_hash is None:
                raise ValueError(
                    "drift fidelity items must include expected_hash and observed_hash"
                )

        if self.expected_hash is not None and not _is_hex64(self.expected_hash):
            raise ValueError("expected_hash must be lowercase sha256 hex")
        if self.observed_hash is not None and not _is_hex64(self.observed_hash):
            raise ValueError("observed_hash must be lowercase sha256 hex")

        if not _is_hex16(self.fidelity_id):
            raise ValueError("fidelity_id must be lowercase hex")
        expected_fidelity_id = build_projection_alignment_fidelity_id(
            fidelity_code=self.fidelity_code,
            status=self.status,
            severity=self.severity,
            justification_refs=self.justification_refs,
            expected_hash=self.expected_hash,
            observed_hash=self.observed_hash,
        )
        if self.fidelity_id != expected_fidelity_id:
            raise ValueError("fidelity_id must match deterministic content hash")
        return self


class AdeuProjectionAlignmentFidelity(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: ProjectionAlignmentFidelityPacketSchemaVersion = (
        ADEU_PROJECTION_ALIGNMENT_FIDELITY_SCHEMA
    )
    source_text_hash: str = Field(min_length=1)
    projection_alignment_hash: str = Field(min_length=64, max_length=64)
    fidelity_input_hash: str = Field(min_length=64, max_length=64)
    fidelity_summary: ProjectionAlignmentFidelitySummary
    fidelity_items: list[ProjectionAlignmentFidelityItem] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuProjectionAlignmentFidelity":
        if not _is_hex64(self.projection_alignment_hash):
            raise ValueError("projection_alignment_hash must be lowercase sha256 hex")
        if not _is_hex64(self.fidelity_input_hash):
            raise ValueError("fidelity_input_hash must be lowercase sha256 hex")

        fidelity_sort_keys = [
            (item.fidelity_code, item.fidelity_id) for item in self.fidelity_items
        ]
        if fidelity_sort_keys != sorted(fidelity_sort_keys):
            raise ValueError("fidelity_items must be lexicographically sorted by frozen key")

        observed_codes = sorted(item.fidelity_code for item in self.fidelity_items)
        if observed_codes != sorted(_FROZEN_FIDELITY_CODES):
            raise ValueError("fidelity_items must include exactly one item per fidelity_code")

        for item in self.fidelity_items:
            item_source_hashes = {
                source_text_hash
                for schema, source_text_hash in (
                    _ref_schema_and_source(ref) or ("", "") for ref in item.justification_refs
                )
                if schema
            }
            if item_source_hashes != {self.source_text_hash}:
                raise ValueError(
                    "fidelity item justification_refs must bind to packet source_text_hash"
                )

        code_counts = Counter(item.fidelity_code for item in self.fidelity_items)
        status_counts = Counter(item.status for item in self.fidelity_items)
        severity_counts = Counter(item.severity for item in self.fidelity_items)

        expected_counts_by_code = {
            code: code_counts[code] for code in sorted(_FROZEN_FIDELITY_CODES)
        }
        if self.fidelity_summary.counts_by_code != expected_counts_by_code:
            raise ValueError("fidelity_summary.counts_by_code must match fidelity_items")

        expected_counts_by_status = {status: status_counts[status] for status in _ALLOWED_STATUSES}
        if self.fidelity_summary.counts_by_status != expected_counts_by_status:
            raise ValueError("fidelity_summary.counts_by_status must match fidelity_items")

        summary_severity_keys = tuple(self.fidelity_summary.counts_by_severity.keys())
        expected_counts_by_severity = {
            severity: severity_counts[severity] for severity in summary_severity_keys
        }
        if self.fidelity_summary.counts_by_severity != expected_counts_by_severity:
            raise ValueError("fidelity_summary.counts_by_severity must match fidelity_items")
        if set(severity_counts.keys()) - set(summary_severity_keys):
            raise ValueError("fidelity_summary.counts_by_severity is missing observed severities")

        if self.fidelity_summary.total_checks != len(self.fidelity_items):
            raise ValueError("fidelity_summary.total_checks must equal len(fidelity_items)")
        if self.fidelity_summary.compatible_checks != status_counts["compatible"]:
            raise ValueError(
                "fidelity_summary.compatible_checks must match count(status=compatible)"
            )
        if self.fidelity_summary.drift_checks != status_counts["drift"]:
            raise ValueError("fidelity_summary.drift_checks must match count(status=drift)")
        return self


def canonicalize_projection_alignment_fidelity_input_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    normalized = AdeuProjectionAlignmentFidelityInput.model_validate(payload)
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


def canonicalize_projection_alignment_fidelity_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    normalized = AdeuProjectionAlignmentFidelity.model_validate(payload)
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)
