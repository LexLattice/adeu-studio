from __future__ import annotations

import hashlib
import json
import re
from collections import Counter
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

SemanticsV4CandidatePacketSchemaVersion = Literal["adeu_semantics_v4_candidate_packet@0.1"]
SemanticsV4ComparisonCode = Literal[
    "STATUS_SET_CONTINUITY_REVIEW",
    "ASSURANCE_SET_CONTINUITY_REVIEW",
    "REQUEST_FORMULA_HASH_CONTINUITY_REVIEW",
    "WITNESS_REF_STRUCTURE_REVIEW",
]
SemanticsV4ComparisonStatus = Literal["compatible", "drift"]
SemanticsV4ComparisonSeverity = Literal["low", "medium", "high"]

ADEU_SEMANTICS_V4_CANDIDATE_PACKET_SCHEMA = "adeu_semantics_v4_candidate_packet@0.1"
_HEX16_CHARS = frozenset("0123456789abcdef")
_HEX64_CHARS = frozenset("0123456789abcdef")

_V3_REF_RE = re.compile(r"^artifact:semantics_diagnostics@1:v3:[^:]+:[^:]+:[^:]+$")
_V4_CANDIDATE_REF_RE = re.compile(
    r"^artifact:semantics_diagnostics@1:v4_candidate:[^:]+:[^:]+:[^:]+$"
)
_TRUST_REF_RE = re.compile(r"^artifact:adeu_trust_invariant_packet@0\.1:[^:]+:[^:]+:[^:]+$")

_FROZEN_ASSURANCE_VALUES = frozenset({"kernel_only", "solver_backed", "proof_checked"})

_REQUIRED_JUSTIFICATION_PATTERNS_BY_CODE: dict[
    SemanticsV4ComparisonCode, tuple[re.Pattern[str], ...]
] = {
    "STATUS_SET_CONTINUITY_REVIEW": (_V3_REF_RE, _V4_CANDIDATE_REF_RE),
    "ASSURANCE_SET_CONTINUITY_REVIEW": (_V3_REF_RE, _V4_CANDIDATE_REF_RE),
    "REQUEST_FORMULA_HASH_CONTINUITY_REVIEW": (_V3_REF_RE, _V4_CANDIDATE_REF_RE),
    "WITNESS_REF_STRUCTURE_REVIEW": (_TRUST_REF_RE, _V3_REF_RE, _V4_CANDIDATE_REF_RE),
}

_EXPECTED_SEVERITY_BY_CODE_STATUS: dict[
    tuple[SemanticsV4ComparisonCode, SemanticsV4ComparisonStatus],
    SemanticsV4ComparisonSeverity,
] = {
    ("STATUS_SET_CONTINUITY_REVIEW", "compatible"): "low",
    ("STATUS_SET_CONTINUITY_REVIEW", "drift"): "high",
    ("ASSURANCE_SET_CONTINUITY_REVIEW", "compatible"): "low",
    ("ASSURANCE_SET_CONTINUITY_REVIEW", "drift"): "medium",
    ("REQUEST_FORMULA_HASH_CONTINUITY_REVIEW", "compatible"): "low",
    ("REQUEST_FORMULA_HASH_CONTINUITY_REVIEW", "drift"): "high",
    ("WITNESS_REF_STRUCTURE_REVIEW", "compatible"): "low",
    ("WITNESS_REF_STRUCTURE_REVIEW", "drift"): "medium",
}


def _is_hex16(value: str) -> bool:
    return len(value) == 16 and all(char in _HEX16_CHARS for char in value)


def _is_hex64(value: str) -> bool:
    return len(value) == 64 and all(char in _HEX64_CHARS for char in value)


def build_semantics_v4_candidate_comparison_id(
    *,
    comparison_code: SemanticsV4ComparisonCode,
    status: SemanticsV4ComparisonStatus,
    severity: SemanticsV4ComparisonSeverity,
    justification_refs: list[str],
    expected_hash: str | None,
    observed_hash: str | None,
) -> str:
    payload: dict[str, Any] = {
        "comparison_code": comparison_code,
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


class SemanticsV4CandidateComparisonSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")

    total_comparisons: int = Field(ge=0)
    compatible_checks: int = Field(ge=0)
    drift_checks: int = Field(ge=0)
    counts_by_code: dict[str, int] = Field(default_factory=dict)
    counts_by_severity: dict[str, int] = Field(default_factory=dict)
    counts_by_status: dict[str, int] = Field(default_factory=dict)

    @model_validator(mode="after")
    def _validate_contract(self) -> "SemanticsV4CandidateComparisonSummary":
        if list(self.counts_by_code.keys()) != sorted(self.counts_by_code.keys()):
            raise ValueError("counts_by_code keys must be lexicographically sorted")
        if any(
            key not in _REQUIRED_JUSTIFICATION_PATTERNS_BY_CODE
            for key in self.counts_by_code
        ):
            raise ValueError("counts_by_code contains unsupported comparison_code")
        if any(value < 0 for value in self.counts_by_code.values()):
            raise ValueError("counts_by_code values must be non-negative integers")

        if list(self.counts_by_severity.keys()) != sorted(self.counts_by_severity.keys()):
            raise ValueError("counts_by_severity keys must be lexicographically sorted")
        if any(key not in {"high", "low", "medium"} for key in self.counts_by_severity):
            raise ValueError("counts_by_severity contains unsupported severity value")
        if any(value < 0 for value in self.counts_by_severity.values()):
            raise ValueError("counts_by_severity values must be non-negative integers")

        if list(self.counts_by_status.keys()) != sorted(self.counts_by_status.keys()):
            raise ValueError("counts_by_status keys must be lexicographically sorted")
        if any(key not in {"compatible", "drift"} for key in self.counts_by_status):
            raise ValueError("counts_by_status contains unsupported status value")
        if any(value < 0 for value in self.counts_by_status.values()):
            raise ValueError("counts_by_status values must be non-negative integers")

        if self.total_comparisons != sum(self.counts_by_code.values()):
            raise ValueError("total_comparisons must equal sum(counts_by_code.values())")
        if self.total_comparisons != sum(self.counts_by_severity.values()):
            raise ValueError("total_comparisons must equal sum(counts_by_severity.values())")
        if self.total_comparisons != sum(self.counts_by_status.values()):
            raise ValueError("total_comparisons must equal sum(counts_by_status.values())")
        if self.compatible_checks + self.drift_checks != self.total_comparisons:
            raise ValueError("compatible_checks + drift_checks must equal total_comparisons")
        if self.compatible_checks != self.counts_by_status.get("compatible", 0):
            raise ValueError("compatible_checks must match counts_by_status['compatible']")
        if self.drift_checks != self.counts_by_status.get("drift", 0):
            raise ValueError("drift_checks must match counts_by_status['drift']")
        return self


class SemanticsV4CandidateComparisonItem(BaseModel):
    model_config = ConfigDict(extra="forbid")

    comparison_id: str = Field(min_length=16, max_length=16)
    comparison_code: SemanticsV4ComparisonCode
    status: SemanticsV4ComparisonStatus
    severity: SemanticsV4ComparisonSeverity
    justification_refs: list[str] = Field(default_factory=list)
    expected_hash: str | None = None
    observed_hash: str | None = None
    message: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "SemanticsV4CandidateComparisonItem":
        if self.justification_refs != sorted(self.justification_refs):
            raise ValueError("justification_refs must be lexicographically sorted")
        if len(set(self.justification_refs)) != len(self.justification_refs):
            raise ValueError("justification_refs may not contain duplicates")
        expected_patterns = _REQUIRED_JUSTIFICATION_PATTERNS_BY_CODE[self.comparison_code]
        if len(self.justification_refs) != len(expected_patterns):
            raise ValueError(
                "justification_refs cardinality must match frozen comparison_code mapping"
            )
        for value, pattern in zip(self.justification_refs, expected_patterns):
            if pattern.fullmatch(value) is None:
                raise ValueError("justification_refs must match frozen schema/lane tuple patterns")

        expected_severity = _EXPECTED_SEVERITY_BY_CODE_STATUS[(self.comparison_code, self.status)]
        if self.severity != expected_severity:
            raise ValueError("severity must match frozen comparison_code/status mapping")

        if self.status == "compatible":
            if self.expected_hash is not None or self.observed_hash is not None:
                raise ValueError(
                    "compatible comparison items must omit expected_hash/observed_hash"
                )
        else:
            if self.expected_hash is None or self.observed_hash is None:
                raise ValueError("drift comparison items must include expected_hash/observed_hash")

        if self.expected_hash is not None and not _is_hex64(self.expected_hash):
            raise ValueError("expected_hash must be lowercase sha256 hex")
        if self.observed_hash is not None and not _is_hex64(self.observed_hash):
            raise ValueError("observed_hash must be lowercase sha256 hex")

        if not _is_hex16(self.comparison_id):
            raise ValueError("comparison_id must be lowercase hex")
        expected_id = build_semantics_v4_candidate_comparison_id(
            comparison_code=self.comparison_code,
            status=self.status,
            severity=self.severity,
            justification_refs=self.justification_refs,
            expected_hash=self.expected_hash,
            observed_hash=self.observed_hash,
        )
        if self.comparison_id != expected_id:
            raise ValueError("comparison_id must match deterministic content hash")
        return self


class AdeuSemanticsV4CandidatePacket(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: SemanticsV4CandidatePacketSchemaVersion = ADEU_SEMANTICS_V4_CANDIDATE_PACKET_SCHEMA
    source_text_hash: str = Field(min_length=1)
    core_ir_artifact_id: str = Field(min_length=1)
    concept_artifact_id: str = Field(min_length=1)
    trust_invariant_packet_hash: str = Field(min_length=64, max_length=64)
    baseline_semantics_hash: str = Field(min_length=64, max_length=64)
    candidate_semantics_hash: str = Field(min_length=64, max_length=64)
    comparison_summary: SemanticsV4CandidateComparisonSummary
    comparison_items: list[SemanticsV4CandidateComparisonItem] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuSemanticsV4CandidatePacket":
        if not _is_hex64(self.trust_invariant_packet_hash):
            raise ValueError("trust_invariant_packet_hash must be lowercase sha256 hex")
        if not _is_hex64(self.baseline_semantics_hash):
            raise ValueError("baseline_semantics_hash must be lowercase sha256 hex")
        if not _is_hex64(self.candidate_semantics_hash):
            raise ValueError("candidate_semantics_hash must be lowercase sha256 hex")

        item_sort_keys = [
            (item.comparison_code, item.comparison_id)
            for item in self.comparison_items
        ]
        if item_sort_keys != sorted(item_sort_keys):
            raise ValueError("comparison_items must be lexicographically sorted by frozen key")

        expected_codes = sorted(_REQUIRED_JUSTIFICATION_PATTERNS_BY_CODE)
        observed_codes = sorted(item.comparison_code for item in self.comparison_items)
        if observed_codes != expected_codes:
            raise ValueError("comparison_items must include exactly one item per comparison_code")

        code_counts = Counter(item.comparison_code for item in self.comparison_items)
        severity_counts = Counter(item.severity for item in self.comparison_items)
        status_counts = Counter(item.status for item in self.comparison_items)

        expected_counts_by_code = {code: code_counts[code] for code in sorted(code_counts)}
        expected_counts_by_severity = {
            severity: severity_counts[severity]
            for severity in sorted(severity_counts)
        }
        expected_counts_by_status = {
            status: status_counts[status]
            for status in sorted(status_counts)
        }

        if self.comparison_summary.total_comparisons != len(self.comparison_items):
            raise ValueError(
                "comparison_summary.total_comparisons must equal len(comparison_items)"
            )
        if self.comparison_summary.counts_by_code != expected_counts_by_code:
            raise ValueError("comparison_summary.counts_by_code must match comparison_items")
        if self.comparison_summary.counts_by_severity != expected_counts_by_severity:
            raise ValueError("comparison_summary.counts_by_severity must match comparison_items")
        if self.comparison_summary.counts_by_status != expected_counts_by_status:
            raise ValueError("comparison_summary.counts_by_status must match comparison_items")
        if self.comparison_summary.compatible_checks != status_counts["compatible"]:
            raise ValueError("comparison_summary.compatible_checks must match comparison_items")
        if self.comparison_summary.drift_checks != status_counts["drift"]:
            raise ValueError("comparison_summary.drift_checks must match comparison_items")
        return self


def canonicalize_semantics_v4_candidate_packet_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    normalized = AdeuSemanticsV4CandidatePacket.model_validate(payload)
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)
