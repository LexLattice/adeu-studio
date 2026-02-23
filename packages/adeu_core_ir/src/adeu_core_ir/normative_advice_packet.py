from __future__ import annotations

import json
from collections import Counter
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

NormativeAdvicePacketSchemaVersion = Literal["adeu_normative_advice_packet@0.1"]
NormativeAdviceCode = Literal[
    "MAPPING_GAP_REVIEW",
    "SOURCE_DIVERGENCE_REVIEW",
    "TOPOLOGY_ALIGNMENT_REVIEW",
    "CLAIM_PROJECTION_REVIEW",
    "TRUST_ALIGNMENT_REVIEW",
]
NormativeAdvicePriority = Literal["low", "medium", "high"]
CrossIRIssueCode = Literal[
    "MISSING_CONCEPT_MAPPING",
    "MISSING_CORE_IR_MAPPING",
    "TOPOLOGY_DRIFT",
    "CLAIM_PROJECTION_GAP",
    "LINK_KIND_DRIFT",
    "SOURCE_HASH_MISMATCH",
    "TRUST_LABEL_MISMATCH",
]
CrossIRIssueSeverity = Literal["warn", "error"]

NORMATIVE_ADVICE_PACKET_SCHEMA = "adeu_normative_advice_packet@0.1"
NORMATIVE_ADVICE_JUSTIFICATION_PREFIX = "coherence_issue:"

_ADVICE_PRIORITY_BY_CODE: dict[NormativeAdviceCode, NormativeAdvicePriority] = {
    "MAPPING_GAP_REVIEW": "medium",
    "SOURCE_DIVERGENCE_REVIEW": "high",
    "TOPOLOGY_ALIGNMENT_REVIEW": "medium",
    "CLAIM_PROJECTION_REVIEW": "high",
    "TRUST_ALIGNMENT_REVIEW": "medium",
}
_HEX16_CHARS = frozenset("0123456789abcdef")
_HEX64_CHARS = frozenset("0123456789abcdef")


def _is_hex16(value: str) -> bool:
    return len(value) == 16 and all(char in _HEX16_CHARS for char in value)


def _is_hex64(value: str) -> bool:
    return len(value) == 64 and all(char in _HEX64_CHARS for char in value)


def _advice_id(
    *,
    advice_code: NormativeAdviceCode,
    concept_refs: list[str],
    core_ir_refs: list[str],
    justification_refs: list[str],
) -> str:
    import hashlib

    payload = {
        "advice_code": advice_code,
        "concept_refs": concept_refs,
        "core_ir_refs": core_ir_refs,
        "justification_refs": justification_refs,
    }
    canonical_json = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    )
    return hashlib.sha256(canonical_json.encode("utf-8")).hexdigest()[:16]


def _issue_id_from_justification_ref(value: str) -> str | None:
    if not value.startswith(NORMATIVE_ADVICE_JUSTIFICATION_PREFIX):
        return None
    issue_id = value[len(NORMATIVE_ADVICE_JUSTIFICATION_PREFIX) :]
    if not _is_hex16(issue_id):
        return None
    return issue_id


class NormativeAdviceSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")

    total_advice: int = Field(ge=0)
    counts_by_code: dict[str, int] = Field(default_factory=dict)
    counts_by_priority: dict[str, int] = Field(default_factory=dict)

    @model_validator(mode="after")
    def _validate_contract(self) -> "NormativeAdviceSummary":
        if list(self.counts_by_code.keys()) != sorted(self.counts_by_code.keys()):
            raise ValueError("counts_by_code keys must be lexicographically sorted")
        if any(key not in _ADVICE_PRIORITY_BY_CODE for key in self.counts_by_code):
            raise ValueError("counts_by_code contains unsupported advice_code")
        if any(value < 0 for value in self.counts_by_code.values()):
            raise ValueError("counts_by_code values must be non-negative integers")

        if list(self.counts_by_priority.keys()) != sorted(self.counts_by_priority.keys()):
            raise ValueError("counts_by_priority keys must be lexicographically sorted")
        if any(key not in {"high", "low", "medium"} for key in self.counts_by_priority):
            raise ValueError("counts_by_priority contains unsupported priority value")
        if any(value < 0 for value in self.counts_by_priority.values()):
            raise ValueError("counts_by_priority values must be non-negative integers")
        return self


class NormativeAdviceSourceIssueSnapshot(BaseModel):
    model_config = ConfigDict(extra="forbid")

    issue_id: str = Field(min_length=16, max_length=16)
    issue_code: CrossIRIssueCode
    severity: CrossIRIssueSeverity
    message: str = Field(min_length=1)
    evidence: dict[str, Any]

    @model_validator(mode="after")
    def _validate_contract(self) -> "NormativeAdviceSourceIssueSnapshot":
        if not _is_hex16(self.issue_id):
            raise ValueError("source_issue_snapshot.issue_id must be lowercase hex")
        return self


class NormativeAdviceItem(BaseModel):
    model_config = ConfigDict(extra="forbid")

    advice_id: str = Field(min_length=16, max_length=16)
    advice_code: NormativeAdviceCode
    priority: NormativeAdvicePriority
    concept_refs: list[str] = Field(default_factory=list)
    core_ir_refs: list[str] = Field(default_factory=list)
    justification_refs: list[str] = Field(default_factory=list)
    source_issue_snapshot: NormativeAdviceSourceIssueSnapshot | None = None
    message: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "NormativeAdviceItem":
        if self.priority != _ADVICE_PRIORITY_BY_CODE[self.advice_code]:
            raise ValueError("priority must match frozen advice_code mapping")
        if self.concept_refs != sorted(self.concept_refs):
            raise ValueError("concept_refs must be lexicographically sorted")
        if len(set(self.concept_refs)) != len(self.concept_refs):
            raise ValueError("concept_refs may not contain duplicates")
        if self.core_ir_refs != sorted(self.core_ir_refs):
            raise ValueError("core_ir_refs must be lexicographically sorted")
        if len(set(self.core_ir_refs)) != len(self.core_ir_refs):
            raise ValueError("core_ir_refs may not contain duplicates")
        if self.justification_refs != sorted(self.justification_refs):
            raise ValueError("justification_refs must be lexicographically sorted")
        if len(set(self.justification_refs)) != len(self.justification_refs):
            raise ValueError("justification_refs may not contain duplicates")
        if len(self.justification_refs) != 1:
            raise ValueError("each advice item must include exactly one justification_ref")
        issue_id = _issue_id_from_justification_ref(self.justification_refs[0])
        if issue_id is None:
            raise ValueError("justification_ref must use coherence_issue:{issue_id} format")
        if (
            self.source_issue_snapshot is not None
            and self.source_issue_snapshot.issue_id != issue_id
        ):
            raise ValueError(
                "source_issue_snapshot.issue_id must match justification_refs[0] issue id"
            )
        if not _is_hex16(self.advice_id):
            raise ValueError("advice_id must be lowercase hex")
        expected_advice_id = _advice_id(
            advice_code=self.advice_code,
            concept_refs=self.concept_refs,
            core_ir_refs=self.core_ir_refs,
            justification_refs=self.justification_refs,
        )
        if self.advice_id != expected_advice_id:
            raise ValueError("advice_id must match deterministic content hash")
        return self


class AdeuNormativeAdvicePacket(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: NormativeAdvicePacketSchemaVersion = NORMATIVE_ADVICE_PACKET_SCHEMA
    source_text_hash: str = Field(min_length=1)
    core_ir_artifact_id: str = Field(min_length=1)
    concept_artifact_id: str = Field(min_length=1)
    bridge_manifest_hash: str = Field(min_length=64, max_length=64)
    advice_summary: NormativeAdviceSummary
    advice_items: list[NormativeAdviceItem] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuNormativeAdvicePacket":
        if not _is_hex64(self.bridge_manifest_hash):
            raise ValueError("bridge_manifest_hash must be a lowercase sha256 hex digest")

        advice_sort_keys = [
            (
                item.advice_code,
                item.concept_refs[0] if item.concept_refs else "",
                item.core_ir_refs[0] if item.core_ir_refs else "",
                item.advice_id,
            )
            for item in self.advice_items
        ]
        if advice_sort_keys != sorted(advice_sort_keys):
            raise ValueError("advice_items must be lexicographically sorted by frozen key")

        code_counts = Counter(item.advice_code for item in self.advice_items)
        priority_counts = Counter(item.priority for item in self.advice_items)
        expected_counts_by_code = {code: code_counts[code] for code in sorted(code_counts)}
        expected_counts_by_priority = {
            priority: priority_counts[priority] for priority in sorted(priority_counts)
        }
        if self.advice_summary.total_advice != len(self.advice_items):
            raise ValueError("advice_summary.total_advice must equal len(advice_items)")
        if self.advice_summary.counts_by_code != expected_counts_by_code:
            raise ValueError("advice_summary.counts_by_code must match advice_items")
        if self.advice_summary.counts_by_priority != expected_counts_by_priority:
            raise ValueError("advice_summary.counts_by_priority must match advice_items")
        return self


def canonicalize_normative_advice_packet_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    normalized = AdeuNormativeAdvicePacket.model_validate(payload)
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)
