from __future__ import annotations

import hashlib
import json
from collections import Counter
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

TrustInvariantPacketSchemaVersion = Literal["adeu_trust_invariant_packet@0.1"]
TrustInvariantCode = Literal[
    "CANONICAL_JSON_CONFORMANCE",
    "HASH_RECOMPUTE_MATCH",
    "REPLAY_HASH_STABILITY",
    "MANIFEST_CHAIN_STABILITY",
]
TrustInvariantStatus = Literal["pass", "fail"]

TRUST_INVARIANT_PACKET_SCHEMA = "adeu_trust_invariant_packet@0.1"
_HEX16_CHARS = frozenset("0123456789abcdef")
_HEX64_CHARS = frozenset("0123456789abcdef")
_ARTIFACT_REF_PREFIX = "artifact:"
_REQUIRED_JUSTIFICATION_SCHEMAS_BY_CODE: dict[TrustInvariantCode, tuple[str, ...]] = {
    "CANONICAL_JSON_CONFORMANCE": (
        "adeu_cross_ir_coherence_diagnostics@0.1",
        "adeu_normative_advice_packet@0.1",
    ),
    "HASH_RECOMPUTE_MATCH": ("adeu_normative_advice_packet@0.1",),
    "REPLAY_HASH_STABILITY": ("adeu_trust_invariant_packet@0.1",),
    "MANIFEST_CHAIN_STABILITY": (
        "adeu_cross_ir_coherence_diagnostics@0.1",
        "adeu_normative_advice_packet@0.1",
    ),
}


def _is_hex16(value: str) -> bool:
    return len(value) == 16 and all(char in _HEX16_CHARS for char in value)


def _is_hex64(value: str) -> bool:
    return len(value) == 64 and all(char in _HEX64_CHARS for char in value)


def _artifact_ref_schema(value: str) -> str | None:
    if not value.startswith(_ARTIFACT_REF_PREFIX):
        return None
    parts = value.split(":")
    if len(parts) != 5:
        return None
    if not all(parts):
        return None
    _, schema, source_text_hash, core_ir_artifact_id, concept_artifact_id = parts
    if not source_text_hash or not core_ir_artifact_id or not concept_artifact_id:
        return None
    return schema


def build_trust_invariant_proof_id(
    *,
    invariant_code: TrustInvariantCode,
    status: TrustInvariantStatus,
    justification_refs: list[str],
    expected_hash: str | None,
    observed_hash: str | None,
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
    canonical_json = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    )
    return hashlib.sha256(canonical_json.encode("utf-8")).hexdigest()[:16]


class TrustInvariantSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")

    total_checks: int = Field(ge=0)
    passed_checks: int = Field(ge=0)
    failed_checks: int = Field(ge=0)
    counts_by_invariant_code: dict[str, int]
    counts_by_status: dict[str, int]

    @model_validator(mode="after")
    def _validate_contract(self) -> "TrustInvariantSummary":
        if list(self.counts_by_invariant_code.keys()) != sorted(
            self.counts_by_invariant_code.keys()
        ):
            raise ValueError("counts_by_invariant_code keys must be lexicographically sorted")
        if any(
            key not in _REQUIRED_JUSTIFICATION_SCHEMAS_BY_CODE
            for key in self.counts_by_invariant_code
        ):
            raise ValueError("counts_by_invariant_code contains unsupported invariant_code")
        if any(value < 0 for value in self.counts_by_invariant_code.values()):
            raise ValueError("counts_by_invariant_code values must be non-negative integers")

        if list(self.counts_by_status.keys()) != sorted(self.counts_by_status.keys()):
            raise ValueError("counts_by_status keys must be lexicographically sorted")
        if any(key not in {"fail", "pass"} for key in self.counts_by_status):
            raise ValueError("counts_by_status contains unsupported status value")
        if any(value < 0 for value in self.counts_by_status.values()):
            raise ValueError("counts_by_status values must be non-negative integers")
        return self


class TrustInvariantProofItem(BaseModel):
    model_config = ConfigDict(extra="forbid")

    proof_id: str = Field(min_length=16, max_length=16)
    invariant_code: TrustInvariantCode
    status: TrustInvariantStatus
    justification_refs: list[str]
    expected_hash: str | None = None
    observed_hash: str | None = None
    source_snapshot: dict[str, Any] | None = None
    message: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "TrustInvariantProofItem":
        if self.justification_refs != sorted(self.justification_refs):
            raise ValueError("justification_refs must be lexicographically sorted")
        if len(set(self.justification_refs)) != len(self.justification_refs):
            raise ValueError("justification_refs may not contain duplicates")
        if not self.justification_refs:
            raise ValueError("justification_refs must be non-empty")

        expected_schemas = _REQUIRED_JUSTIFICATION_SCHEMAS_BY_CODE[self.invariant_code]
        observed_schemas: list[str] = []
        for value in self.justification_refs:
            schema = _artifact_ref_schema(value)
            if schema is None:
                raise ValueError("justification_ref must use artifact:{schema}:{tuple} format")
            observed_schemas.append(schema)
        if tuple(observed_schemas) != expected_schemas:
            raise ValueError("justification_refs must match frozen cardinality and schema order")

        if self.invariant_code == "CANONICAL_JSON_CONFORMANCE":
            if self.expected_hash is not None or self.observed_hash is not None:
                raise ValueError(
                    "canonical-json-conformance may not include expected_hash/observed_hash"
                )
        elif self.invariant_code == "REPLAY_HASH_STABILITY":
            if self.expected_hash is not None:
                raise ValueError("replay-hash-stability may not include expected_hash")
            if self.observed_hash is None:
                raise ValueError("replay-hash-stability must include observed_hash")
        else:
            if self.expected_hash is None or self.observed_hash is None:
                raise ValueError(
                    "hash-recompute/manifest-chain invariants require "
                    "expected_hash and observed_hash"
                )

        if self.expected_hash is not None and not _is_hex64(self.expected_hash):
            raise ValueError("expected_hash must be lowercase sha256 hex")
        if self.observed_hash is not None and not _is_hex64(self.observed_hash):
            raise ValueError("observed_hash must be lowercase sha256 hex")

        if not _is_hex16(self.proof_id):
            raise ValueError("proof_id must be lowercase hex")
        expected_proof_id = build_trust_invariant_proof_id(
            invariant_code=self.invariant_code,
            status=self.status,
            justification_refs=self.justification_refs,
            expected_hash=self.expected_hash,
            observed_hash=self.observed_hash,
        )
        if self.proof_id != expected_proof_id:
            raise ValueError("proof_id must match deterministic content hash")
        return self


class AdeuTrustInvariantPacket(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: TrustInvariantPacketSchemaVersion = TRUST_INVARIANT_PACKET_SCHEMA
    source_text_hash: str = Field(min_length=1)
    core_ir_artifact_id: str = Field(min_length=1)
    concept_artifact_id: str = Field(min_length=1)
    bridge_manifest_hash: str = Field(min_length=64, max_length=64)
    normative_advice_packet_hash: str = Field(min_length=64, max_length=64)
    proof_summary: TrustInvariantSummary
    proof_items: list[TrustInvariantProofItem]

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuTrustInvariantPacket":
        if not _is_hex64(self.bridge_manifest_hash):
            raise ValueError("bridge_manifest_hash must be a lowercase sha256 hex digest")
        if not _is_hex64(self.normative_advice_packet_hash):
            raise ValueError(
                "normative_advice_packet_hash must be a lowercase sha256 hex digest"
            )

        proof_sort_keys = [(item.invariant_code, item.proof_id) for item in self.proof_items]
        if proof_sort_keys != sorted(proof_sort_keys):
            raise ValueError("proof_items must be lexicographically sorted by frozen key")

        expected_invariant_codes = sorted(_REQUIRED_JUSTIFICATION_SCHEMAS_BY_CODE)
        observed_invariant_codes = sorted(item.invariant_code for item in self.proof_items)
        if observed_invariant_codes != expected_invariant_codes:
            raise ValueError("proof_items must include exactly one item per invariant_code")

        invariant_counts = Counter(item.invariant_code for item in self.proof_items)
        status_counts = Counter(item.status for item in self.proof_items)
        expected_counts_by_invariant_code = {
            code: invariant_counts[code] for code in sorted(invariant_counts)
        }
        expected_counts_by_status = {
            status: status_counts[status] for status in sorted(status_counts)
        }

        if self.proof_summary.total_checks != len(self.proof_items):
            raise ValueError("proof_summary.total_checks must equal len(proof_items)")
        if self.proof_summary.passed_checks != status_counts["pass"]:
            raise ValueError("proof_summary.passed_checks must equal count(status=pass)")
        if self.proof_summary.failed_checks != status_counts["fail"]:
            raise ValueError("proof_summary.failed_checks must equal count(status=fail)")
        if (
            self.proof_summary.passed_checks + self.proof_summary.failed_checks
            != self.proof_summary.total_checks
        ):
            raise ValueError("proof_summary pass/fail counts must sum to total_checks")
        if self.proof_summary.counts_by_invariant_code != expected_counts_by_invariant_code:
            raise ValueError("proof_summary.counts_by_invariant_code must match proof_items")
        if self.proof_summary.counts_by_status != expected_counts_by_status:
            raise ValueError("proof_summary.counts_by_status must match proof_items")
        return self


def canonicalize_trust_invariant_packet_payload(payload: dict[str, Any]) -> dict[str, Any]:
    normalized = AdeuTrustInvariantPacket.model_validate(payload)
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)
