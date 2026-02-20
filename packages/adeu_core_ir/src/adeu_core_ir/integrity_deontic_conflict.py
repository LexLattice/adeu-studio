from __future__ import annotations

import unicodedata
from collections import defaultdict
from dataclasses import dataclass
from typing import Any, Literal, Mapping

from pydantic import BaseModel, ConfigDict, Field, model_validator

from .models import AdeuCoreIR, CoreDNode

IntegrityDeonticConflictSchemaVersion = Literal["adeu_integrity_deontic_conflict@0.1"]
IntegrityDeonticConflictKind = Literal["deontic_conflict"]
_MAX_EMITTED_CONFLICTS = 1000


def _conflict_sort_key(
    conflict: "AdeuIntegrityDeonticConflictEntry",
) -> tuple[IntegrityDeonticConflictKind, str, str]:
    return (conflict.kind, conflict.primary_id, conflict.related_id)


def _ascii_lowercase(value: str) -> str:
    lowered_chars: list[str] = []
    for char in value:
        if "A" <= char <= "Z":
            lowered_chars.append(chr(ord(char) + 32))
        else:
            lowered_chars.append(char)
    return "".join(lowered_chars)


def _normalize_text(value: str | None) -> str:
    if value is None:
        return ""
    normalized = unicodedata.normalize("NFC", value)
    normalized = " ".join(normalized.split()).strip()
    return _ascii_lowercase(normalized)


def _normalize_condition(value: str | None) -> str:
    normalized = _normalize_text(value)
    if normalized in {"always", "none"}:
        return ""
    return normalized


def _is_conflict_modality_pair(modality_a: str, modality_b: str) -> bool:
    return {modality_a, modality_b} == {"obligatory", "forbidden"}


@dataclass(frozen=True)
class _DeonticCandidate:
    node_id: str
    modality: Literal["obligatory", "forbidden", "permitted"]
    normalized_target: str
    normalized_condition: str
    priority: int | None


class AdeuIntegrityDeonticConflictSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")

    total_conflicts: int
    deontic_conflict: int

    @model_validator(mode="after")
    def _validate_total(self) -> "AdeuIntegrityDeonticConflictSummary":
        if self.total_conflicts != self.deontic_conflict:
            raise ValueError("summary.total_conflicts must equal summary.deontic_conflict")
        return self


class AdeuIntegrityDeonticConflictEntry(BaseModel):
    model_config = ConfigDict(extra="forbid")

    kind: IntegrityDeonticConflictKind
    primary_id: str
    related_id: str = ""
    details: dict[str, Any] | None = None

    @model_validator(mode="after")
    def _validate_ids(self) -> "AdeuIntegrityDeonticConflictEntry":
        if not self.primary_id:
            raise ValueError("conflict.primary_id may not be empty")
        return self


class AdeuIntegrityDeonticConflict(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: IntegrityDeonticConflictSchemaVersion = "adeu_integrity_deontic_conflict@0.1"
    source_text_hash: str
    summary: AdeuIntegrityDeonticConflictSummary
    conflicts: list[AdeuIntegrityDeonticConflictEntry] = Field(default_factory=list)
    metadata: dict[str, Any] | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuIntegrityDeonticConflict":
        sorted_conflicts = sorted(self.conflicts, key=_conflict_sort_key)
        if self.conflicts != sorted_conflicts:
            raise ValueError("conflicts must be sorted by (kind, primary_id, related_id)")

        expected_summary = {
            "total_conflicts": len(self.conflicts),
            "deontic_conflict": len(self.conflicts),
        }
        actual_summary = self.summary.model_dump(mode="json")
        if actual_summary != expected_summary:
            raise ValueError("summary counts must match conflicts list counts exactly")
        return self


def _collect_deontic_candidates(core_ir: AdeuCoreIR) -> list[_DeonticCandidate]:
    candidates: list[_DeonticCandidate] = []
    for node in core_ir.nodes:
        if not isinstance(node, CoreDNode):
            continue
        if node.modality not in {"obligatory", "forbidden", "permitted"}:
            continue

        normalized_target = _normalize_text(node.target)
        if not normalized_target:
            continue
        normalized_condition = _normalize_condition(node.condition)
        candidates.append(
            _DeonticCandidate(
                node_id=node.id,
                modality=node.modality,
                normalized_target=normalized_target,
                normalized_condition=normalized_condition,
                priority=node.priority,
            )
        )
    return sorted(candidates, key=lambda candidate: candidate.node_id)


def _raise_conflict_cap_error() -> None:
    raise ValueError(
        "URM_ADEU_INTEGRITY_FIXTURE_INVALID: "
        "deontic conflict diagnostics exceeded cap"
    )


def _build_conflict_details(
    *,
    primary: _DeonticCandidate,
    related: _DeonticCandidate,
) -> dict[str, Any]:
    details: dict[str, Any] = {
        "normalized_target": primary.normalized_target,
        "normalized_condition": primary.normalized_condition,
        "primary_modality": primary.modality,
        "related_modality": related.modality,
    }
    if primary.priority is not None:
        details["primary_priority"] = primary.priority
    if related.priority is not None:
        details["related_priority"] = related.priority
    return details


def build_integrity_deontic_conflict_diagnostics(
    payload: AdeuCoreIR | Mapping[str, Any],
) -> AdeuIntegrityDeonticConflict:
    core_ir = payload if isinstance(payload, AdeuCoreIR) else AdeuCoreIR.model_validate(payload)
    candidates = _collect_deontic_candidates(core_ir)
    grouped_candidates: dict[tuple[str, str], list[_DeonticCandidate]] = defaultdict(list)
    for candidate in candidates:
        grouped_candidates[(candidate.normalized_target, candidate.normalized_condition)].append(
            candidate
        )

    conflicts: list[AdeuIntegrityDeonticConflictEntry] = []
    for group_key in sorted(grouped_candidates):
        group = grouped_candidates[group_key]
        if len(group) < 2:
            continue
        for index, candidate_a in enumerate(group):
            for candidate_b in group[index + 1 :]:
                if not _is_conflict_modality_pair(candidate_a.modality, candidate_b.modality):
                    continue

                primary, related = (
                    (candidate_a, candidate_b)
                    if candidate_a.node_id <= candidate_b.node_id
                    else (candidate_b, candidate_a)
                )
                conflicts.append(
                    AdeuIntegrityDeonticConflictEntry.model_validate(
                        {
                            "kind": "deontic_conflict",
                            "primary_id": primary.node_id,
                            "related_id": related.node_id,
                            "details": _build_conflict_details(primary=primary, related=related),
                        }
                    )
                )
                if len(conflicts) > _MAX_EMITTED_CONFLICTS:
                    _raise_conflict_cap_error()

    sorted_conflicts = sorted(conflicts, key=_conflict_sort_key)
    return AdeuIntegrityDeonticConflict.model_validate(
        {
            "schema": "adeu_integrity_deontic_conflict@0.1",
            "source_text_hash": core_ir.source_text_hash,
            "summary": {
                "total_conflicts": len(sorted_conflicts),
                "deontic_conflict": len(sorted_conflicts),
            },
            "conflicts": [
                conflict.model_dump(mode="json", by_alias=True, exclude_none=True)
                for conflict in sorted_conflicts
            ],
        }
    )


def canonicalize_integrity_deontic_conflict_payload(
    payload: AdeuIntegrityDeonticConflict | Mapping[str, Any],
) -> dict[str, Any]:
    diagnostics = (
        payload
        if isinstance(payload, AdeuIntegrityDeonticConflict)
        else AdeuIntegrityDeonticConflict.model_validate(payload)
    )
    return diagnostics.model_dump(mode="json", by_alias=True, exclude_none=True)
