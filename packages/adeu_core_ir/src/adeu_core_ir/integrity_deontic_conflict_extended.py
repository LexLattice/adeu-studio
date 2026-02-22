from __future__ import annotations

import unicodedata
from collections import defaultdict
from dataclasses import dataclass
from typing import Any, Literal, Mapping

from pydantic import BaseModel, ConfigDict, Field, model_validator

from .models import AdeuCoreIR

IntegrityDeonticConflictExtendedSchemaVersion = Literal[
    "adeu_integrity_deontic_conflict_extended@0.1"
]
IntegrityDeonticConflictExtendedKind = Literal[
    "deontic_conflict",
    "deontic_tension",
]
_Modality = Literal["obligatory", "forbidden", "permitted"]

_MAX_EMITTED_CONFLICTS = 1000


def _is_present_component(value: Any) -> bool:
    return isinstance(value, str) and value != ""


def _conflict_sort_key(
    conflict: "AdeuIntegrityDeonticConflictExtendedEntry",
) -> tuple[IntegrityDeonticConflictExtendedKind, str, str]:
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


def _conflict_kind_for_modalities(
    modality_a: _Modality,
    modality_b: _Modality,
) -> IntegrityDeonticConflictExtendedKind | None:
    modality_pair = {modality_a, modality_b}
    if modality_pair == {"obligatory", "forbidden"}:
        return "deontic_conflict"
    if modality_pair == {"forbidden", "permitted"}:
        return "deontic_tension"
    return None


def _extract_source_text_hash(payload: Mapping[str, Any]) -> str:
    source_text_hash = payload.get("source_text_hash")
    if not _is_present_component(source_text_hash):
        raise ValueError("source_text_hash must be a non-empty string")
    return source_text_hash


@dataclass(frozen=True)
class _DeonticCandidate:
    node_id: str
    modality: _Modality
    normalized_target: str
    normalized_condition: str
    priority: int | None


class AdeuIntegrityDeonticConflictExtendedSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")

    total_conflicts: int
    deontic_conflict: int
    deontic_tension: int

    @model_validator(mode="after")
    def _validate_total(self) -> "AdeuIntegrityDeonticConflictExtendedSummary":
        expected_total = self.deontic_conflict + self.deontic_tension
        if self.total_conflicts != expected_total:
            raise ValueError("summary.total_conflicts must equal the sum of conflict counts")
        return self


class AdeuIntegrityDeonticConflictExtendedEntry(BaseModel):
    model_config = ConfigDict(extra="forbid")

    kind: IntegrityDeonticConflictExtendedKind
    primary_id: str
    related_id: str = ""
    details: dict[str, Any] | None = None

    @model_validator(mode="after")
    def _validate_ids(self) -> "AdeuIntegrityDeonticConflictExtendedEntry":
        if not self.primary_id:
            raise ValueError("conflict.primary_id may not be empty")
        return self


class AdeuIntegrityDeonticConflictExtended(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: IntegrityDeonticConflictExtendedSchemaVersion = (
        "adeu_integrity_deontic_conflict_extended@0.1"
    )
    source_text_hash: str
    summary: AdeuIntegrityDeonticConflictExtendedSummary
    conflicts: list[AdeuIntegrityDeonticConflictExtendedEntry] = Field(default_factory=list)
    metadata: dict[str, Any] | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuIntegrityDeonticConflictExtended":
        sorted_conflicts = sorted(self.conflicts, key=_conflict_sort_key)
        if self.conflicts != sorted_conflicts:
            raise ValueError("conflicts must be sorted by (kind, primary_id, related_id)")

        counts: dict[IntegrityDeonticConflictExtendedKind, int] = {
            "deontic_conflict": 0,
            "deontic_tension": 0,
        }
        for conflict in self.conflicts:
            counts[conflict.kind] += 1

        expected_summary = {
            "total_conflicts": len(self.conflicts),
            "deontic_conflict": counts["deontic_conflict"],
            "deontic_tension": counts["deontic_tension"],
        }
        actual_summary = self.summary.model_dump(mode="json")
        if actual_summary != expected_summary:
            raise ValueError("summary counts must match conflicts list counts exactly")
        return self


def _collect_deontic_candidates(payload: Mapping[str, Any]) -> list[_DeonticCandidate]:
    raw_nodes = payload.get("nodes")
    if raw_nodes is None:
        return []
    if not isinstance(raw_nodes, list):
        raise ValueError("nodes must be a list when present")

    candidates: list[_DeonticCandidate] = []
    for node in raw_nodes:
        if not isinstance(node, Mapping):
            continue
        if node.get("layer") != "D":
            continue

        node_id = node.get("id")
        modality = node.get("modality")
        if not (
            _is_present_component(node_id)
            and modality in {"obligatory", "forbidden", "permitted"}
        ):
            continue

        normalized_target = _normalize_text(node.get("target"))
        if not normalized_target:
            continue
        normalized_condition = _normalize_condition(node.get("condition"))
        priority = node.get("priority") if isinstance(node.get("priority"), int) else None
        candidates.append(
            _DeonticCandidate(
                node_id=node_id,
                modality=modality,
                normalized_target=normalized_target,
                normalized_condition=normalized_condition,
                priority=priority,
            )
        )
    return sorted(candidates, key=lambda candidate: candidate.node_id)


def _raise_conflict_cap_error() -> None:
    raise ValueError(
        "URM_ADEU_INTEGRITY_FIXTURE_INVALID: "
        "deontic conflict extended diagnostics exceeded cap"
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


def build_integrity_deontic_conflict_extended_diagnostics(
    payload: AdeuCoreIR | Mapping[str, Any],
) -> AdeuIntegrityDeonticConflictExtended:
    raw_payload: Mapping[str, Any]
    if isinstance(payload, AdeuCoreIR):
        raw_payload = payload.model_dump(mode="json", by_alias=True, exclude_none=False)
    else:
        raw_payload = payload

    source_text_hash = _extract_source_text_hash(raw_payload)
    candidates = _collect_deontic_candidates(raw_payload)
    grouped_candidates: dict[tuple[str, str], list[_DeonticCandidate]] = defaultdict(list)
    for candidate in candidates:
        grouped_candidates[(candidate.normalized_target, candidate.normalized_condition)].append(
            candidate
        )

    conflict_map: dict[
        tuple[IntegrityDeonticConflictExtendedKind, str, str],
        AdeuIntegrityDeonticConflictExtendedEntry,
    ] = {}
    for group_key in sorted(grouped_candidates):
        group = grouped_candidates[group_key]
        if len(group) < 2:
            continue
        for index, candidate_a in enumerate(group):
            for candidate_b in group[index + 1 :]:
                conflict_kind = _conflict_kind_for_modalities(
                    candidate_a.modality, candidate_b.modality
                )
                if conflict_kind is None:
                    continue

                primary, related = (
                    (candidate_a, candidate_b)
                    if candidate_a.node_id <= candidate_b.node_id
                    else (candidate_b, candidate_a)
                )
                if primary.node_id == related.node_id:
                    continue
                conflict_key = (conflict_kind, primary.node_id, related.node_id)
                if conflict_key in conflict_map:
                    continue
                if len(conflict_map) >= _MAX_EMITTED_CONFLICTS:
                    _raise_conflict_cap_error()

                conflict_map[conflict_key] = AdeuIntegrityDeonticConflictExtendedEntry(
                    kind=conflict_kind,
                    primary_id=primary.node_id,
                    related_id=related.node_id,
                    details=_build_conflict_details(primary=primary, related=related),
                )

    sorted_conflicts = sorted(conflict_map.values(), key=_conflict_sort_key)
    counts: dict[IntegrityDeonticConflictExtendedKind, int] = {
        "deontic_conflict": 0,
        "deontic_tension": 0,
    }
    for conflict in sorted_conflicts:
        counts[conflict.kind] += 1

    return AdeuIntegrityDeonticConflictExtended(
        schema="adeu_integrity_deontic_conflict_extended@0.1",
        source_text_hash=source_text_hash,
        summary=AdeuIntegrityDeonticConflictExtendedSummary(
            total_conflicts=len(sorted_conflicts),
            deontic_conflict=counts["deontic_conflict"],
            deontic_tension=counts["deontic_tension"],
        ),
        conflicts=sorted_conflicts,
    )


def canonicalize_integrity_deontic_conflict_extended_payload(
    payload: AdeuIntegrityDeonticConflictExtended | Mapping[str, Any],
) -> dict[str, Any]:
    diagnostics = (
        payload
        if isinstance(payload, AdeuIntegrityDeonticConflictExtended)
        else AdeuIntegrityDeonticConflictExtended.model_validate(payload)
    )
    return diagnostics.model_dump(mode="json", by_alias=True, exclude_none=True)
