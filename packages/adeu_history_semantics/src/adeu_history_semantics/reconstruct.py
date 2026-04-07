from __future__ import annotations

import re
from dataclasses import dataclass

from .models import (
    ODEU_LANE_ORDER,
    HistoryEvidenceRef,
    HistoryLedger,
    HistoryLedgerEntry,
    HistoryODEULaneReconstruction,
    HistoryODEUReconstructionPacket,
    HistorySlice,
    HistoryThemeAnchor,
    compute_history_odeu_packet_id,
    compute_history_odeu_packet_semantic_hash,
)

_SENTENCE_SPLIT_RE = re.compile(r"(?<=[.!?])\s+")
_LANE_EXPLICIT_LINE_RE = re.compile(r"^\s*([OEDU])\s*[:\-]\s*(.+)$", re.IGNORECASE)
_O_DEFINITION_RE = re.compile(
    r"\b(is a|is an|is the|means|defined as|treat(?:s|ed)? as)\b",
    re.IGNORECASE,
)
_E_EXPLICIT_RE = re.compile(
    r"\b(provenance|evidence|explicit|authoritative|underdetermined|heuristic|source)\b",
    re.IGNORECASE,
)
_D_EXPLICIT_RE = re.compile(
    r"\b(must|should|do not|must not|forbidden|required|preserve|keep|prefer|fail-closed)\b",
    re.IGNORECASE,
)
_U_EXPLICIT_RE = re.compile(
    r"\b(goal|purpose|bootstrap|ready for|help|used for|so that|enable|target|future)\b",
    re.IGNORECASE,
)

_LANE_KEYWORDS: dict[str, tuple[str, ...]] = {
    "O": (
        "artifact",
        "anchor",
        "frame",
        "history",
        "lane",
        "ledger",
        "ontology",
        "ontological",
        "ontological lane",
        "packet",
        "reconstruction",
        "slice",
        "substrate",
        "theme",
    ),
    "E": (
        "authoritative",
        "confidence",
        "deterministic",
        "evidence",
        "epistemic",
        "epistemic lane",
        "explicit",
        "heuristic",
        "honesty",
        "provenance",
        "reconstruct",
        "source",
        "test",
        "underdetermined",
        "validate",
    ),
    "D": (
        "default bias",
        "deontic",
        "deontic lane",
        "do not",
        "fail-closed",
        "forbidden",
        "keep",
        "must",
        "must not",
        "not allowed",
        "prefer",
        "preserve",
        "required",
        "should",
    ),
    "U": (
        "bootstrap",
        "enable",
        "future ingestion",
        "goal",
        "help",
        "later work",
        "purpose",
        "ready for",
        "so that",
        "target",
        "utility",
        "utility lane",
        "used for",
    ),
}


@dataclass(frozen=True)
class _LaneCandidate:
    lane_id: str
    score: int
    current_slice_rank: int
    order_index: int
    span_index: int
    entry_id: str
    role: str
    excerpt: str


def build_history_evidence_ref(
    *,
    entry: HistoryLedgerEntry,
    excerpt: str,
) -> HistoryEvidenceRef:
    normalized_excerpt = excerpt.strip()
    if not normalized_excerpt:
        raise ValueError("excerpt must be non-empty")
    if normalized_excerpt not in entry.entry_text:
        raise ValueError("excerpt must be present in the referenced entry_text")
    return HistoryEvidenceRef(
        entry_id=entry.entry_id,
        role=entry.role,
        excerpt=normalized_excerpt,
    )


def build_history_odeu_reconstruction_packets(
    *,
    ledger: HistoryLedger,
    slices: list[HistorySlice],
    theme_anchors: list[HistoryThemeAnchor],
) -> list[HistoryODEUReconstructionPacket]:
    if not slices:
        raise ValueError("slices must be non-empty")
    if not theme_anchors:
        raise ValueError("theme_anchors must be non-empty")

    entry_lookup = {entry.entry_id: entry for entry in ledger.entries}
    slice_lookup = {item.slice_id: item for item in slices}
    if len(slice_lookup) != len(slices):
        raise ValueError("slices must have unique slice_id values")

    anchor_by_slice: dict[str, HistoryThemeAnchor] = {}
    for anchor in theme_anchors:
        for slice_id in anchor.slice_ids:
            if slice_id not in slice_lookup:
                raise ValueError("theme anchors must reference released slice ids")
            if slice_id in anchor_by_slice:
                raise ValueError("each released slice must resolve to exactly one theme anchor")
            anchor_by_slice[slice_id] = anchor

    if set(anchor_by_slice) != set(slice_lookup):
        raise ValueError("each released slice must resolve to exactly one theme anchor")

    ordered_slices = sorted(slices, key=lambda item: item.slice_index)
    packets: list[HistoryODEUReconstructionPacket] = []
    for current_slice in ordered_slices:
        theme_anchor = anchor_by_slice[current_slice.slice_id]
        current_entry_ids = set(current_slice.entry_ids)
        anchor_entries = sorted(
            [entry_lookup[entry_id] for entry_id in theme_anchor.anchor_entry_ids],
            key=lambda item: item.order_index,
        )
        has_user_anchor = any(entry.role == "user" for entry in anchor_entries)

        lane_reconstructions: list[HistoryODEULaneReconstruction] = []
        for lane_id in ODEU_LANE_ORDER:
            candidates = _lane_candidates(
                entries=anchor_entries,
                lane_id=lane_id,
                current_entry_ids=current_entry_ids,
            )
            if not candidates:
                lane_reconstructions.append(
                    HistoryODEULaneReconstruction(
                        lane_id=lane_id,
                        presence_status=_absent_lane_posture(entries=anchor_entries),
                        explicitation_status="underdetermined",
                        dominant_role_posture="none",
                    )
                )
                continue
            selected_candidates = candidates[:2]
            evidence_refs = [
                build_history_evidence_ref(
                    entry=entry_lookup[item.entry_id],
                    excerpt=item.excerpt,
                )
                for item in selected_candidates
            ]
            presence_status = _presence_status(candidates=candidates)
            explicitation_status = _explicitation_status(
                lane_id=lane_id,
                candidates=candidates,
                has_user_anchor=has_user_anchor,
            )
            dominant_role_posture = _dominant_role_posture(
                candidates=selected_candidates,
                has_user_anchor=has_user_anchor,
            )
            lane_reconstructions.append(
                HistoryODEULaneReconstruction(
                    lane_id=lane_id,
                    presence_status=presence_status,
                    explicitation_status=explicitation_status,
                    dominant_role_posture=dominant_role_posture,
                    reconstruction_text=_reconstruction_text(
                        presence_status=presence_status,
                        explicitation_status=explicitation_status,
                        candidates=selected_candidates,
                    ),
                    evidence_refs=evidence_refs,
                )
            )

        semantic_hash = compute_history_odeu_packet_semantic_hash(
            source_id=ledger.source_id,
            slice_id=current_slice.slice_id,
            theme_anchor_id=theme_anchor.theme_anchor_id,
            lane_reconstructions=lane_reconstructions,
        )
        packets.append(
            HistoryODEUReconstructionPacket(
                packet_id=compute_history_odeu_packet_id(semantic_hash=semantic_hash),
                source_id=ledger.source_id,
                slice_id=current_slice.slice_id,
                theme_anchor_id=theme_anchor.theme_anchor_id,
                lane_reconstructions=lane_reconstructions,
                semantic_hash=semantic_hash,
            )
        )

    validate_history_odeu_reconstruction_packets(
        ledger=ledger,
        slices=slices,
        theme_anchors=theme_anchors,
        packets=packets,
    )
    return packets


def validate_history_odeu_reconstruction_packets(
    *,
    ledger: HistoryLedger,
    slices: list[HistorySlice],
    theme_anchors: list[HistoryThemeAnchor],
    packets: list[HistoryODEUReconstructionPacket],
) -> None:
    if not packets:
        raise ValueError("packets must be non-empty")

    entry_lookup = {entry.entry_id: entry for entry in ledger.entries}
    slice_lookup = {item.slice_id: item for item in slices}
    if len(slice_lookup) != len(slices):
        raise ValueError("slices must have unique slice_id values")

    anchor_by_slice: dict[str, HistoryThemeAnchor] = {}
    for anchor in theme_anchors:
        for slice_id in anchor.slice_ids:
            if slice_id not in slice_lookup:
                raise ValueError("theme anchors must reference released slice ids")
            if slice_id in anchor_by_slice:
                raise ValueError("each released slice must resolve to exactly one theme anchor")
            anchor_by_slice[slice_id] = anchor

    packet_by_slice: dict[str, HistoryODEUReconstructionPacket] = {}
    for packet in packets:
        if packet.source_id != ledger.source_id:
            raise ValueError("packet source_id must match ledger source_id")
        if packet.slice_id in packet_by_slice:
            raise ValueError("packets must contain exactly one packet per released slice")
        if packet.slice_id not in slice_lookup:
            raise ValueError("packet slice_id must reference a released slice")
        expected_theme_anchor = anchor_by_slice.get(packet.slice_id)
        if expected_theme_anchor is None:
            raise ValueError("packet slice_id must resolve to a released theme anchor")
        if packet.theme_anchor_id != expected_theme_anchor.theme_anchor_id:
            raise ValueError("packet theme_anchor_id must match the released slice/theme mapping")
        packet_by_slice[packet.slice_id] = packet
        for lane in packet.lane_reconstructions:
            for evidence_ref in lane.evidence_refs:
                entry = entry_lookup.get(evidence_ref.entry_id)
                if entry is None:
                    raise ValueError("evidence_refs must reference released ledger entries")
                if evidence_ref.role != entry.role:
                    raise ValueError("evidence_ref role must match the released ledger entry role")
                if evidence_ref.excerpt not in entry.entry_text:
                    raise ValueError(
                        "evidence_ref excerpt must be present in the released ledger entry text"
                    )

    expected_slice_ids = [
        item.slice_id for item in sorted(slices, key=lambda item: item.slice_index)
    ]
    if sorted(packet_by_slice) != sorted(expected_slice_ids):
        raise ValueError("packets must contain exactly one packet per released slice")


def _lane_candidates(
    *,
    entries: list[HistoryLedgerEntry],
    lane_id: str,
    current_entry_ids: set[str],
) -> list[_LaneCandidate]:
    candidates: list[_LaneCandidate] = []
    for entry in entries:
        for span_index, span in enumerate(_candidate_spans(entry.entry_text)):
            score = _lane_score(span=span, lane_id=lane_id)
            if score <= 0:
                continue
            candidates.append(
                _LaneCandidate(
                    lane_id=lane_id,
                    score=score,
                    current_slice_rank=0 if entry.entry_id in current_entry_ids else 1,
                    order_index=entry.order_index,
                    span_index=span_index,
                    entry_id=entry.entry_id,
                    role=entry.role,
                    excerpt=span.strip(),
                )
            )
    ordered = sorted(
        candidates,
        key=lambda item: (
            -item.score,
            item.current_slice_rank,
            item.order_index,
            item.span_index,
            item.excerpt,
        ),
    )
    deduped: list[_LaneCandidate] = []
    seen: set[tuple[str, str]] = set()
    for item in ordered:
        key = (item.entry_id, item.excerpt)
        if key in seen:
            continue
        seen.add(key)
        deduped.append(item)
    return deduped


def _candidate_spans(text: str) -> list[str]:
    spans: list[str] = []
    for raw_line in text.split("\n"):
        line = raw_line.strip()
        if not line:
            continue
        explicit = _LANE_EXPLICIT_LINE_RE.match(line)
        if explicit is not None:
            spans.append(f"{explicit.group(1).upper()}: {explicit.group(2).strip()}")
            continue
        sentences = [piece.strip() for piece in _SENTENCE_SPLIT_RE.split(line) if piece.strip()]
        spans.extend(sentences or [line])
    return spans


def _lane_score(*, span: str, lane_id: str) -> int:
    explicit = _LANE_EXPLICIT_LINE_RE.match(span)
    if explicit is not None:
        return 8 if explicit.group(1).upper() == lane_id else 0
    lowered = span.casefold()
    score = 0
    for keyword in _LANE_KEYWORDS[lane_id]:
        if keyword in lowered:
            score += 2 if " " in keyword or "-" in keyword else 1
    if lane_id == "O" and _O_DEFINITION_RE.search(lowered) is not None:
        score += 1
    if lane_id == "E" and _E_EXPLICIT_RE.search(lowered) is not None:
        score += 1
    if lane_id == "D" and _D_EXPLICIT_RE.search(lowered) is not None:
        score += 1
    if lane_id == "U" and _U_EXPLICIT_RE.search(lowered) is not None:
        score += 1
    return score


def _presence_status(*, candidates: list[_LaneCandidate]) -> str:
    if not candidates:
        return "underdetermined"
    max_score = candidates[0].score
    if max_score >= 5 or (len(candidates) >= 2 and candidates[0].score + candidates[1].score >= 7):
        return "present"
    return "weakly_present"


def _explicitation_status(
    *,
    lane_id: str,
    candidates: list[_LaneCandidate],
    has_user_anchor: bool,
) -> str:
    if not candidates:
        return "underdetermined"
    top = candidates[0]
    if _has_explicit_lane_marker(top.excerpt, lane_id=lane_id) or top.score >= 4:
        if top.role == "assistant" and has_user_anchor:
            return "dialogically_explicitated"
        return "locally_explicit"
    if top.role == "assistant" and has_user_anchor:
        return "dialogically_explicitated"
    return "contextually_reconstructed"


def _has_explicit_lane_marker(span: str, *, lane_id: str) -> bool:
    explicit = _LANE_EXPLICIT_LINE_RE.match(span)
    return explicit is not None and explicit.group(1).upper() == lane_id


def _dominant_role_posture(
    *,
    candidates: list[_LaneCandidate],
    has_user_anchor: bool,
) -> str:
    roles = {item.role for item in candidates}
    if not roles:
        return "none"
    if roles == {"user"}:
        return "user_primary"
    if roles == {"assistant"}:
        return "assistant_explication" if has_user_anchor else "source_primary"
    if roles <= {"system"}:
        return "source_primary"
    return "mixed"


def _reconstruction_text(
    *,
    presence_status: str,
    explicitation_status: str,
    candidates: list[_LaneCandidate],
) -> str:
    excerpts = [_normalize_reconstruction_excerpt(item.excerpt) for item in candidates]
    joined = "; ".join(excerpts)
    if presence_status == "weakly_present" or explicitation_status == "contextually_reconstructed":
        return f"Contextually reconstructed from: {joined}"
    return joined


def _normalize_reconstruction_excerpt(text: str) -> str:
    normalized = re.sub(r"\s+", " ", text).strip()
    if normalized.endswith((".", "!", "?")):
        return normalized
    return f"{normalized}."


def _absent_lane_posture(*, entries: list[HistoryLedgerEntry]) -> str:
    combined = " ".join(entry.entry_text for entry in entries).casefold()
    if any(
        marker in combined
        for marker in ("odeu", "four lanes", "all four", "explicit lanes", "unclear", "?")
    ):
        return "underdetermined"
    return "not_salient"


__all__ = [
    "build_history_evidence_ref",
    "build_history_odeu_reconstruction_packets",
    "validate_history_odeu_reconstruction_packets",
]
