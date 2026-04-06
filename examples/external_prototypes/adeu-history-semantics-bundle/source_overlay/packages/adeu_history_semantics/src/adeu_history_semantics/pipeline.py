from __future__ import annotations

import re
from collections import Counter
from collections.abc import Iterable
from dataclasses import dataclass

from .models import (
    ASSISTANT_EXPLICATION_POSTURE,
    INTERPRETATION_AUTHORITY_POSTURE,
    INFERENTIAL_MATURITY_ORDER,
    LANE_ORDER,
    SEMANTIC_IDENTITY_MODE,
    SOURCE_AUTHORITY_POSTURE,
    THEME_SELECTION_POSTURE,
    HistoryEvidenceRef,
    HistoryLedger,
    HistoryLedgerEntry,
    HistoryODEULaneReconstruction,
    HistoryODEUReconstructionPacket,
    HistorySemanticBundle,
    HistorySlice,
    HistorySourceArtifact,
    HistoryThemeAnchor,
    HistoryWorkspaceQuestion,
    HistoryWorkspaceSnapshot,
    HistoryWorkspaceThemeFrame,
    compute_history_slice_id,
    compute_history_theme_anchor_id,
    compute_theme_key,
    sha256_canonical_json,
)
from .preclassify import build_history_ledger, build_history_source_artifact

_SENTENCE_SPLIT_RE = re.compile(r"(?<=[.!?])\s+")
_THEME_TOKEN_RE = re.compile(r"[a-z0-9][a-z0-9_-]{2,}")
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

_STOPWORDS = frozenset(
    {
        "about",
        "after",
        "again",
        "against",
        "all",
        "also",
        "and",
        "any",
        "are",
        "around",
        "because",
        "been",
        "before",
        "being",
        "between",
        "both",
        "bound",
        "build",
        "but",
        "can",
        "cannot",
        "clearly",
        "conversation",
        "could",
        "default",
        "deterministic",
        "dialogic",
        "does",
        "each",
        "explicit",
        "first",
        "for",
        "from",
        "have",
        "history-like",
        "into",
        "just",
        "keep",
        "later",
        "like",
        "make",
        "message",
        "messages",
        "module",
        "must",
        "need",
        "only",
        "our",
        "over",
        "packet",
        "packets",
        "preserve",
        "raw",
        "should",
        "slice",
        "slices",
        "some",
        "source",
        "style",
        "text",
        "that",
        "the",
        "their",
        "then",
        "there",
        "these",
        "this",
        "through",
        "turn",
        "user",
        "using",
        "what",
        "when",
        "with",
        "work",
        "workspace",
        "would",
    }
)

_THEME_BOOST_TERMS = frozenset(
    {
        "abstract",
        "anchor",
        "bootstrap",
        "chronology",
        "corpus",
        "epistemic",
        "epistemics",
        "inferential",
        "maturity",
        "ontology",
        "odeu",
        "provenance",
        "reconstruction",
        "semantic",
        "semantics",
        "substrate",
        "theme",
        "utility",
        "workspace",
    }
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
        "packet",
        "reconstruction",
        "slice",
        "substrate",
        "theme",
        "workspace",
    ),
    "E": (
        "authoritative",
        "confidence",
        "deterministic",
        "evidence",
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
        "used for",
    ),
}

_LANE_LONG_NAMES = {
    "O": "ontological lane",
    "E": "epistemic lane",
    "D": "deontic lane",
    "U": "utility lane",
}


@dataclass(frozen=True)
class _LaneCandidate:
    lane_id: str
    score: int
    order_index: int
    span_index: int
    entry_id: str
    role: str
    excerpt: str


def build_bounded_slices(*, ledger: HistoryLedger) -> list[HistorySlice]:
    groups: dict[str, list[HistoryLedgerEntry]] = {}
    for entry in ledger.entries:
        groups.setdefault(entry.preclassification.local_group_id, []).append(entry)

    ordered_group_ids = list(
        dict.fromkeys(entry.preclassification.local_group_id for entry in ledger.entries)
    )
    slices: list[HistorySlice] = []
    for slice_index, group_id in enumerate(ordered_group_ids):
        entries = sorted(groups[group_id], key=lambda item: item.preclassification.order_index)
        user_entries = [item for item in entries if item.preclassification.role == "user"]
        if user_entries:
            primary_entries = user_entries
            support_entries = [item for item in entries if item.preclassification.role != "user"]
        else:
            primary_entries = entries
            support_entries = []
        theme_terms = _extract_theme_terms(item.entry_text for item in primary_entries)
        if not theme_terms:
            theme_terms = [f"slice_{slice_index:04d}"]
        theme_label = " / ".join(theme_terms[:3])
        maturity_score = _inferential_maturity_score(entries)
        slice_id = compute_history_slice_id(
            source_id=ledger.source_id,
            slice_index=slice_index,
            primary_entry_ids=[item.entry_id for item in primary_entries],
            support_entry_ids=[item.entry_id for item in support_entries],
        )
        slices.append(
            HistorySlice(
                slice_id=slice_id,
                source_id=ledger.source_id,
                slice_index=slice_index,
                primary_entry_ids=[item.entry_id for item in primary_entries],
                support_entry_ids=[item.entry_id for item in support_entries],
                chronology_start_index=entries[0].preclassification.order_index,
                chronology_end_index=entries[-1].preclassification.order_index,
                suggested_theme_terms=theme_terms,
                suggested_theme_label=theme_label,
                inferential_maturity_score=maturity_score,
                inferential_maturity_band=_maturity_band_for_score(maturity_score),
                slice_notes=[f"local_group_id={group_id}"],
            )
        )
    return slices


def build_theme_anchors(
    *,
    ledger: HistoryLedger,
    slices: list[HistorySlice],
) -> list[HistoryThemeAnchor]:
    entry_lookup = {entry.entry_id: entry for entry in ledger.entries}
    aggregates: dict[str, dict[str, object]] = {}

    for current_slice in slices:
        primary_entries = [entry_lookup[entry_id] for entry_id in current_slice.primary_entry_ids]
        selection_posture = (
            "user_message_primary"
            if any(entry.preclassification.role == "user" for entry in primary_entries)
            else "source_fallback_primary"
        )
        theme_key = compute_theme_key(current_slice.suggested_theme_terms)
        aggregate = aggregates.setdefault(
            theme_key,
            {
                "selection_posture": selection_posture,
                "anchor_terms": list(current_slice.suggested_theme_terms),
                "primary_entry_ids": list(current_slice.primary_entry_ids),
                "support_entry_ids": list(current_slice.support_entry_ids),
                "slice_ids": [current_slice.slice_id],
            },
        )
        if (
            aggregate["selection_posture"] != "user_message_primary"
            and selection_posture == "user_message_primary"
        ):
            aggregate["selection_posture"] = selection_posture
        aggregate["anchor_terms"] = _ordered_unique(
            [*aggregate["anchor_terms"], *current_slice.suggested_theme_terms]
        )
        aggregate["primary_entry_ids"] = _ordered_unique(
            [*aggregate["primary_entry_ids"], *current_slice.primary_entry_ids]
        )
        aggregate["support_entry_ids"] = _ordered_unique(
            [*aggregate["support_entry_ids"], *current_slice.support_entry_ids]
        )
        aggregate["slice_ids"] = _ordered_unique([*aggregate["slice_ids"], current_slice.slice_id])

    anchors: list[HistoryThemeAnchor] = []
    for theme_key, aggregate in sorted(aggregates.items()):
        anchor_terms = list(aggregate["anchor_terms"])
        display_label = " / ".join(anchor_terms[:3])
        primary_entry_ids = list(aggregate["primary_entry_ids"])
        slice_ids = list(aggregate["slice_ids"])
        anchors.append(
            HistoryThemeAnchor(
                theme_anchor_id=compute_history_theme_anchor_id(
                    source_id=ledger.source_id,
                    theme_key=theme_key,
                    primary_entry_ids=primary_entry_ids,
                    slice_ids=slice_ids,
                ),
                source_id=ledger.source_id,
                theme_key=theme_key,
                display_label=display_label,
                selection_posture=str(aggregate["selection_posture"]),
                anchor_terms=anchor_terms,
                primary_entry_ids=primary_entry_ids,
                support_entry_ids=list(aggregate["support_entry_ids"]),
                slice_ids=slice_ids,
            )
        )
    return anchors


def build_odeu_reconstruction_packets(
    *,
    ledger: HistoryLedger,
    slices: list[HistorySlice],
    theme_anchors: list[HistoryThemeAnchor],
) -> list[HistoryODEUReconstructionPacket]:
    entry_lookup = {entry.entry_id: entry for entry in ledger.entries}
    anchor_by_slice: dict[str, HistoryThemeAnchor] = {}
    for anchor in theme_anchors:
        for slice_id in anchor.slice_ids:
            anchor_by_slice[slice_id] = anchor

    packets: list[HistoryODEUReconstructionPacket] = []
    for current_slice in slices:
        theme_anchor = anchor_by_slice[current_slice.slice_id]
        entries = [
            entry_lookup[entry_id]
            for entry_id in [*current_slice.primary_entry_ids, *current_slice.support_entry_ids]
        ]
        entries = sorted(entries, key=lambda item: item.preclassification.order_index)
        has_user_anchor = any(entry.preclassification.role == "user" for entry in entries)
        lane_models: list[HistoryODEULaneReconstruction] = []
        for lane_id in LANE_ORDER:
            candidates = _lane_candidates(entries=entries, lane_id=lane_id)
            if not candidates:
                presence_status = _absent_lane_posture(entries=entries)
                lane_models.append(
                    HistoryODEULaneReconstruction(
                        lane_id=lane_id,
                        presence_status=presence_status,
                        explicitation_status="underdetermined",
                        dominant_role_posture="none",
                        reconstruction_text=_absent_lane_text(
                            lane_id=lane_id,
                            presence_status=presence_status,
                        ),
                        evidence_refs=[],
                    )
                )
                continue
            evidence_refs = [
                HistoryEvidenceRef(entry_id=item.entry_id, role=item.role, excerpt=item.excerpt)
                for item in candidates[:2]
            ]
            presence_status = _presence_status(candidates=candidates)
            explicitation_status = _explicitation_status(
                lane_id=lane_id,
                candidates=candidates,
                has_user_anchor=has_user_anchor,
            )
            dominant_role_posture = _dominant_role_posture(
                candidates=candidates[:2],
                has_user_anchor=has_user_anchor,
            )
            lane_models.append(
                HistoryODEULaneReconstruction(
                    lane_id=lane_id,
                    presence_status=presence_status,
                    explicitation_status=explicitation_status,
                    dominant_role_posture=dominant_role_posture,
                    reconstruction_text=_reconstruction_text(
                        lane_id=lane_id,
                        presence_status=presence_status,
                        explicitation_status=explicitation_status,
                        candidates=candidates[:2],
                    ),
                    evidence_refs=evidence_refs,
                )
            )
        reintegrated_summary = _reintegrated_summary(
            theme_anchor=theme_anchor,
            lane_models=lane_models,
        )
        packet_basis = _packet_identity_basis(
            source_id=ledger.source_id,
            slice_id=current_slice.slice_id,
            theme_anchor_id=theme_anchor.theme_anchor_id,
            lane_models=lane_models,
            reintegrated_summary=reintegrated_summary,
        )
        semantic_hash = sha256_canonical_json(packet_basis)
        packets.append(
            HistoryODEUReconstructionPacket(
                packet_id=f"history_packet:{semantic_hash[:16]}",
                source_id=ledger.source_id,
                slice_id=current_slice.slice_id,
                theme_anchor_id=theme_anchor.theme_anchor_id,
                lane_reconstructions=lane_models,
                reintegrated_summary=reintegrated_summary,
                interpretation_authority_posture=INTERPRETATION_AUTHORITY_POSTURE,
                semantic_identity_mode=SEMANTIC_IDENTITY_MODE,
                semantic_hash=semantic_hash,
            )
        )
    return packets


def build_workspace_snapshot(
    *,
    source: HistorySourceArtifact,
    ledger: HistoryLedger,
    slices: list[HistorySlice],
    theme_anchors: list[HistoryThemeAnchor],
    packets: list[HistoryODEUReconstructionPacket],
) -> HistoryWorkspaceSnapshot:
    entry_lookup = {entry.entry_id: entry for entry in ledger.entries}
    slice_lookup = {item.slice_id: item for item in slices}
    packets_by_theme: dict[str, list[HistoryODEUReconstructionPacket]] = {}
    for packet in packets:
        packets_by_theme.setdefault(packet.theme_anchor_id, []).append(packet)

    theme_frames: list[HistoryWorkspaceThemeFrame] = []
    for anchor in theme_anchors:
        anchor_packets = sorted(
            packets_by_theme.get(anchor.theme_anchor_id, []),
            key=lambda item: slice_lookup[item.slice_id].chronology_start_index,
        )
        anchor_slices = [slice_lookup[slice_id] for slice_id in anchor.slice_ids]
        chronology_start = min(item.chronology_start_index for item in anchor_slices)
        chronology_end = max(item.chronology_end_index for item in anchor_slices)
        underdeveloped_lane_ids = _ordered_unique(
            [
                lane.lane_id
                for packet in anchor_packets
                for lane in packet.lane_reconstructions
                if lane.presence_status in {"weakly_present", "underdetermined"}
            ]
        )
        open_questions = _workspace_questions(
            theme_display_label=anchor.display_label,
            anchor_packets=anchor_packets,
        )
        provenance_entry_ids = _ordered_provenance_entry_ids(
            anchor=anchor,
            anchor_slices=anchor_slices,
            anchor_packets=anchor_packets,
            entry_lookup=entry_lookup,
        )
        maturity_band = _max_maturity_band(item.inferential_maturity_band for item in anchor_slices)
        frame_basis = _frame_identity_basis(
            theme_anchor_id=anchor.theme_anchor_id,
            slice_ids=[item.slice_id for item in anchor_slices],
            packet_ids=[item.packet_id for item in anchor_packets],
            chronology_start_index=chronology_start,
            chronology_end_index=chronology_end,
            inferential_maturity_band=maturity_band,
            underdeveloped_lane_ids=underdeveloped_lane_ids,
            provenance_entry_ids=provenance_entry_ids,
            open_questions=open_questions,
        )
        theme_frames.append(
            HistoryWorkspaceThemeFrame(
                frame_id=f"history_frame:{sha256_canonical_json(frame_basis)[:16]}",
                theme_anchor_id=anchor.theme_anchor_id,
                theme_display_label=anchor.display_label,
                slice_ids=[item.slice_id for item in anchor_slices],
                packet_ids=[item.packet_id for item in anchor_packets],
                chronology_start_index=chronology_start,
                chronology_end_index=chronology_end,
                inferential_maturity_band=maturity_band,
                underdeveloped_lane_ids=underdeveloped_lane_ids,
                provenance_entry_ids=provenance_entry_ids,
                open_questions=open_questions,
            )
        )

    chronology_slice_order = [
        item.slice_id
        for item in sorted(
            slices,
            key=lambda item: (item.chronology_start_index, item.slice_index, item.slice_id),
        )
    ]
    inferential_slice_order = [
        item.slice_id
        for item in sorted(
            slices,
            key=lambda item: (
                -item.inferential_maturity_score,
                item.chronology_start_index,
                item.slice_id,
            ),
        )
    ]
    ordered_theme_frames = sorted(theme_frames, key=lambda item: item.theme_anchor_id)
    workspace_basis = _workspace_identity_basis(
        source_id=source.source_id,
        ledger_id=ledger.ledger_id,
        chronology_slice_order=chronology_slice_order,
        inferential_slice_order=inferential_slice_order,
        theme_frames=ordered_theme_frames,
    )
    semantic_hash = sha256_canonical_json(workspace_basis)
    return HistoryWorkspaceSnapshot(
        workspace_snapshot_id=f"history_workspace:{semantic_hash[:16]}",
        source_id=source.source_id,
        ledger_id=ledger.ledger_id,
        chronology_slice_order=chronology_slice_order,
        inferential_slice_order=inferential_slice_order,
        theme_frames=ordered_theme_frames,
        lane_order=list(LANE_ORDER),
        source_authority_posture=SOURCE_AUTHORITY_POSTURE,
        interpretation_authority_posture=INTERPRETATION_AUTHORITY_POSTURE,
        theme_selection_posture=THEME_SELECTION_POSTURE,
        assistant_explication_posture=ASSISTANT_EXPLICATION_POSTURE,
        semantic_identity_mode=SEMANTIC_IDENTITY_MODE,
        semantic_hash=semantic_hash,
    )


def compile_history_semantic_bundle(
    *,
    source_text: str,
    input_kind: str,
    source_label: str | None = None,
    corpus_wave_posture: str = "unassigned",
    source_notes: list[str] | None = None,
    compiler_version: str = "v0",
) -> HistorySemanticBundle:
    source = build_history_source_artifact(
        source_text=source_text,
        input_kind=input_kind,
        source_label=source_label,
        corpus_wave_posture=corpus_wave_posture,
        source_notes=source_notes,
    )
    return compile_history_semantic_bundle_from_source(
        source=source,
        compiler_version=compiler_version,
    )


def compile_history_semantic_bundle_from_source(
    *,
    source: HistorySourceArtifact,
    compiler_version: str = "v0",
) -> HistorySemanticBundle:
    ledger = build_history_ledger(source=source)
    slices = build_bounded_slices(ledger=ledger)
    theme_anchors = build_theme_anchors(ledger=ledger, slices=slices)
    packets = build_odeu_reconstruction_packets(
        ledger=ledger,
        slices=slices,
        theme_anchors=theme_anchors,
    )
    workspace_snapshot = build_workspace_snapshot(
        source=source,
        ledger=ledger,
        slices=slices,
        theme_anchors=theme_anchors,
        packets=packets,
    )
    ordered_slices = sorted(slices, key=lambda item: item.slice_index)
    ordered_theme_anchors = sorted(theme_anchors, key=lambda item: item.theme_key)
    ordered_packets = sorted(packets, key=lambda item: item.slice_id)
    bundle_id = _bundle_id(
        compiler_version=compiler_version,
        source_id=source.source_id,
        ledger_id=ledger.ledger_id,
        slice_ids=[item.slice_id for item in ordered_slices],
        theme_anchor_ids=[item.theme_anchor_id for item in ordered_theme_anchors],
        packet_ids=[item.packet_id for item in ordered_packets],
        workspace_snapshot_id=workspace_snapshot.workspace_snapshot_id,
    )
    return HistorySemanticBundle(
        bundle_id=bundle_id,
        compiler_version=compiler_version,
        source=source,
        ledger=ledger,
        slices=ordered_slices,
        theme_anchors=ordered_theme_anchors,
        reconstruction_packets=ordered_packets,
        workspace_snapshot=workspace_snapshot,
    )


def _extract_theme_terms(texts: Iterable[str]) -> list[str]:
    counts: Counter[str] = Counter()
    first_seen: dict[str, tuple[int, int]] = {}
    text_list = list(texts)
    for text_index, text in enumerate(text_list):
        tokens = _theme_tokens(text)
        for token_index, token in enumerate(tokens):
            if token in _STOPWORDS:
                continue
            score = 1
            if token in _THEME_BOOST_TERMS:
                score += 2
            if token_index < 12:
                score += 1
            counts[token] += score
            first_seen.setdefault(token, (text_index, token_index))
    ordered = sorted(
        counts,
        key=lambda item: (-counts[item], first_seen[item][0], first_seen[item][1], item),
    )
    return ordered[:4]


def _theme_tokens(text: str) -> list[str]:
    lowered = text.casefold().replace("/", " ")
    return [token for token in _THEME_TOKEN_RE.findall(lowered) if len(token) >= 3]


def _inferential_maturity_score(entries: list[HistoryLedgerEntry]) -> int:
    score = 0
    for entry in entries:
        signals = set(entry.preclassification.structural_markers)
        if entry.preclassification.role == "assistant":
            score += 2
        if "odeu_marker_present" in signals:
            score += 2
        if "definition_pattern_present" in signals:
            score += 1
        if "imperative_signal_present" in signals:
            score += 1
        if "negation_guard_present" in signals:
            score += 1
        if entry.preclassification.text_shape_signals.sentence_count >= 2:
            score += 1
        if entry.preclassification.text_shape_signals.word_count >= 30:
            score += 1
        if (
            entry.preclassification.role == "user"
            and "question_mark_present" in signals
            and score > 0
        ):
            score -= 1
    return max(score, 0)


def _maturity_band_for_score(score: int) -> str:
    if score >= 7:
        return "consolidated"
    if score >= 4:
        return "explicit"
    if score >= 2:
        return "developing"
    return "emergent"


def _lane_candidates(*, entries: list[HistoryLedgerEntry], lane_id: str) -> list[_LaneCandidate]:
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
                    order_index=entry.preclassification.order_index,
                    span_index=span_index,
                    entry_id=entry.entry_id,
                    role=entry.preclassification.role,
                    excerpt=_normalize_excerpt(span),
                )
            )
    ordered = sorted(
        candidates,
        key=lambda item: (-item.score, item.order_index, item.span_index, item.excerpt),
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
    if _has_explicit_lane_marker(top.excerpt, lane_id=lane_id) or _lane_score(
        span=top.excerpt, lane_id=lane_id
    ) >= 4:
        if top.role == "assistant" and has_user_anchor:
            return "dialogically_explicitated"
        return "locally_explicit"
    if top.role == "assistant" and has_user_anchor:
        return "dialogically_explicitated"
    return "contextually_reconstructed"


def _has_explicit_lane_marker(span: str, *, lane_id: str) -> bool:
    explicit = _LANE_EXPLICIT_LINE_RE.match(span)
    return explicit is not None and explicit.group(1).upper() == lane_id


def _dominant_role_posture(*, candidates: list[_LaneCandidate], has_user_anchor: bool) -> str:
    roles = {item.role for item in candidates}
    if not roles:
        return "none"
    if roles == {"user"}:
        return "user_primary"
    if roles == {"assistant"}:
        return "assistant_explication" if has_user_anchor else "source_primary"
    if roles <= {"unknown", "system"}:
        return "source_primary"
    return "mixed"


def _reconstruction_text(
    *,
    lane_id: str,
    presence_status: str,
    explicitation_status: str,
    candidates: list[_LaneCandidate],
) -> str:
    if presence_status in {"underdetermined", "not_salient"}:
        return _absent_lane_text(lane_id=lane_id, presence_status=presence_status)
    excerpts = [_normalize_excerpt(item.excerpt) for item in candidates]
    joined = "; ".join(excerpts)
    if explicitation_status == "contextually_reconstructed":
        return f"Contextually reconstructed from: {joined}"
    return joined


def _absent_lane_posture(*, entries: list[HistoryLedgerEntry]) -> str:
    combined = " ".join(entry.entry_text for entry in entries).casefold()
    expects_full_lane_build = any(
        marker in combined for marker in ("odeu", "four lanes", "all four", "explicit lanes")
    )
    if (
        expects_full_lane_build
        or "?" in combined
        or "unclear" in combined
        or "underdetermined" in combined
    ):
        return "underdetermined"
    return "not_salient"


def _absent_lane_text(*, lane_id: str, presence_status: str) -> str:
    if presence_status == "underdetermined":
        return (
            f"{_LANE_LONG_NAMES[lane_id]} remains underdetermined "
            "from the available local material."
        )
    return f"{_LANE_LONG_NAMES[lane_id]} is not salient in this slice."


def _reintegrated_summary(
    *,
    theme_anchor: HistoryThemeAnchor,
    lane_models: list[HistoryODEULaneReconstruction],
) -> str:
    parts = [
        f"{lane.lane_id}: {lane.presence_status}"
        for lane in lane_models
        if lane.presence_status in {"present", "weakly_present"}
    ]
    if not parts:
        parts = [f"{lane.lane_id}: {lane.presence_status}" for lane in lane_models]
    return f"{theme_anchor.display_label} -> " + "; ".join(parts)


def _workspace_questions(
    *,
    theme_display_label: str,
    anchor_packets: list[HistoryODEUReconstructionPacket],
) -> list[HistoryWorkspaceQuestion]:
    questions: list[HistoryWorkspaceQuestion] = []
    seen: set[tuple[str, str]] = set()
    for packet in anchor_packets:
        for lane in packet.lane_reconstructions:
            if lane.presence_status not in {"weakly_present", "underdetermined"}:
                continue
            reason_kind = (
                "weak_lane"
                if lane.presence_status == "weakly_present"
                else "underdetermined_lane"
            )
            question_text = (
                f"{_LANE_LONG_NAMES[lane.lane_id]} for theme '{theme_display_label}' is "
                f"{lane.presence_status}; collect more explicit local material "
                "or later explication."
            )
            key = (lane.lane_id, reason_kind)
            if key in seen:
                continue
            seen.add(key)
            basis = {
                "lane_id": lane.lane_id,
                "reason_kind": reason_kind,
                "question_text": question_text,
            }
            questions.append(
                HistoryWorkspaceQuestion(
                    question_id=f"history_question:{sha256_canonical_json(basis)[:16]}",
                    lane_id=lane.lane_id,
                    reason_kind=reason_kind,
                    question_text=question_text,
                )
            )
    return questions


def _ordered_provenance_entry_ids(
    *,
    anchor: HistoryThemeAnchor,
    anchor_slices: list[HistorySlice],
    anchor_packets: list[HistoryODEUReconstructionPacket],
    entry_lookup: dict[str, HistoryLedgerEntry],
) -> list[str]:
    candidate_ids = [
        *anchor.primary_entry_ids,
        *anchor.support_entry_ids,
        *[
            entry_id
            for item in anchor_slices
            for entry_id in [*item.primary_entry_ids, *item.support_entry_ids]
        ],
        *[
            evidence.entry_id
            for packet in anchor_packets
            for lane in packet.lane_reconstructions
            for evidence in lane.evidence_refs
        ],
    ]
    unique_ids = _ordered_unique(candidate_ids)
    return sorted(unique_ids, key=lambda item: entry_lookup[item].preclassification.order_index)


def _max_maturity_band(bands: Iterable[str]) -> str:
    order = {name: index for index, name in enumerate(INFERENTIAL_MATURITY_ORDER)}
    band_list = list(bands)
    return max(band_list, key=lambda item: order[item])


def _ordered_unique(values: list[str]) -> list[str]:
    seen: set[str] = set()
    ordered: list[str] = []
    for value in values:
        if value not in seen:
            seen.add(value)
            ordered.append(value)
    return ordered


def _normalize_excerpt(text: str) -> str:
    normalized = re.sub(r"\s+", " ", text).strip()
    if normalized.endswith((".", "!", "?")):
        return normalized
    return f"{normalized}."


def _packet_identity_basis(
    *,
    source_id: str,
    slice_id: str,
    theme_anchor_id: str,
    lane_models: list[HistoryODEULaneReconstruction],
    reintegrated_summary: str,
) -> dict[str, object]:
    return {
        "schema": "adeu_history_odeu_reconstruction_packet@1",
        "source_id": source_id,
        "slice_id": slice_id,
        "theme_anchor_id": theme_anchor_id,
        "lane_reconstructions": [
            {
                "lane_id": lane.lane_id,
                "presence_status": lane.presence_status,
                "explicitation_status": lane.explicitation_status,
                "dominant_role_posture": lane.dominant_role_posture,
                "reconstruction_text": lane.reconstruction_text,
                "evidence_refs": [
                    {
                        "entry_id": item.entry_id,
                        "role": item.role,
                        "excerpt": item.excerpt,
                    }
                    for item in lane.evidence_refs
                ],
            }
            for lane in lane_models
        ],
        "reintegrated_summary": reintegrated_summary,
        "semantic_identity_mode": SEMANTIC_IDENTITY_MODE,
    }


def _frame_identity_basis(
    *,
    theme_anchor_id: str,
    slice_ids: list[str],
    packet_ids: list[str],
    chronology_start_index: int,
    chronology_end_index: int,
    inferential_maturity_band: str,
    underdeveloped_lane_ids: list[str],
    provenance_entry_ids: list[str],
    open_questions: list[HistoryWorkspaceQuestion],
) -> dict[str, object]:
    return {
        "theme_anchor_id": theme_anchor_id,
        "slice_ids": slice_ids,
        "packet_ids": packet_ids,
        "chronology_start_index": chronology_start_index,
        "chronology_end_index": chronology_end_index,
        "inferential_maturity_band": inferential_maturity_band,
        "underdeveloped_lane_ids": underdeveloped_lane_ids,
        "provenance_entry_ids": provenance_entry_ids,
        "open_questions": [
            {
                "lane_id": question.lane_id,
                "reason_kind": question.reason_kind,
                "question_text": question.question_text,
            }
            for question in open_questions
        ],
    }


def _workspace_identity_basis(
    *,
    source_id: str,
    ledger_id: str,
    chronology_slice_order: list[str],
    inferential_slice_order: list[str],
    theme_frames: list[HistoryWorkspaceThemeFrame],
) -> dict[str, object]:
    return {
        "schema": "adeu_history_workspace_snapshot@1",
        "source_id": source_id,
        "ledger_id": ledger_id,
        "chronology_slice_order": chronology_slice_order,
        "inferential_slice_order": inferential_slice_order,
        "theme_frames": [
            {
                "theme_anchor_id": frame.theme_anchor_id,
                "slice_ids": frame.slice_ids,
                "packet_ids": frame.packet_ids,
                "chronology_start_index": frame.chronology_start_index,
                "chronology_end_index": frame.chronology_end_index,
                "inferential_maturity_band": frame.inferential_maturity_band,
                "underdeveloped_lane_ids": frame.underdeveloped_lane_ids,
                "provenance_entry_ids": frame.provenance_entry_ids,
                "open_questions": [
                    {
                        "lane_id": question.lane_id,
                        "reason_kind": question.reason_kind,
                        "question_text": question.question_text,
                    }
                    for question in frame.open_questions
                ],
            }
            for frame in theme_frames
        ],
        "lane_order": list(LANE_ORDER),
        "semantic_identity_mode": SEMANTIC_IDENTITY_MODE,
    }


def _bundle_id(
    *,
    compiler_version: str,
    source_id: str,
    ledger_id: str,
    slice_ids: list[str],
    theme_anchor_ids: list[str],
    packet_ids: list[str],
    workspace_snapshot_id: str,
) -> str:
    basis = {
        "schema": "adeu_history_semantic_bundle@1",
        "compiler_version": compiler_version,
        "source_id": source_id,
        "ledger_id": ledger_id,
        "slice_ids": slice_ids,
        "theme_anchor_ids": theme_anchor_ids,
        "packet_ids": packet_ids,
        "workspace_snapshot_id": workspace_snapshot_id,
    }
    return f"history_bundle:{sha256_canonical_json(basis)[:16]}"


__all__ = [
    "build_bounded_slices",
    "build_odeu_reconstruction_packets",
    "build_theme_anchors",
    "build_workspace_snapshot",
    "compile_history_semantic_bundle",
    "compile_history_semantic_bundle_from_source",
]
