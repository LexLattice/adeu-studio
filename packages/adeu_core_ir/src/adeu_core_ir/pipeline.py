from __future__ import annotations

import hashlib
import json
import re
from copy import deepcopy
from dataclasses import dataclass, field
from typing import Any

from adeu_ir import SourceSpan
from pydantic import TypeAdapter

from .ids import stable_core_node_id
from .models import (
    AdeuCoreIR,
    CoreDNode,
    CoreEdge,
    CoreENode,
    CoreNode,
    CoreONode,
    CoreUNode,
    canonical_edge_sort_key,
    canonical_node_sort_key,
    canonicalize_core_ir_payload,
)

_CORE_NODE_ADAPTER = TypeAdapter(CoreNode)
_SENTENCE_RE = re.compile(r"[^.!?]+(?:[.!?]+|$)")
_TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9_-]{2,}")

_STOPWORDS = {
    "the",
    "and",
    "for",
    "with",
    "that",
    "this",
    "from",
    "are",
    "was",
    "were",
    "have",
    "has",
    "had",
    "will",
    "would",
    "can",
    "could",
    "should",
    "must",
    "may",
    "might",
    "into",
    "about",
    "over",
    "under",
    "after",
    "before",
    "while",
    "where",
    "which",
    "when",
    "than",
    "their",
    "there",
    "these",
    "those",
    "such",
    "also",
}

_FORBIDDEN_MODAL_RE = re.compile(r"\b(must not|shall not|forbidden|prohibited|cannot|can't)\b")
_OBLIGATORY_MODAL_RE = re.compile(r"\b(must|shall|required|obliged)\b")
_PERMISSION_MODAL_RE = re.compile(r"\b(may|can|allowed|permitted)\b")
_EXCEPTION_RE = re.compile(r"\b(unless|except|except when)\b")
_GOAL_RE = re.compile(r"\b(goal|objective|aim|improve|protect|support)\b")
_METRIC_RE = re.compile(r"\b(maximize|minimize|reduce|increase|decrease|optimize)\b")
_PREFERENCE_RE = re.compile(r"\b(prefer|priority|prioritize)\b")


def _canonical_json(value: object) -> str:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def _sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _normalize_whitespace(text: str) -> str:
    return " ".join(text.split()).strip()


def _normalize_primary_key_text(text: str) -> str:
    return _normalize_whitespace(text).lower()


def _display_text_sort_key(text: str) -> tuple[str, str]:
    normalized = _normalize_whitespace(text)
    return (_normalize_primary_key_text(normalized), normalized)


def _canonical_span_pairs(spans: list[SourceSpan]) -> list[tuple[int, int]]:
    pairs = sorted({(span.start, span.end) for span in spans})
    if not pairs:
        return []
    merged: list[tuple[int, int]] = [pairs[0]]
    for start, end in pairs[1:]:
        prev_start, prev_end = merged[-1]
        if start <= prev_end:
            merged[-1] = (prev_start, max(prev_end, end))
            continue
        merged.append((start, end))
    return merged


def _canonical_spans(spans: list[SourceSpan]) -> list[SourceSpan]:
    return [SourceSpan(start=start, end=end) for start, end in _canonical_span_pairs(spans)]


def _node_primary_text(node: CoreNode) -> str:
    if isinstance(node, CoreENode):
        return node.text
    return node.label


def _node_spans(node: CoreNode) -> list[SourceSpan]:
    if isinstance(node, CoreENode):
        return _canonical_spans(list(node.spans))
    return []


@dataclass(frozen=True)
class NormalizedCoreSourceText:
    raw_text: str
    normalized_text: str
    source_text_hash: str
    _raw_to_normalized_offsets: tuple[int, ...] = field(repr=False)

    def to_normalized_offset(self, raw_offset: int) -> int:
        if raw_offset < 0 or raw_offset > len(self.raw_text):
            raise ValueError(f"raw_offset {raw_offset} out of range")
        return self._raw_to_normalized_offsets[raw_offset]

    def to_normalized_span(self, span: SourceSpan | dict[str, int]) -> SourceSpan:
        source_span = span if isinstance(span, SourceSpan) else SourceSpan.model_validate(span)
        normalized_start = self.to_normalized_offset(source_span.start)
        normalized_end = self.to_normalized_offset(source_span.end)
        return SourceSpan(start=normalized_start, end=normalized_end)


def normalize_core_source_text(source_text: str) -> NormalizedCoreSourceText:
    if not source_text:
        return NormalizedCoreSourceText(
            raw_text=source_text,
            normalized_text="",
            source_text_hash=_sha256_text(""),
            _raw_to_normalized_offsets=(0,),
        )

    tokens = list(re.finditer(r"\S+", source_text))
    if not tokens:
        offsets = tuple(0 for _ in range(len(source_text) + 1))
        return NormalizedCoreSourceText(
            raw_text=source_text,
            normalized_text="",
            source_text_hash=_sha256_text(""),
            _raw_to_normalized_offsets=offsets,
        )

    token_texts = [match.group(0) for match in tokens]
    normalized_text = " ".join(token_texts)
    normalized_length = len(normalized_text)
    offsets = [0] * (len(source_text) + 1)

    first_start = tokens[0].start()
    for idx in range(0, first_start + 1):
        offsets[idx] = 0

    output_prefix = 0
    for token_index, token in enumerate(tokens):
        token_start = token.start()
        token_end = token.end()
        output_start = output_prefix + token_index
        token_length = token_end - token_start

        for boundary in range(token_start, token_end + 1):
            offsets[boundary] = output_start + (boundary - token_start)

        if token_index + 1 < len(tokens):
            next_start = tokens[token_index + 1].start()
            output_end = output_start + token_length
            for boundary in range(token_end, next_start):
                offsets[boundary] = output_end
        else:
            for boundary in range(token_end, len(source_text) + 1):
                offsets[boundary] = normalized_length
        output_prefix += token_length

    return NormalizedCoreSourceText(
        raw_text=source_text,
        normalized_text=normalized_text,
        source_text_hash=_sha256_text(normalized_text),
        _raw_to_normalized_offsets=tuple(offsets),
    )


def harvest_core_ir_candidates(
    source: NormalizedCoreSourceText | str,
    *,
    max_concepts: int = 12,
) -> dict[str, Any]:
    normalized_text = (
        source.normalized_text if isinstance(source, NormalizedCoreSourceText) else source
    )
    normalized_text = _normalize_whitespace(normalized_text)

    nodes: list[dict[str, Any]] = []
    edges: list[dict[str, Any]] = []

    sentence_entries: list[tuple[str, SourceSpan]] = []
    for match in _SENTENCE_RE.finditer(normalized_text):
        segment = match.group(0)
        stripped = segment.strip()
        if not stripped:
            continue
        leading_ws = len(segment) - len(segment.lstrip())
        trailing_ws = len(segment) - len(segment.rstrip())
        start = match.start() + leading_ws
        end = match.end() - trailing_ws
        sentence_entries.append((stripped, SourceSpan(start=start, end=end)))

    claim_ids: list[str] = []
    for index, (sentence, span) in enumerate(sentence_entries):
        claim_id = f"cand_e_claim_{index:04d}"
        claim_ids.append(claim_id)
        nodes.append(
            {
                "id": claim_id,
                "layer": "E",
                "kind": "Claim",
                "text": sentence,
                "spans": [span.model_dump(mode="json")],
            }
        )

    token_counts: dict[str, int] = {}
    for token in _TOKEN_RE.findall(normalized_text):
        lowered = token.lower()
        if lowered in _STOPWORDS:
            continue
        token_counts[lowered] = token_counts.get(lowered, 0) + 1
    selected_concepts = sorted(token_counts.items(), key=lambda item: (-item[1], item[0]))[
        :max_concepts
    ]

    concept_ids: dict[str, str] = {}
    for token, _count in selected_concepts:
        concept_id = f"cand_o_concept_{token}"
        concept_ids[token] = concept_id
        nodes.append({"id": concept_id, "layer": "O", "kind": "Concept", "label": token})

    latest_deontic_id: str | None = None
    for index, (sentence, _span) in enumerate(sentence_entries):
        sentence_lower = sentence.lower()
        claim_id = claim_ids[index]
        sentence_tokens = {token.lower() for token in _TOKEN_RE.findall(sentence)}

        for token in sorted(sentence_tokens):
            concept_id = concept_ids.get(token)
            if concept_id is not None:
                edges.append({"type": "about", "from": claim_id, "to": concept_id})

        deontic_id: str | None = None
        if _FORBIDDEN_MODAL_RE.search(sentence_lower):
            deontic_id = f"cand_d_norm_forbidden_{index:04d}"
            nodes.append(
                {
                    "id": deontic_id,
                    "layer": "D",
                    "kind": "Norm",
                    "label": sentence,
                    "modality": "forbidden",
                }
            )
        elif _OBLIGATORY_MODAL_RE.search(sentence_lower):
            deontic_id = f"cand_d_norm_obligatory_{index:04d}"
            nodes.append(
                {
                    "id": deontic_id,
                    "layer": "D",
                    "kind": "Norm",
                    "label": sentence,
                    "modality": "obligatory",
                }
            )
        elif _PERMISSION_MODAL_RE.search(sentence_lower):
            deontic_id = f"cand_d_policy_permitted_{index:04d}"
            nodes.append(
                {
                    "id": deontic_id,
                    "layer": "D",
                    "kind": "Policy",
                    "label": sentence,
                    "modality": "permitted",
                }
            )

        if deontic_id is not None:
            latest_deontic_id = deontic_id
            edges.append({"type": "justifies", "from": claim_id, "to": deontic_id})

        if _EXCEPTION_RE.search(sentence_lower) and latest_deontic_id is not None:
            exception_id = f"cand_d_exception_{index:04d}"
            nodes.append(
                {
                    "id": exception_id,
                    "layer": "D",
                    "kind": "Exception",
                    "label": sentence,
                    "priority": 0,
                }
            )
            edges.append({"type": "excepts", "from": exception_id, "to": latest_deontic_id})

        utility_id: str | None = None
        utility_kind: str | None = None
        if _PREFERENCE_RE.search(sentence_lower):
            utility_id = f"cand_u_preference_{index:04d}"
            utility_kind = "Preference"
        elif _METRIC_RE.search(sentence_lower):
            utility_id = f"cand_u_metric_{index:04d}"
            utility_kind = "Metric"
        elif _GOAL_RE.search(sentence_lower):
            utility_id = f"cand_u_goal_{index:04d}"
            utility_kind = "Goal"

        if utility_id is not None and utility_kind is not None:
            nodes.append(
                {
                    "id": utility_id,
                    "layer": "U",
                    "kind": utility_kind,
                    "label": sentence,
                }
            )
            if utility_kind == "Preference":
                if latest_deontic_id is not None:
                    edges.append(
                        {"type": "prioritizes", "from": utility_id, "to": latest_deontic_id}
                    )
            elif deontic_id is not None:
                edges.append({"type": "serves_goal", "from": deontic_id, "to": utility_id})
            else:
                edges.append({"type": "serves_goal", "from": claim_id, "to": utility_id})

    return {"nodes": nodes, "edges": edges}


@dataclass(frozen=True)
class _CandidateNode:
    node: CoreNode
    duplicate_key: tuple[str, str, str, str]
    canonical_stable_id: str
    tie_break_payload: str


def _candidate_node(node_payload: dict[str, Any], *, source_text_hash: str) -> _CandidateNode:
    node = _CORE_NODE_ADAPTER.validate_python(node_payload)
    primary_text = _node_primary_text(node)
    duplicate_key = (
        node.layer,
        node.kind,
        _normalize_primary_key_text(primary_text),
        source_text_hash,
    )
    canonical_stable_id = stable_core_node_id(
        layer=node.layer,
        kind=node.kind,
        primary_text_or_label=primary_text,
        source_text_hash=source_text_hash,
        spans=_node_spans(node),
    )
    tie_break_payload = _canonical_json(
        node.model_dump(mode="json", by_alias=True, exclude_none=True)
    )
    return _CandidateNode(
        node=node,
        duplicate_key=duplicate_key,
        canonical_stable_id=canonical_stable_id,
        tie_break_payload=tie_break_payload,
    )


def _merge_o_group(group: list[_CandidateNode], retained_id: str) -> CoreONode:
    labels = sorted(
        {
            _normalize_whitespace(item.node.label)
            for item in group
            if isinstance(item.node, CoreONode)
        },
        key=_display_text_sort_key,
    )
    if not labels:
        raise ValueError("cannot merge empty O-node group")
    label = labels[0]

    aliases: set[str] = set()
    for item in group:
        if not isinstance(item.node, CoreONode):
            continue
        aliases.update(
            _normalize_whitespace(alias)
            for alias in item.node.aliases
            if _normalize_whitespace(alias)
        )
        normalized_label = _normalize_whitespace(item.node.label)
        if normalized_label and normalized_label != label:
            aliases.add(normalized_label)

    aliases.discard(label)
    return CoreONode(id=retained_id, kind=group[0].node.kind, label=label, aliases=sorted(aliases))


def _merge_e_group(group: list[_CandidateNode], retained_id: str) -> CoreENode:
    representatives = sorted(
        group, key=lambda item: (item.canonical_stable_id, item.tie_break_payload)
    )
    representative = representatives[0].node
    if not isinstance(representative, CoreENode):
        raise ValueError("cannot merge non-E node in E group")

    texts = sorted(
        {
            _normalize_whitespace(item.node.text)
            for item in representatives
            if isinstance(item.node, CoreENode)
        },
        key=_display_text_sort_key,
    )
    text = texts[0] if texts else _normalize_whitespace(representative.text)

    merged_spans: list[SourceSpan] = []
    for item in representatives:
        if isinstance(item.node, CoreENode):
            merged_spans.extend(item.node.spans)
    canonical_spans = _canonical_spans(merged_spans)

    return CoreENode(
        id=retained_id,
        kind=representative.kind,
        text=text,
        spans=canonical_spans,
        confidence=representative.confidence,
        ledger_version=representative.ledger_version,
        S_milli=representative.s_milli,
        B_milli=representative.b_milli,
        R_milli=representative.r_milli,
        S=representative.s,
        B=representative.b,
        R=representative.r,
    )


def _merge_d_group(group: list[_CandidateNode], retained_id: str) -> CoreDNode:
    representatives = sorted(
        group, key=lambda item: (item.canonical_stable_id, item.tie_break_payload)
    )
    representative = representatives[0].node
    if not isinstance(representative, CoreDNode):
        raise ValueError("cannot merge non-D node in D group")

    labels = sorted(
        {
            _normalize_whitespace(item.node.label)
            for item in representatives
            if isinstance(item.node, CoreDNode)
        },
        key=_display_text_sort_key,
    )
    label = labels[0] if labels else _normalize_whitespace(representative.label)

    return CoreDNode(
        id=retained_id,
        kind=representative.kind,
        label=label,
        constraint_kind=representative.constraint_kind,
        modality=representative.modality,
        condition=representative.condition,
        target=representative.target,
        priority=representative.priority,
    )


def _merge_u_group(group: list[_CandidateNode], retained_id: str) -> CoreUNode:
    representatives = sorted(
        group, key=lambda item: (item.canonical_stable_id, item.tie_break_payload)
    )
    representative = representatives[0].node
    if not isinstance(representative, CoreUNode):
        raise ValueError("cannot merge non-U node in U group")

    labels = sorted(
        {
            _normalize_whitespace(item.node.label)
            for item in representatives
            if isinstance(item.node, CoreUNode)
        },
        key=_display_text_sort_key,
    )
    label = labels[0] if labels else _normalize_whitespace(representative.label)

    return CoreUNode(
        id=retained_id,
        kind=representative.kind,
        label=label,
        weight=representative.weight,
    )


def canonicalize_core_ir_candidates(
    *,
    source_text_hash: str,
    candidates: dict[str, Any],
    source_text: str | None = None,
) -> AdeuCoreIR:
    raw_nodes = candidates.get("nodes", [])
    raw_edges = candidates.get("edges", [])
    if not isinstance(raw_nodes, list):
        raise ValueError("candidate nodes must be a list")
    if not isinstance(raw_edges, list):
        raise ValueError("candidate edges must be a list")

    candidate_nodes: list[_CandidateNode] = []
    node_id_seen: set[str] = set()
    for raw_node in raw_nodes:
        if not isinstance(raw_node, dict):
            raise ValueError("candidate nodes must be object items")
        candidate = _candidate_node(raw_node, source_text_hash=source_text_hash)
        if candidate.node.id in node_id_seen:
            raise ValueError(f"duplicate candidate node id: {candidate.node.id}")
        node_id_seen.add(candidate.node.id)
        candidate_nodes.append(candidate)

    grouped: dict[tuple[str, str, str, str], list[_CandidateNode]] = {}
    for candidate in candidate_nodes:
        grouped.setdefault(candidate.duplicate_key, []).append(candidate)

    id_remap: dict[str, str] = {}
    canonical_nodes: list[CoreNode] = []
    for key in sorted(grouped.keys()):
        group = grouped[key]
        representatives = sorted(
            group, key=lambda item: (item.canonical_stable_id, item.tie_break_payload)
        )
        first = representatives[0]

        merged_spans: list[SourceSpan] = []
        for item in representatives:
            merged_spans.extend(_node_spans(item.node))
        canonical_spans = _canonical_spans(merged_spans)
        recomputed_stable_id = stable_core_node_id(
            layer=first.node.layer,
            kind=first.node.kind,
            primary_text_or_label=_node_primary_text(first.node),
            source_text_hash=source_text_hash,
            spans=canonical_spans,
        )
        retained_id = min(
            [recomputed_stable_id, *(item.canonical_stable_id for item in representatives)]
        )
        for item in representatives:
            id_remap[item.node.id] = retained_id

        if isinstance(first.node, CoreONode):
            canonical_node = _merge_o_group(representatives, retained_id)
        elif isinstance(first.node, CoreENode):
            canonical_node = _merge_e_group(representatives, retained_id)
        elif isinstance(first.node, CoreDNode):
            canonical_node = _merge_d_group(representatives, retained_id)
        elif isinstance(first.node, CoreUNode):
            canonical_node = _merge_u_group(representatives, retained_id)
        else:
            raise ValueError(f"unsupported node type for canonicalization: {type(first.node)!r}")
        canonical_nodes.append(canonical_node)

    canonical_edges: list[CoreEdge] = []
    for raw_edge in raw_edges:
        edge = CoreEdge.model_validate(raw_edge)
        from_ref = id_remap.get(edge.from_ref)
        to_ref = id_remap.get(edge.to_ref)
        if from_ref is None or to_ref is None:
            raise ValueError(
                "unresolved candidate edge reference: "
                f"type={edge.type} from={edge.from_ref} to={edge.to_ref}"
            )
        canonical_edges.append(
            CoreEdge.model_validate({"type": edge.type, "from": from_ref, "to": to_ref})
        )

    deduped_edges: list[CoreEdge] = []
    for identity in sorted({edge.identity for edge in canonical_edges}):
        deduped_edges.append(
            CoreEdge.model_validate({"type": identity[0], "from": identity[1], "to": identity[2]})
        )

    payload: dict[str, Any] = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": source_text_hash,
        "nodes": [
            node.model_dump(mode="json", by_alias=True, exclude_none=True)
            for node in sorted(canonical_nodes, key=canonical_node_sort_key)
        ],
        "edges": [
            edge.model_dump(mode="json", by_alias=True, exclude_none=True)
            for edge in sorted(deduped_edges, key=canonical_edge_sort_key)
        ],
    }
    if source_text is not None:
        payload["source_text"] = source_text

    canonical_payload = canonicalize_core_ir_payload(payload)
    return AdeuCoreIR.model_validate(canonical_payload)


def build_core_ir_from_source_text(
    source_text: str,
    *,
    candidates: dict[str, Any] | None = None,
    include_source_text: bool = True,
    candidate_span_space: str = "raw",
) -> AdeuCoreIR:
    normalized = normalize_core_source_text(source_text)
    if candidate_span_space not in {"raw", "normalized"}:
        raise ValueError("candidate_span_space must be 'raw' or 'normalized'")
    if candidates is None:
        harvested = harvest_core_ir_candidates(normalized)
    else:
        harvested = deepcopy(candidates)
        if candidate_span_space == "raw":
            raw_nodes = harvested.get("nodes", [])
            if not isinstance(raw_nodes, list):
                raise ValueError("candidate nodes must be a list")
            for node in raw_nodes:
                if not isinstance(node, dict):
                    raise ValueError("candidate nodes must be object items")
                if node.get("layer") != "E":
                    continue
                spans = node.get("spans")
                if spans is None:
                    continue
                if not isinstance(spans, list):
                    raise ValueError("E-node spans must be a list")
                remapped_spans = [
                    normalized.to_normalized_span(span).model_dump(mode="json") for span in spans
                ]
                node["spans"] = remapped_spans
    return canonicalize_core_ir_candidates(
        source_text_hash=normalized.source_text_hash,
        source_text=normalized.normalized_text if include_source_text else None,
        candidates=harvested,
    )
