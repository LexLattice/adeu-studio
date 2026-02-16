from __future__ import annotations

import hashlib
import json
import re
from collections import defaultdict
from collections.abc import Mapping, Sequence
from typing import Any, Literal

from adeu_concepts import ConceptIR
from adeu_ir import Ref
from pydantic import TypeAdapter

SEMANTIC_DEPTH_SCHEMA = "semantic_depth_report@1"
SIGNATURE_PROJECTION_VERSION = "semantic_depth.signature.v1"
RANKING_OBJECTIVE_VERSION = "semantic_depth.rank.v1"
RANKING_TIE_BREAK_VERSION = "semantic_depth.tie_break.v1"

SEMANTIC_DEPTH_PACKET_INVALID_CODE = "URM_SEMANTIC_DEPTH_PACKET_INVALID"
SEMANTIC_DEPTH_INVALID_REF_CODE = "URM_SEMANTIC_DEPTH_INVALID_REF"
SEMANTIC_DEPTH_INVALID_CARDINALITY_CODE = "URM_SEMANTIC_DEPTH_INVALID_CARDINALITY"
SEMANTIC_DEPTH_DUPLICATE_CONFLICT_ID_CODE = "URM_SEMANTIC_DEPTH_DUPLICATE_CONFLICT_ID"
SEMANTIC_DEPTH_PERMUTATION_MISMATCH_CODE = "URM_SEMANTIC_DEPTH_PERMUTATION_MISMATCH"
SEMANTIC_DEPTH_IDEMPOTENCY_CONFLICT_CODE = "URM_SEMANTIC_DEPTH_IDEMPOTENCY_CONFLICT"
SEMANTIC_DEPTH_CONFIDENCE_INVALID_CODE = "URM_SEMANTIC_DEPTH_CONFIDENCE_INVALID"

SemanticDepthConflictKind = Literal[
    "claim_text_conflict",
    "link_kind_conflict",
    "reason_code_mismatch",
    "sense_gloss_conflict",
    "status_flip",
]

_CONFLICT_KINDS: tuple[SemanticDepthConflictKind, ...] = (
    "status_flip",
    "reason_code_mismatch",
    "link_kind_conflict",
    "claim_text_conflict",
    "sense_gloss_conflict",
)

CONFLICT_KIND_PRIORITY: dict[str, int] = {
    "status_flip": 900,
    "reason_code_mismatch": 800,
    "link_kind_conflict": 700,
    "claim_text_conflict": 600,
    "sense_gloss_conflict": 500,
}

_CONFLICT_KIND_DEFAULT_CONFIDENCE_MILLI: dict[str, int] = {
    "status_flip": 920,
    "reason_code_mismatch": 850,
    "link_kind_conflict": 820,
    "claim_text_conflict": 780,
    "sense_gloss_conflict": 760,
}

_ARTIFACT_REF_RE = re.compile(r"^artifact:[^\s]+$")
_EVENT_REF_RE = re.compile(r"^event:[^#]+#[0-9]+$")
_EVENT_REF_PARSE_RE = re.compile(r"^event:(?P<stream_id>[^#]+)#(?P<seq>[0-9]+)$")
SEMANTIC_DEPTH_HASH_EXCLUDED_FIELDS = frozenset(
    {
        "semantic_depth_hash",
        "client_request_id",
        "request_id",
        "generated_at",
        "materialized_at",
        "operator_note",
        "nonsemantic_fields",
    }
)
SEMANTIC_DEPTH_HASH_EXCLUDED_FIELD_LIST = tuple(sorted(SEMANTIC_DEPTH_HASH_EXCLUDED_FIELDS))

_REF_ADAPTER = TypeAdapter(Ref)


class SemanticDepthError(ValueError):
    """Raised when semantic-depth packet normalization/validation fails."""

    def __init__(
        self,
        message: str,
        *,
        code: str = SEMANTIC_DEPTH_PACKET_INVALID_CODE,
    ) -> None:
        super().__init__(message)
        self.code = code


def _canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def _canonical_clone(value: Any) -> Any:
    return json.loads(_canonical_json(value))


def _sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _is_valid_ref(ref: str) -> bool:
    return bool(_ARTIFACT_REF_RE.match(ref) or _EVENT_REF_RE.match(ref))


def validate_semantic_depth_ref(ref: str) -> str:
    value = str(ref).strip()
    if not value:
        raise SemanticDepthError("empty semantic-depth ref", code=SEMANTIC_DEPTH_INVALID_REF_CODE)
    if not _is_valid_ref(value):
        raise SemanticDepthError(
            f"invalid semantic-depth ref format: {value!r}",
            code=SEMANTIC_DEPTH_INVALID_REF_CODE,
        )
    return value


def parse_event_ref(ref: str) -> tuple[str, int]:
    value = validate_semantic_depth_ref(ref)
    matched = _EVENT_REF_PARSE_RE.match(value)
    if matched is None:
        raise SemanticDepthError(
            f"invalid event ref format: {value!r}",
            code=SEMANTIC_DEPTH_INVALID_REF_CODE,
        )
    stream_id = matched.group("stream_id")
    seq = int(matched.group("seq"))
    return stream_id, seq


def _normalize_ref_list(refs: Sequence[str], *, field_name: str) -> list[str]:
    normalized = [validate_semantic_depth_ref(ref) for ref in refs]
    canonical = sorted(set(normalized))
    if len(canonical) != len(normalized):
        raise SemanticDepthError(
            f"{field_name} must be unique",
            code=SEMANTIC_DEPTH_INVALID_REF_CODE,
        )
    return canonical


def _normalize_input_refs(refs: Sequence[str]) -> list[str]:
    canonical = _normalize_ref_list(refs, field_name="input_artifact_refs")
    if len(canonical) != 2:
        raise SemanticDepthError(
            "input_artifact_refs must contain exactly two refs",
            code=SEMANTIC_DEPTH_INVALID_CARDINALITY_CODE,
        )
    return canonical


def _normalize_typed_ref(value: Any) -> dict[str, Any]:
    payload = _canonical_clone(value)
    parsed = _REF_ADAPTER.validate_python(payload)
    dumped = _REF_ADAPTER.dump_python(parsed, mode="json")
    return _canonical_clone(dumped)


def _validate_conflict_kind(kind: str) -> SemanticDepthConflictKind:
    if kind not in _CONFLICT_KINDS:
        raise SemanticDepthError(f"unsupported conflict kind: {kind!r}")
    return kind  # type: ignore[return-value]


def _normalize_conflict_key(conflict_key: Mapping[str, Any]) -> dict[str, Any]:
    kind = _validate_conflict_kind(str(conflict_key.get("kind") or ""))
    if "subject_ref" not in conflict_key or "object_ref" not in conflict_key:
        raise SemanticDepthError("conflict_key requires subject_ref/object_ref")

    normalized: dict[str, Any] = {
        "kind": kind,
        "subject_ref": _normalize_typed_ref(conflict_key["subject_ref"]),
        "object_ref": _normalize_typed_ref(conflict_key["object_ref"]),
    }
    if conflict_key.get("predicate_ref") is not None:
        normalized["predicate_ref"] = _normalize_typed_ref(conflict_key["predicate_ref"])
    if conflict_key.get("locus_ref") is not None:
        normalized["locus_ref"] = _normalize_typed_ref(conflict_key["locus_ref"])
    return normalized


def conflict_id_from_key(conflict_key: Mapping[str, Any]) -> str:
    normalized = _normalize_conflict_key(conflict_key)
    return _sha256_text(_canonical_json(normalized))


def _normalize_source_ref_ids(value: Any) -> list[str]:
    if value is None:
        return []
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise SemanticDepthError("source_ref_ids must be an array of refs")
    return _normalize_ref_list([str(item) for item in value], field_name="source_ref_ids")


def _normalize_priority(*, value: Any, kind: str) -> int:
    expected = CONFLICT_KIND_PRIORITY[kind]
    if value is None:
        return expected
    try:
        parsed = int(value)
    except (TypeError, ValueError) as exc:
        raise SemanticDepthError("priority must be an integer") from exc
    if parsed != expected:
        raise SemanticDepthError("priority must match frozen kind->priority mapping")
    return parsed


def _confidence_milli_from_ratio(*, num: Any, denom: Any) -> int:
    try:
        parsed_num = int(num)
        parsed_denom = int(denom)
    except (TypeError, ValueError) as exc:
        raise SemanticDepthError(
            "confidence_ratio_num and confidence_ratio_denom must be integers",
            code=SEMANTIC_DEPTH_CONFIDENCE_INVALID_CODE,
        ) from exc
    if parsed_denom <= 0:
        raise SemanticDepthError(
            "confidence_ratio_denom must be > 0",
            code=SEMANTIC_DEPTH_CONFIDENCE_INVALID_CODE,
        )
    confidence_milli = (parsed_num * 1000 + parsed_denom // 2) // parsed_denom
    if confidence_milli < 0 or confidence_milli > 1000:
        raise SemanticDepthError(
            "derived confidence_milli must be in [0, 1000]",
            code=SEMANTIC_DEPTH_CONFIDENCE_INVALID_CODE,
        )
    return confidence_milli


def _normalize_confidence_milli(*, value: Any, kind: str, provenance_raw: Mapping[str, Any]) -> int:
    has_ratio = (
        "confidence_ratio_num" in provenance_raw
        or "confidence_ratio_denom" in provenance_raw
    )
    if has_ratio:
        if value is not None:
            raise SemanticDepthError(
                (
                    "confidence_milli is mutually exclusive with "
                    "confidence_ratio_num/confidence_ratio_denom"
                ),
                code=SEMANTIC_DEPTH_CONFIDENCE_INVALID_CODE,
            )
        if (
            "confidence_ratio_num" not in provenance_raw
            or "confidence_ratio_denom" not in provenance_raw
        ):
            raise SemanticDepthError(
                (
                    "confidence_ratio_num and confidence_ratio_denom are both required "
                    "when ratio confidence is used"
                ),
                code=SEMANTIC_DEPTH_CONFIDENCE_INVALID_CODE,
            )
        return _confidence_milli_from_ratio(
            num=provenance_raw.get("confidence_ratio_num"),
            denom=provenance_raw.get("confidence_ratio_denom"),
        )

    if value is None:
        return _CONFLICT_KIND_DEFAULT_CONFIDENCE_MILLI.get(kind, 500)
    try:
        parsed = int(value)
    except (TypeError, ValueError) as exc:
        raise SemanticDepthError(
            "confidence_milli must be an integer",
            code=SEMANTIC_DEPTH_CONFIDENCE_INVALID_CODE,
        ) from exc
    if parsed < 0 or parsed > 1000:
        raise SemanticDepthError(
            "confidence_milli must be in [0, 1000]",
            code=SEMANTIC_DEPTH_CONFIDENCE_INVALID_CODE,
        )
    return parsed


def _normalize_conflict_item(raw_item: Mapping[str, Any]) -> dict[str, Any]:
    payload = _canonical_clone(raw_item)
    conflict_key_raw = payload.get("conflict_key")
    if not isinstance(conflict_key_raw, Mapping):
        raise SemanticDepthError("conflict item requires conflict_key object")
    conflict_key = _normalize_conflict_key(conflict_key_raw)
    conflict_id = conflict_id_from_key(conflict_key)
    provided_id = payload.get("conflict_id")
    if provided_id is not None and str(provided_id) != conflict_id:
        raise SemanticDepthError("conflict_id does not match canonical conflict_key")

    kind = conflict_key["kind"]
    provenance_raw = payload.get("provenance")
    if provenance_raw is None:
        provenance_raw = {}
    if not isinstance(provenance_raw, Mapping):
        raise SemanticDepthError("conflict provenance must be an object")

    priority = _normalize_priority(value=provenance_raw.get("priority"), kind=str(kind))
    confidence_milli = _normalize_confidence_milli(
        value=provenance_raw.get("confidence_milli"),
        kind=str(kind),
        provenance_raw=provenance_raw,
    )
    evidence_kind = str(provenance_raw.get("evidence_kind") or kind)
    source_ref_ids = _normalize_source_ref_ids(provenance_raw.get("source_ref_ids"))

    provenance: dict[str, Any] = {
        "priority": priority,
        "confidence_milli": confidence_milli,
        "evidence_kind": evidence_kind,
        "source_ref_ids": source_ref_ids,
    }
    solver_status = provenance_raw.get("solver_status")
    if solver_status is not None:
        provenance["solver_status"] = str(solver_status)

    normalized: dict[str, Any] = {
        "conflict_id": conflict_id,
        "conflict_key": conflict_key,
        "provenance": provenance,
    }
    for key in sorted(payload.keys()):
        if key in {"conflict_id", "conflict_key", "provenance"}:
            continue
        normalized[key] = _canonical_clone(payload[key])
    return normalized


def _normalize_conflict_items(conflict_items: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    normalized = [_normalize_conflict_item(item) for item in conflict_items]
    seen: set[str] = set()
    for item in normalized:
        conflict_id = str(item["conflict_id"])
        if conflict_id in seen:
            raise SemanticDepthError(
                f"duplicate conflict_id in report: {conflict_id}",
                code=SEMANTIC_DEPTH_DUPLICATE_CONFLICT_ID_CODE,
            )
        seen.add(conflict_id)
    normalized.sort(key=lambda item: str(item["conflict_id"]))
    return normalized


def _derive_ranked_conflict_ids(conflicts: Sequence[Mapping[str, Any]]) -> list[str]:
    ranked = sorted(
        (str(item["conflict_id"]) for item in conflicts),
        key=lambda conflict_id: _ranking_sort_tuple(conflict_id=conflict_id, conflicts=conflicts),
    )
    return ranked


def _ranking_sort_tuple(
    *,
    conflict_id: str,
    conflicts: Sequence[Mapping[str, Any]],
) -> tuple[int, int, str]:
    for item in conflicts:
        if str(item["conflict_id"]) != conflict_id:
            continue
        provenance = item.get("provenance", {})
        priority = int((provenance or {}).get("priority", 0))
        confidence_milli = int((provenance or {}).get("confidence_milli", 0))
        return (-priority, -confidence_milli, conflict_id)
    return (0, 0, conflict_id)


def _normalize_ranked_conflict_ids(
    ranked_conflict_ids: Sequence[str] | None,
    *,
    conflicts: Sequence[Mapping[str, Any]],
) -> list[str]:
    known_ids = [str(item["conflict_id"]) for item in conflicts]
    known_set = set(known_ids)
    if ranked_conflict_ids is None:
        return _derive_ranked_conflict_ids(conflicts)
    if not isinstance(ranked_conflict_ids, Sequence) or isinstance(
        ranked_conflict_ids,
        (str, bytes, bytearray),
    ):
        raise SemanticDepthError("ranked_conflict_ids must be an array")
    ranked = [str(item) for item in ranked_conflict_ids]
    if len(set(ranked)) != len(ranked):
        raise SemanticDepthError("ranked_conflict_ids must be unique")
    if set(ranked) != known_set:
        raise SemanticDepthError("ranked_conflict_ids must match conflict_items conflict_id set")
    expected = _derive_ranked_conflict_ids(conflicts)
    if ranked != expected:
        raise SemanticDepthError(
            "ranked_conflict_ids must match deterministic objective/tie-break ordering",
        )
    return expected


def strip_nonsemantic_semantic_depth_fields(value: Any) -> Any:
    if isinstance(value, Mapping):
        normalized: dict[str, Any] = {}
        for raw_key, raw_value in sorted(value.items(), key=lambda item: str(item[0])):
            key = str(raw_key)
            if key in SEMANTIC_DEPTH_HASH_EXCLUDED_FIELDS:
                continue
            if key.endswith("_raw"):
                continue
            normalized[key] = strip_nonsemantic_semantic_depth_fields(raw_value)
        return normalized
    if isinstance(value, list):
        return [strip_nonsemantic_semantic_depth_fields(item) for item in value]
    return value


def semantic_depth_hash(payload: Mapping[str, Any]) -> str:
    normalized = strip_nonsemantic_semantic_depth_fields(payload)
    return _sha256_text(_canonical_json(normalized))


def _coherence_summary_hash(summary: Mapping[str, Any]) -> str:
    normalized = strip_nonsemantic_semantic_depth_fields(summary)
    return _sha256_text(_canonical_json(normalized))


def _require_frozen_version(*, value: str, expected: str, field_name: str) -> None:
    if value != expected:
        raise SemanticDepthError(f"{field_name} must be {expected}")


def build_semantic_depth_report(
    *,
    input_artifact_refs: Sequence[str],
    conflict_items: Sequence[Mapping[str, Any]],
    ranked_conflict_ids: Sequence[str] | None = None,
    signature_projection_version: str = SIGNATURE_PROJECTION_VERSION,
    ranking_objective_version: str = RANKING_OBJECTIVE_VERSION,
    ranking_tie_break_version: str = RANKING_TIE_BREAK_VERSION,
    diff_refs: Sequence[str] = (),
    witness_refs: Sequence[str] = (),
    semantics_diagnostics_ref: str | None = None,
    explain_diff_ref: str | None = None,
    coherence_summary: Mapping[str, Any] | None = None,
    nonsemantic_fields: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    _require_frozen_version(
        value=signature_projection_version,
        expected=SIGNATURE_PROJECTION_VERSION,
        field_name="signature_projection_version",
    )
    _require_frozen_version(
        value=ranking_objective_version,
        expected=RANKING_OBJECTIVE_VERSION,
        field_name="ranking_objective_version",
    )
    _require_frozen_version(
        value=ranking_tie_break_version,
        expected=RANKING_TIE_BREAK_VERSION,
        field_name="ranking_tie_break_version",
    )

    normalized_input_refs = _normalize_input_refs(input_artifact_refs)
    normalized_conflicts = _normalize_conflict_items(conflict_items)
    normalized_ranked_ids = _normalize_ranked_conflict_ids(
        ranked_conflict_ids,
        conflicts=normalized_conflicts,
    )

    packet: dict[str, Any] = {
        "schema": SEMANTIC_DEPTH_SCHEMA,
        "input_artifact_refs": normalized_input_refs,
        "signature_projection_version": signature_projection_version,
        "ranking_objective_version": ranking_objective_version,
        "ranking_tie_break_version": ranking_tie_break_version,
        "conflict_items": normalized_conflicts,
        "ranked_conflict_ids": normalized_ranked_ids,
        "hash_excluded_fields": list(SEMANTIC_DEPTH_HASH_EXCLUDED_FIELD_LIST),
    }

    if diff_refs:
        packet["diff_refs"] = _normalize_ref_list(diff_refs, field_name="diff_refs")
    if witness_refs:
        packet["witness_refs"] = _normalize_ref_list(witness_refs, field_name="witness_refs")
    if semantics_diagnostics_ref is not None:
        packet["semantics_diagnostics_ref"] = validate_semantic_depth_ref(semantics_diagnostics_ref)
    if explain_diff_ref is not None:
        packet["explain_diff_ref"] = validate_semantic_depth_ref(explain_diff_ref)
    if coherence_summary is not None:
        coherence_payload = _canonical_clone(dict(coherence_summary))
        packet["coherence_summary"] = coherence_payload
        packet["coherence_summary_hash"] = _coherence_summary_hash(coherence_payload)
    if nonsemantic_fields:
        packet["nonsemantic_fields"] = _canonical_clone(dict(nonsemantic_fields))

    packet["semantic_depth_hash"] = semantic_depth_hash(packet)
    return packet


def validate_semantic_depth_report(payload: Mapping[str, Any]) -> None:
    if payload.get("schema") != SEMANTIC_DEPTH_SCHEMA:
        raise SemanticDepthError("payload schema must be semantic_depth_report@1")

    hash_excluded_fields = payload.get("hash_excluded_fields")
    if hash_excluded_fields != list(SEMANTIC_DEPTH_HASH_EXCLUDED_FIELD_LIST):
        raise SemanticDepthError("hash_excluded_fields does not match frozen exclusion set")

    input_refs_raw = payload.get("input_artifact_refs")
    if not isinstance(input_refs_raw, Sequence) or isinstance(
        input_refs_raw,
        (str, bytes, bytearray),
    ):
        raise SemanticDepthError("input_artifact_refs must be an array")
    normalized_input_refs = _normalize_input_refs([str(item) for item in input_refs_raw])
    if list(input_refs_raw) != normalized_input_refs:
        raise SemanticDepthError("input_artifact_refs must be canonical-sorted and unique")

    signature_projection_version = str(payload.get("signature_projection_version") or "")
    ranking_objective_version = str(payload.get("ranking_objective_version") or "")
    ranking_tie_break_version = str(payload.get("ranking_tie_break_version") or "")
    _require_frozen_version(
        value=signature_projection_version,
        expected=SIGNATURE_PROJECTION_VERSION,
        field_name="signature_projection_version",
    )
    _require_frozen_version(
        value=ranking_objective_version,
        expected=RANKING_OBJECTIVE_VERSION,
        field_name="ranking_objective_version",
    )
    _require_frozen_version(
        value=ranking_tie_break_version,
        expected=RANKING_TIE_BREAK_VERSION,
        field_name="ranking_tie_break_version",
    )

    conflict_items_raw = payload.get("conflict_items")
    if not isinstance(conflict_items_raw, Sequence) or isinstance(
        conflict_items_raw,
        (str, bytes, bytearray),
    ):
        raise SemanticDepthError("conflict_items must be an array")
    normalized_conflicts = _normalize_conflict_items(
        [
            item if isinstance(item, Mapping) else {}
            for item in conflict_items_raw
        ]
    )
    if list(conflict_items_raw) != normalized_conflicts:
        raise SemanticDepthError("conflict_items must be canonical-sorted by conflict_id")

    ranked_raw = payload.get("ranked_conflict_ids")
    if not isinstance(ranked_raw, Sequence) or isinstance(ranked_raw, (str, bytes, bytearray)):
        raise SemanticDepthError("ranked_conflict_ids must be an array")
    _normalize_ranked_conflict_ids(
        [str(item) for item in ranked_raw],
        conflicts=normalized_conflicts,
    )

    for key in ("diff_refs", "witness_refs"):
        value = payload.get(key)
        if value is None:
            continue
        if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
            raise SemanticDepthError(f"{key} must be an array of refs")
        normalized_refs = _normalize_ref_list([str(item) for item in value], field_name=key)
        if list(value) != normalized_refs:
            raise SemanticDepthError(f"{key} must be canonical-sorted and unique")

    for key in ("semantics_diagnostics_ref", "explain_diff_ref"):
        value = payload.get(key)
        if value is None:
            continue
        validate_semantic_depth_ref(str(value))

    coherence_summary = payload.get("coherence_summary")
    coherence_summary_hash = payload.get("coherence_summary_hash")
    if coherence_summary is None and coherence_summary_hash is not None:
        raise SemanticDepthError("coherence_summary_hash requires coherence_summary")
    if coherence_summary is not None:
        if not isinstance(coherence_summary, Mapping):
            raise SemanticDepthError("coherence_summary must be an object")
        expected_summary_hash = _coherence_summary_hash(coherence_summary)
        if (
            not isinstance(coherence_summary_hash, str)
            or coherence_summary_hash != expected_summary_hash
        ):
            raise SemanticDepthError("coherence_summary_hash mismatch")

    expected_hash = semantic_depth_hash(payload)
    actual_hash = payload.get("semantic_depth_hash")
    if not isinstance(actual_hash, str) or actual_hash != expected_hash:
        raise SemanticDepthError("semantic_depth_hash mismatch")


def semantic_depth_idempotency_semantic_key(payload: Mapping[str, Any]) -> dict[str, str]:
    required_fields = (
        "schema",
        "signature_projection_version",
        "ranking_objective_version",
        "ranking_tie_break_version",
        "semantic_depth_hash",
    )
    key: dict[str, str] = {}
    for field_name in required_fields:
        raw = payload.get(field_name)
        if not isinstance(raw, str) or not raw:
            raise SemanticDepthError(
                f"semantic-depth packet missing required semantic key field: {field_name}"
            )
        key[field_name] = raw
    return key


def _inline_source_ref(payload: Mapping[str, Any]) -> str:
    return f"artifact:inline_sha256:{_sha256_text(_canonical_json(dict(payload)))}"


def _claims_by_sense(ir: ConceptIR) -> dict[str, tuple[str, ...]]:
    grouped: dict[str, set[str]] = defaultdict(set)
    for claim in ir.claims:
        grouped[claim.sense_id].add(claim.text.strip())
    return {sense_id: tuple(sorted(texts)) for sense_id, texts in grouped.items()}


def _sense_gloss_by_id(ir: ConceptIR) -> dict[str, str]:
    return {sense.id: sense.gloss.strip() for sense in ir.senses}


def _link_kind_by_edge(ir: ConceptIR) -> dict[tuple[str, str], tuple[str, ...]]:
    grouped: dict[tuple[str, str], set[str]] = defaultdict(set)
    for link in ir.links:
        grouped[(link.src_sense_id, link.dst_sense_id)].add(link.kind)
    return {edge: tuple(sorted(kinds)) for edge, kinds in grouped.items()}


def _make_conflict_item(
    *,
    kind: SemanticDepthConflictKind,
    subject_ref: Mapping[str, Any],
    object_ref: Mapping[str, Any],
    source_ref_ids: Sequence[str],
    locus_text: str,
    predicate_text: str | None = None,
    details: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    conflict_key: dict[str, Any] = {
        "kind": kind,
        "subject_ref": _canonical_clone(subject_ref),
        "object_ref": _canonical_clone(object_ref),
        "locus_ref": {"ref_type": "text", "text": locus_text},
    }
    if predicate_text is not None:
        conflict_key["predicate_ref"] = {"ref_type": "text", "text": predicate_text}
    payload: dict[str, Any] = {
        "conflict_key": conflict_key,
        "provenance": {
            "priority": CONFLICT_KIND_PRIORITY[kind],
            "confidence_milli": _CONFLICT_KIND_DEFAULT_CONFIDENCE_MILLI[kind],
            "evidence_kind": kind,
            "source_ref_ids": list(source_ref_ids),
        },
    }
    if details is not None:
        payload["details"] = _canonical_clone(details)
    return payload


def _pairwise_conflicts_for_concept_ir(
    *,
    first_ir: ConceptIR,
    second_ir: ConceptIR,
    source_ref_ids: Sequence[str],
) -> list[dict[str, Any]]:
    subject_ref = {"ref_type": "doc", "doc_ref": first_ir.context.doc_id}
    object_ref = {"ref_type": "doc", "doc_ref": second_ir.context.doc_id}
    conflicts: list[dict[str, Any]] = []

    left_gloss = _sense_gloss_by_id(first_ir)
    right_gloss = _sense_gloss_by_id(second_ir)
    for sense_id in sorted(set(left_gloss).intersection(right_gloss)):
        if left_gloss[sense_id] == right_gloss[sense_id]:
            continue
        conflicts.append(
            _make_conflict_item(
                kind="sense_gloss_conflict",
                subject_ref=subject_ref,
                object_ref=object_ref,
                source_ref_ids=source_ref_ids,
                locus_text=f"sense:{sense_id}",
                predicate_text="gloss_mismatch",
                details={
                    "sense_id": sense_id,
                    "left_gloss": left_gloss[sense_id],
                    "right_gloss": right_gloss[sense_id],
                },
            )
        )

    left_claims = _claims_by_sense(first_ir)
    right_claims = _claims_by_sense(second_ir)
    for sense_id in sorted(set(left_claims).intersection(right_claims)):
        if left_claims[sense_id] == right_claims[sense_id]:
            continue
        conflicts.append(
            _make_conflict_item(
                kind="claim_text_conflict",
                subject_ref=subject_ref,
                object_ref=object_ref,
                source_ref_ids=source_ref_ids,
                locus_text=f"claim:{sense_id}",
                predicate_text="claim_set_mismatch",
                details={
                    "sense_id": sense_id,
                    "left_claim_texts": list(left_claims[sense_id]),
                    "right_claim_texts": list(right_claims[sense_id]),
                },
            )
        )

    left_links = _link_kind_by_edge(first_ir)
    right_links = _link_kind_by_edge(second_ir)
    for edge in sorted(set(left_links).union(right_links)):
        left_kinds = left_links.get(edge, ())
        right_kinds = right_links.get(edge, ())
        if left_kinds == right_kinds:
            continue
        src_sense_id, dst_sense_id = edge
        conflicts.append(
            _make_conflict_item(
                kind="link_kind_conflict",
                subject_ref=subject_ref,
                object_ref=object_ref,
                source_ref_ids=source_ref_ids,
                locus_text=f"link:{src_sense_id}->{dst_sense_id}",
                predicate_text="link_kind_set_mismatch",
                details={
                    "src_sense_id": src_sense_id,
                    "dst_sense_id": dst_sense_id,
                    "left_link_kinds": list(left_kinds),
                    "right_link_kinds": list(right_kinds),
                },
            )
        )

    return conflicts


def build_semantic_depth_report_from_concept_pair(
    *,
    left_ir: ConceptIR,
    right_ir: ConceptIR,
    input_artifact_refs: Sequence[str] | None = None,
    diff_refs: Sequence[str] = (),
    witness_refs: Sequence[str] = (),
    semantics_diagnostics_ref: str | None = None,
    explain_diff_ref: str | None = None,
    coherence_summary: Mapping[str, Any] | None = None,
    nonsemantic_fields: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    if input_artifact_refs is not None:
        if len(input_artifact_refs) != 2:
            raise SemanticDepthError(
                "input_artifact_refs must contain exactly two refs",
                code=SEMANTIC_DEPTH_INVALID_CARDINALITY_CODE,
            )
        left_ref = validate_semantic_depth_ref(str(input_artifact_refs[0]))
        right_ref = validate_semantic_depth_ref(str(input_artifact_refs[1]))
    else:
        left_ref = _inline_source_ref(
            {
                "domain": "concepts",
                "side": "left",
                "concept_ir": left_ir.model_dump(mode="json", exclude_none=True),
            }
        )
        right_ref = _inline_source_ref(
            {
                "domain": "concepts",
                "side": "right",
                "concept_ir": right_ir.model_dump(mode="json", exclude_none=True),
            }
        )

    if left_ref <= right_ref:
        first_ir = left_ir
        second_ir = right_ir
    else:
        first_ir = right_ir
        second_ir = left_ir

    normalized_input_refs = _normalize_input_refs([left_ref, right_ref])
    conflicts = _pairwise_conflicts_for_concept_ir(
        first_ir=first_ir,
        second_ir=second_ir,
        source_ref_ids=normalized_input_refs,
    )
    return build_semantic_depth_report(
        input_artifact_refs=normalized_input_refs,
        conflict_items=conflicts,
        diff_refs=diff_refs,
        witness_refs=witness_refs,
        semantics_diagnostics_ref=semantics_diagnostics_ref,
        explain_diff_ref=explain_diff_ref,
        coherence_summary=coherence_summary,
        nonsemantic_fields=nonsemantic_fields,
    )
