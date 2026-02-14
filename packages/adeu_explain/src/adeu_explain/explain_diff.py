from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Mapping, Sequence
from typing import Any, Literal

from .models import ConceptAnalysisDelta, DiffReport, FlipExplanation

EXPLAIN_DIFF_SCHEMA = "explain_diff@1"
EXPLAIN_BUILDER_VERSION = "odeu.explain-builder.v1"
EXPLAIN_PACKET_INVALID_CODE = "URM_EXPLAIN_PACKET_INVALID"
EXPLAIN_INVALID_REF_CODE = "URM_EXPLAIN_INVALID_REF"

ExplainKind = Literal[
    "semantic_diff",
    "concepts_diff",
    "puzzles_diff",
    "flip_explain",
]

_EXPLAIN_KINDS: tuple[ExplainKind, ...] = (
    "semantic_diff",
    "concepts_diff",
    "puzzles_diff",
    "flip_explain",
)

_ARTIFACT_REF_RE = re.compile(r"^artifact:[^\s]+$")
_EVENT_REF_RE = re.compile(r"^event:[^#]+#[0-9]+$")

# Nonsemantic fields are intentionally excluded from explain_hash.
EXPLAIN_HASH_EXCLUDED_FIELDS = frozenset(
    {
        "explain_hash",
        "client_request_id",
        "request_id",
        "materialized_at",
        "generated_at",
        "operator_note",
        "nonsemantic_fields",
        "run_ir_mismatch",
        "left_mismatch",
        "right_mismatch",
    }
)

EXPLAIN_HASH_EXCLUDED_FIELD_LIST = tuple(sorted(EXPLAIN_HASH_EXCLUDED_FIELDS))


class ExplainDiffError(ValueError):
    """Raised when explain packet normalization/validation fails."""

    def __init__(self, message: str, *, code: str = EXPLAIN_PACKET_INVALID_CODE) -> None:
        super().__init__(message)
        self.code = code


def _canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def _sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _canonical_clone(value: Any) -> Any:
    return json.loads(_canonical_json(value))


def _validate_explain_kind(explain_kind: str) -> ExplainKind:
    if explain_kind not in _EXPLAIN_KINDS:
        raise ExplainDiffError(f"unsupported explain_kind: {explain_kind!r}")
    return explain_kind  # type: ignore[return-value]


def _is_valid_ref(ref: str) -> bool:
    return bool(_ARTIFACT_REF_RE.match(ref) or _EVENT_REF_RE.match(ref))


def validate_explain_ref(ref: str) -> str:
    value = str(ref).strip()
    if not value:
        raise ExplainDiffError("empty explain ref", code=EXPLAIN_INVALID_REF_CODE)
    if not _is_valid_ref(value):
        raise ExplainDiffError(
            f"invalid explain ref format: {value!r}",
            code=EXPLAIN_INVALID_REF_CODE,
        )
    return value


def normalize_explain_ref_list(refs: Sequence[str]) -> list[str]:
    normalized = [validate_explain_ref(ref) for ref in refs]
    return sorted(set(normalized))


def inline_source_ref(source_payload: Mapping[str, Any]) -> str:
    digest = _sha256_text(_canonical_json(dict(source_payload)))
    return f"artifact:inline_sha256:{digest}"


def _normalize_explanation_items(items: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    normalized_items: list[dict[str, Any]] = []
    for raw in items:
        item = _canonical_clone(raw)
        span = item.get("span")
        if isinstance(span, Mapping):
            item["span"] = {
                key: span[key]
                for key in ("start", "end")
                if key in span
            }
        normalized_items.append(item)
    normalized_items.sort(
        key=lambda item: (
            str(item.get("atom_name") or ""),
            str(item.get("object_id") or ""),
            str(item.get("json_path") or ""),
            str(
                (item.get("span") or {}).get("start")
                if isinstance(item.get("span"), Mapping)
                else ""
            ),
            str(
                (item.get("span") or {}).get("end")
                if isinstance(item.get("span"), Mapping)
                else ""
            ),
        )
    )
    return normalized_items


def _normalize_structural(structural: Mapping[str, Any]) -> dict[str, Any]:
    payload = _canonical_clone(structural)
    json_patches = payload.get("json_patches")
    if isinstance(json_patches, list):
        payload["json_patches"] = sorted(
            (_canonical_clone(item) for item in json_patches),
            key=lambda item: (
                str(item.get("path") or ""),
                str(item.get("op") or ""),
                str(item.get("from") or ""),
                _canonical_json(item.get("value")),
            ),
        )
    for key in ("changed_paths", "changed_object_ids"):
        values = payload.get(key)
        if isinstance(values, list):
            payload[key] = sorted(str(item) for item in values)
    return payload


def _normalize_model_delta(model_delta: Mapping[str, Any]) -> dict[str, Any]:
    payload = _canonical_clone(model_delta)

    added = payload.get("added_assignments")
    if isinstance(added, list):
        payload["added_assignments"] = sorted(
            (_canonical_clone(item) for item in added),
            key=lambda item: (str(item.get("atom") or ""), str(item.get("value") or "")),
        )

    removed = payload.get("removed_assignments")
    if isinstance(removed, list):
        payload["removed_assignments"] = sorted(
            (_canonical_clone(item) for item in removed),
            key=lambda item: (str(item.get("atom") or ""), str(item.get("value") or "")),
        )

    changed = payload.get("changed_assignments")
    if isinstance(changed, list):
        payload["changed_assignments"] = sorted(
            (_canonical_clone(item) for item in changed),
            key=lambda item: (
                str(item.get("atom") or ""),
                str(item.get("left_value") or ""),
                str(item.get("right_value") or ""),
            ),
        )

    changed_atoms = payload.get("changed_atoms")
    if isinstance(changed_atoms, list):
        payload["changed_atoms"] = sorted(str(item) for item in changed_atoms)

    return payload


def _normalize_solver(solver: Mapping[str, Any]) -> dict[str, Any]:
    payload = _canonical_clone(solver)
    for side_key in ("left_runs", "right_runs"):
        runs = payload.get(side_key)
        if isinstance(runs, list):
            payload[side_key] = sorted(
                (_canonical_clone(item) for item in runs),
                key=lambda item: (
                    str(item.get("run_id") or ""),
                    str(item.get("request_hash") or ""),
                    str(item.get("formula_hash") or ""),
                    str(item.get("created_at") or ""),
                ),
            )

    core_delta = payload.get("core_delta")
    if isinstance(core_delta, Mapping):
        core = _canonical_clone(core_delta)
        for key in ("added_atoms", "removed_atoms"):
            values = core.get(key)
            if isinstance(values, list):
                core[key] = sorted(str(item) for item in values)
        payload["core_delta"] = core

    model_delta = payload.get("model_delta")
    if isinstance(model_delta, Mapping):
        payload["model_delta"] = _normalize_model_delta(model_delta)

    for key in ("unpaired_left_hashes", "unpaired_right_hashes"):
        values = payload.get(key)
        if isinstance(values, list):
            payload[key] = sorted(str(item) for item in values)

    return payload


def _normalize_causal_slice(causal_slice: Mapping[str, Any]) -> dict[str, Any]:
    payload = _canonical_clone(causal_slice)
    for key in ("touched_atoms", "touched_object_ids", "touched_json_paths"):
        values = payload.get(key)
        if isinstance(values, list):
            payload[key] = sorted(str(item) for item in values)
    explanation_items = payload.get("explanation_items")
    if isinstance(explanation_items, list):
        payload["explanation_items"] = _normalize_explanation_items(explanation_items)
    return payload


def normalize_diff_report_projection(diff_report: DiffReport | Mapping[str, Any]) -> dict[str, Any]:
    if isinstance(diff_report, DiffReport):
        payload = diff_report.model_dump(mode="json", exclude_none=True)
    else:
        payload = _canonical_clone(diff_report)

    structural = payload.get("structural")
    if isinstance(structural, Mapping):
        payload["structural"] = _normalize_structural(structural)

    solver = payload.get("solver")
    if isinstance(solver, Mapping):
        payload["solver"] = _normalize_solver(solver)

    causal_slice = payload.get("causal_slice")
    if isinstance(causal_slice, Mapping):
        payload["causal_slice"] = _normalize_causal_slice(causal_slice)

    summary = payload.get("summary")
    if isinstance(summary, Mapping):
        normalized_summary = _canonical_clone(summary)
        for key in ("unpaired_left_keys", "unpaired_right_keys"):
            values = normalized_summary.get(key)
            if isinstance(values, list):
                normalized_summary[key] = sorted(str(item) for item in values)
        payload["summary"] = normalized_summary

    return payload


def _normalize_flip_explanation(
    explanation: FlipExplanation | Mapping[str, Any] | None,
) -> dict[str, Any] | None:
    if explanation is None:
        return None
    if isinstance(explanation, FlipExplanation):
        payload = explanation.model_dump(mode="json", exclude_none=True)
    else:
        payload = _canonical_clone(explanation)

    primary_changes = payload.get("primary_changes")
    if isinstance(primary_changes, list):
        normalized_primary = []
        for item in primary_changes:
            normalized = _canonical_clone(item)
            paths = normalized.get("changed_paths")
            if isinstance(paths, list):
                normalized["changed_paths"] = sorted(str(path) for path in paths)
            normalized_primary.append(normalized)
        payload["primary_changes"] = sorted(
            normalized_primary,
            key=lambda item: (
                str(item.get("object_kind") or ""),
                str(item.get("object_id") or ""),
                tuple(item.get("changed_paths") or []),
                int(item.get("patch_count") or 0),
            ),
        )

    evidence_changes = payload.get("evidence_changes")
    if isinstance(evidence_changes, list):
        payload["evidence_changes"] = sorted(
            (_canonical_clone(item) for item in evidence_changes),
            key=lambda item: (
                str(item.get("atom_name") or ""),
                str(item.get("evidence_kind") or ""),
                str(item.get("severity") or ""),
                str(item.get("object_kind") or ""),
                str(item.get("object_id") or ""),
                str(item.get("json_path") or ""),
            ),
        )

    cause_chain = payload.get("cause_chain")
    if isinstance(cause_chain, list):
        payload["cause_chain"] = sorted(
            (_canonical_clone(item) for item in cause_chain),
            key=lambda item: (
                str(item.get("severity") or ""),
                str(item.get("object_kind") or ""),
                str(item.get("object_id") or ""),
                str(item.get("json_path") or ""),
                str(item.get("atom_name") or ""),
                str(item.get("evidence_kind") or ""),
                str(item.get("message") or ""),
            ),
        )

    repair_hints = payload.get("repair_hints")
    if isinstance(repair_hints, list):
        payload["repair_hints"] = sorted(
            (_canonical_clone(item) for item in repair_hints),
            key=lambda item: (
                str(item.get("object_kind") or ""),
                str(item.get("object_id") or ""),
                str(item.get("json_path") or ""),
                str(item.get("hint") or ""),
            ),
        )

    return payload


def _normalize_analysis_delta(
    analysis_delta: ConceptAnalysisDelta | Mapping[str, Any] | None,
) -> dict[str, Any] | None:
    if analysis_delta is None:
        return None
    if isinstance(analysis_delta, ConceptAnalysisDelta):
        payload = analysis_delta.model_dump(mode="json", exclude_none=True)
    else:
        payload = _canonical_clone(analysis_delta)

    for key in (
        "mic_atoms_added",
        "mic_atoms_removed",
    ):
        values = payload.get(key)
        if isinstance(values, list):
            payload[key] = sorted(str(item) for item in values)

    for key in (
        "forced_edges_added",
        "forced_edges_removed",
        "countermodel_edges_changed",
    ):
        values = payload.get(key)
        if isinstance(values, list):
            payload[key] = sorted(
                (_canonical_clone(item) for item in values),
                key=lambda item: (
                    str(item.get("src_sense_id") or ""),
                    str(item.get("dst_sense_id") or ""),
                    str(item.get("kind") or ""),
                ),
            )

    return payload


def strip_nonsemantic_explain_fields(value: Any) -> Any:
    if isinstance(value, Mapping):
        normalized: dict[str, Any] = {}
        for raw_key, raw_value in sorted(value.items(), key=lambda item: str(item[0])):
            key = str(raw_key)
            if key in EXPLAIN_HASH_EXCLUDED_FIELDS:
                continue
            if key.endswith("_raw"):
                continue
            normalized[key] = strip_nonsemantic_explain_fields(raw_value)
        return normalized
    if isinstance(value, list):
        return [strip_nonsemantic_explain_fields(item) for item in value]
    return value


def explain_diff_hash(payload: Mapping[str, Any]) -> str:
    return _sha256_text(_canonical_json(strip_nonsemantic_explain_fields(payload)))


def _required_sections_for_kind(explain_kind: ExplainKind) -> frozenset[str]:
    if explain_kind == "flip_explain":
        return frozenset({"diff_report", "flip_explanation"})
    return frozenset({"diff_report"})


def build_explain_diff_packet(
    *,
    explain_kind: str,
    input_artifact_refs: Sequence[str],
    diff_report: DiffReport | Mapping[str, Any],
    diff_refs: Sequence[str] = (),
    witness_refs: Sequence[str] = (),
    semantics_diagnostics_ref: str | None = None,
    validator_evidence_packet_refs: Sequence[str] | None = None,
    flip_explanation: FlipExplanation | Mapping[str, Any] | None = None,
    analysis_delta: ConceptAnalysisDelta | Mapping[str, Any] | None = None,
    run_ir_mismatch: bool | None = None,
    left_mismatch: bool | None = None,
    right_mismatch: bool | None = None,
    nonsemantic_fields: Mapping[str, Any] | None = None,
    builder_version: str = EXPLAIN_BUILDER_VERSION,
) -> dict[str, Any]:
    kind = _validate_explain_kind(explain_kind)

    sections: dict[str, Any] = {
        "diff_report": normalize_diff_report_projection(diff_report),
    }
    normalized_flip = _normalize_flip_explanation(flip_explanation)
    if normalized_flip is not None:
        sections["flip_explanation"] = normalized_flip

    normalized_delta = _normalize_analysis_delta(analysis_delta)
    if normalized_delta is not None:
        sections["analysis_delta"] = normalized_delta

    required_sections = _required_sections_for_kind(kind)
    if not required_sections.issubset(sections):
        raise ExplainDiffError(
            f"missing required sections for {kind}: "
            f"{sorted(required_sections - set(sections))}"
        )

    packet: dict[str, Any] = {
        "schema": EXPLAIN_DIFF_SCHEMA,
        "explain_kind": kind,
        "builder_version": str(builder_version),
        "input_artifact_refs": normalize_explain_ref_list(input_artifact_refs),
        "diff_refs": normalize_explain_ref_list(diff_refs),
        "witness_refs": normalize_explain_ref_list(witness_refs),
        "sections": sections,
        "hash_excluded_fields": list(EXPLAIN_HASH_EXCLUDED_FIELD_LIST),
    }

    if semantics_diagnostics_ref is not None:
        packet["semantics_diagnostics_ref"] = validate_explain_ref(semantics_diagnostics_ref)

    if validator_evidence_packet_refs:
        packet["validator_evidence_packet_refs"] = normalize_explain_ref_list(
            validator_evidence_packet_refs
        )

    if run_ir_mismatch is not None:
        packet["run_ir_mismatch"] = bool(run_ir_mismatch)
    if left_mismatch is not None:
        packet["left_mismatch"] = bool(left_mismatch)
    if right_mismatch is not None:
        packet["right_mismatch"] = bool(right_mismatch)

    if nonsemantic_fields:
        packet["nonsemantic_fields"] = _canonical_clone(dict(nonsemantic_fields))

    packet["explain_hash"] = explain_diff_hash(packet)
    return packet


def validate_explain_diff_packet(payload: Mapping[str, Any]) -> None:
    schema = payload.get("schema")
    if schema != EXPLAIN_DIFF_SCHEMA:
        raise ExplainDiffError("payload schema must be explain_diff@1")

    kind = _validate_explain_kind(str(payload.get("explain_kind") or ""))

    hash_excluded_fields = payload.get("hash_excluded_fields")
    if hash_excluded_fields != list(EXPLAIN_HASH_EXCLUDED_FIELD_LIST):
        raise ExplainDiffError("hash_excluded_fields does not match frozen exclusion set")

    for key in ("input_artifact_refs", "diff_refs", "witness_refs"):
        raw_refs = payload.get(key)
        if not isinstance(raw_refs, Sequence) or isinstance(raw_refs, (str, bytes, bytearray)):
            raise ExplainDiffError(f"{key} must be an array of refs")
        normalized = normalize_explain_ref_list([str(item) for item in raw_refs])
        if list(raw_refs) != normalized:
            raise ExplainDiffError(f"{key} must be canonical-sorted and unique")

    semantics_ref = payload.get("semantics_diagnostics_ref")
    if semantics_ref is not None:
        validate_explain_ref(str(semantics_ref))

    validator_refs = payload.get("validator_evidence_packet_refs")
    if validator_refs is not None:
        if not isinstance(validator_refs, Sequence) or isinstance(
            validator_refs,
            (str, bytes, bytearray),
        ):
            raise ExplainDiffError("validator_evidence_packet_refs must be an array")
        normalized_validator = normalize_explain_ref_list([str(item) for item in validator_refs])
        if list(validator_refs) != normalized_validator:
            raise ExplainDiffError(
                "validator_evidence_packet_refs must be canonical-sorted and unique"
            )

    sections = payload.get("sections")
    if not isinstance(sections, Mapping):
        raise ExplainDiffError("sections must be an object")

    required_sections = _required_sections_for_kind(kind)
    if not required_sections.issubset(set(str(key) for key in sections.keys())):
        raise ExplainDiffError(
            f"sections missing required entries for {kind}: "
            f"{sorted(required_sections - set(str(key) for key in sections.keys()))}"
        )

    expected_hash = explain_diff_hash(payload)
    actual_hash = payload.get("explain_hash")
    if not isinstance(actual_hash, str) or actual_hash != expected_hash:
        raise ExplainDiffError("explain_hash mismatch")
