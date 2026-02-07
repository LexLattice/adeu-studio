from __future__ import annotations

import json
from datetime import datetime, timezone
from typing import Any, Iterable, Sequence

from adeu_ir import SourceSpan, ValidatorAtomRef
from adeu_ir.models import JsonPatchOp

from .models import (
    AtomRef,
    CausalSlice,
    CauseChainItem,
    CoreDelta,
    DiffReport,
    DiffSummary,
    EvidenceChange,
    ExplanationItem,
    FlipExplanation,
    ModelAssignment,
    ModelAssignmentChange,
    ModelDelta,
    PrimaryChange,
    RepairHint,
    SolverDiff,
    StructuralDiff,
    ValidatorRunInput,
    ValidatorRunRef,
)

_STATUS_VALUES = {"SAT", "UNSAT", "UNKNOWN", "TIMEOUT", "ERROR", "INVALID_REQUEST"}
_STATUS_NO_RUNS = "NO_RUNS"
_STATUS_MISSING_LEFT = "MISSING_LEFT"
_STATUS_MISSING_RIGHT = "MISSING_RIGHT"
_ID_FIELD_ALLOWLIST = {
    "id",
    "object_id",
    "entity_id",
    "def_id",
    "sense_id",
    "statement_id",
    "exception_id",
    "bridge_id",
    "ambiguity_id",
    "option_id",
    "ir_id",
    "puzzle_id",
    "person_id",
    "speaker_id",
}
_SEVERITY_RANK = {"ERROR": 0, "WARN": 1, "INFO": 2}


def build_diff_report(
    left: Any,
    right: Any,
    *,
    left_id: str,
    right_id: str,
    left_runs: Sequence[Any] | None = None,
    right_runs: Sequence[Any] | None = None,
    summary_run_source: str | None = None,
    summary_recompute_mode: str | None = None,
    summary_left_backend: str | None = None,
    summary_right_backend: str | None = None,
    summary_left_timeout_ms: int | None = None,
    summary_right_timeout_ms: int | None = None,
) -> DiffReport:
    left_payload = _to_jsonable(left)
    right_payload = _to_jsonable(right)

    structural = _build_structural_diff(left_payload, right_payload)
    solver = _build_solver_diff(left_runs=left_runs or [], right_runs=right_runs or [])
    causal = _build_causal_slice(
        structural=structural,
        solver=solver,
        left_payload=left_payload,
        right_payload=right_payload,
    )
    summary = DiffSummary(
        status_flip=solver.status_flip,
        structural_patch_count=str(len(structural.json_patches)),
        solver_touched_atom_count=str(
            len(
                {
                    *solver.core_delta.added_atoms,
                    *solver.core_delta.removed_atoms,
                    *solver.model_delta.changed_atoms,
                }
            )
        ),
        causal_atom_count=str(len(causal.touched_atoms)),
        run_source=summary_run_source or "unknown",
        recompute_mode=summary_recompute_mode,
        left_backend=summary_left_backend,
        right_backend=summary_right_backend,
        left_timeout_ms=summary_left_timeout_ms,
        right_timeout_ms=summary_right_timeout_ms,
    )
    return DiffReport(
        left_id=left_id,
        right_id=right_id,
        structural=structural,
        solver=solver,
        causal_slice=causal,
        summary=summary,
    )


def build_flip_explanation(
    left: Any,
    right: Any,
    *,
    diff_report: DiffReport,
    left_check_status: str,
    right_check_status: str,
    max_hints: int = 10,
) -> FlipExplanation:
    left_payload = _to_jsonable(left)
    right_payload = _to_jsonable(right)
    left_resolver = _SpanResolver(left_payload)
    right_resolver = _SpanResolver(right_payload)

    check_status_flip = f"{left_check_status}\u2192{right_check_status}"
    solver_status_flip = diff_report.solver.status_flip
    flip_kind = solver_status_flip

    primary_changes = _build_primary_changes(
        diff_report=diff_report,
        left_payload=left_payload,
        right_payload=right_payload,
    )
    evidence_changes = _build_evidence_changes(
        solver=diff_report.solver,
        left_resolver=left_resolver,
        right_resolver=right_resolver,
    )
    cause_chain = _build_cause_chain(evidence_changes)
    repair_hints = _build_repair_hints(cause_chain, max_hints=max_hints)

    return FlipExplanation(
        flip_kind=flip_kind,
        check_status_flip=check_status_flip,
        solver_status_flip=solver_status_flip,
        primary_changes=primary_changes,
        evidence_changes=evidence_changes,
        cause_chain=cause_chain,
        repair_hints=repair_hints,
    )


def _to_jsonable(value: Any) -> Any:
    if hasattr(value, "model_dump"):
        return value.model_dump(mode="json", exclude_none=True)
    return value


def _build_structural_diff(left: Any, right: Any) -> StructuralDiff:
    patches: list[JsonPatchOp] = []
    _diff_to_patches(left, right, (), patches)

    patches.sort(key=_patch_sort_key)
    changed_paths = sorted(
        {
            patch.path
            for patch in patches
            if patch.path is not None
        }
        | {patch.from_path for patch in patches if patch.from_path}
    )

    changed_object_ids = sorted(
        {
            *_collect_changed_object_ids_from_values(left, right, patches),
            *_collect_changed_object_ids_from_paths(left, right, changed_paths),
        }
    )
    return StructuralDiff(
        json_patches=patches,
        changed_paths=changed_paths,
        changed_object_ids=changed_object_ids,
    )


def _diff_to_patches(left: Any, right: Any, path: tuple[str, ...], out: list[JsonPatchOp]) -> None:
    if left == right:
        return

    if isinstance(left, dict) and isinstance(right, dict):
        left_keys = set(left.keys())
        right_keys = set(right.keys())
        for key in sorted(left_keys | right_keys):
            child_path = path + (str(key),)
            if key not in right:
                out.append(JsonPatchOp(op="remove", path=_json_pointer(child_path)))
                continue
            if key not in left:
                out.append(
                    JsonPatchOp(op="add", path=_json_pointer(child_path), value=right[key])
                )
                continue
            _diff_to_patches(left[key], right[key], child_path, out)
        return

    if isinstance(left, list) and isinstance(right, list):
        max_len = max(len(left), len(right))
        for idx in range(max_len):
            child_path = path + (str(idx),)
            if idx >= len(right):
                out.append(JsonPatchOp(op="remove", path=_json_pointer(child_path)))
                continue
            if idx >= len(left):
                out.append(JsonPatchOp(op="add", path=_json_pointer(child_path), value=right[idx]))
                continue
            _diff_to_patches(left[idx], right[idx], child_path, out)
        return

    out.append(
        JsonPatchOp(op="replace", path=_json_pointer(path), value=right),
    )


def _patch_sort_key(patch: JsonPatchOp) -> tuple[str, str, str, str]:
    value_json = json.dumps(patch.value, sort_keys=True, separators=(",", ":"))
    from_path = patch.from_path or ""
    return (patch.path, patch.op, from_path, value_json)


def _json_pointer(parts: Sequence[str]) -> str:
    if not parts:
        return ""
    escaped = [part.replace("~", "~0").replace("/", "~1") for part in parts]
    return "/" + "/".join(escaped)


def _pointer_segments(path: str | None) -> tuple[str, ...]:
    if not path:
        return ()
    text = path if path.startswith("/") else f"/{path}"
    raw = text[1:].split("/")
    return tuple(segment.replace("~1", "/").replace("~0", "~") for segment in raw)


def _get_node(doc: Any, path: str | None) -> tuple[bool, Any]:
    node = doc
    for segment in _pointer_segments(path):
        if isinstance(node, dict):
            if segment not in node:
                return False, None
            node = node[segment]
            continue
        if isinstance(node, list):
            try:
                idx = int(segment)
            except ValueError:
                return False, None
            if idx < 0 or idx >= len(node):
                return False, None
            node = node[idx]
            continue
        return False, None
    return True, node


def _collect_ids_from_value(value: Any, out: set[str]) -> None:
    if isinstance(value, dict):
        for key, nested in value.items():
            if key in _ID_FIELD_ALLOWLIST and isinstance(nested, str) and nested:
                out.add(nested)
            _collect_ids_from_value(nested, out)
        return
    if isinstance(value, list):
        for nested in value:
            _collect_ids_from_value(nested, out)


def _collect_changed_object_ids_from_values(
    left: Any,
    right: Any,
    patches: Sequence[JsonPatchOp],
) -> set[str]:
    out: set[str] = set()
    for patch in patches:
        _collect_ids_from_value(patch.value, out)
        for pointer in [patch.path, patch.from_path]:
            if pointer is None:
                continue
            found_left, left_value = _get_node(left, pointer)
            if found_left:
                _collect_ids_from_value(left_value, out)
            found_right, right_value = _get_node(right, pointer)
            if found_right:
                _collect_ids_from_value(right_value, out)
    return out


def _resolve_object_id_for_path(left: Any, right: Any, path: str) -> str | None:
    segments = _pointer_segments(path)
    for depth in range(len(segments), -1, -1):
        partial = _json_pointer(segments[:depth])
        for source in (right, left):
            found, node = _get_node(source, partial)
            if not found or not isinstance(node, dict):
                continue
            object_id = node.get("id")
            if isinstance(object_id, str) and object_id:
                return object_id
    return None


def _collect_changed_object_ids_from_paths(left: Any, right: Any, paths: Sequence[str]) -> set[str]:
    out: set[str] = set()
    for path in paths:
        object_id = _resolve_object_id_for_path(left, right, path)
        if object_id:
            out.add(object_id)
    return out


def _normalize_atom_map_value(value: Any) -> dict[str, AtomRef]:
    if isinstance(value, dict):
        mapped: dict[str, AtomRef] = {}
        for atom_name, atom_ref in value.items():
            mapped[str(atom_name)] = AtomRef.model_validate(atom_ref)
        return {key: mapped[key] for key in sorted(mapped)}

    if isinstance(value, list):
        mapped = {}
        for raw in value:
            atom = ValidatorAtomRef.model_validate(raw)
            mapped[atom.assertion_name] = AtomRef(
                object_id=atom.object_id,
                json_path=atom.json_path,
            )
        return {key: mapped[key] for key in sorted(mapped)}

    return {}


def _normalize_run(raw: Any) -> ValidatorRunRef:
    if isinstance(raw, ValidatorRunRef):
        return raw

    if isinstance(raw, ValidatorRunInput):
        return ValidatorRunRef(
            run_id=raw.run_id,
            created_at=raw.created_at,
            backend=raw.backend,
            backend_version=raw.backend_version,
            timeout_ms=raw.timeout_ms,
            options_json=raw.options_json,
            request_hash=raw.request_hash,
            formula_hash=raw.formula_hash,
            status=raw.status,
            evidence_json=raw.evidence_json,
            atom_map_json=_normalize_atom_map_value(raw.atom_map_json),
        )

    if hasattr(raw, "request") and hasattr(raw, "result"):
        request = raw.request
        result = raw.result
        atom_map_json = {
            atom.assertion_name: AtomRef(
                object_id=atom.object_id,
                json_path=atom.json_path,
            )
            for atom in getattr(request.payload, "atom_map", []) or []
        }
        return ValidatorRunRef(
            run_id=None,
            created_at=None,
            backend=getattr(result, "backend", None),
            backend_version=getattr(result, "backend_version", None),
            timeout_ms=getattr(result, "timeout_ms", None),
            options_json=getattr(result, "options", {}) or {},
            request_hash=getattr(result, "request_hash", None),
            formula_hash=getattr(result, "formula_hash", None),
            status=getattr(result, "status", None),
            evidence_json=getattr(result.evidence, "model_dump", lambda **_: {})(
                mode="json",
                exclude_none=True,
            ),
            atom_map_json={key: atom_map_json[key] for key in sorted(atom_map_json)},
        )

    if isinstance(raw, dict):
        payload = dict(raw)
    else:
        payload = {
            "run_id": getattr(raw, "run_id", None),
            "created_at": getattr(raw, "created_at", None),
            "backend": getattr(raw, "backend", None),
            "backend_version": getattr(raw, "backend_version", None),
            "timeout_ms": getattr(raw, "timeout_ms", None),
            "options_json": getattr(raw, "options_json", {}) or {},
            "request_hash": getattr(raw, "request_hash", None),
            "formula_hash": getattr(raw, "formula_hash", None),
            "status": getattr(raw, "status", None),
            "evidence_json": getattr(raw, "evidence_json", {}) or {},
            "atom_map_json": getattr(raw, "atom_map_json", {}) or {},
        }

    payload["atom_map_json"] = _normalize_atom_map_value(payload.get("atom_map_json"))
    return ValidatorRunRef.model_validate(payload)


def _normalize_runs(raw_runs: Sequence[Any]) -> list[ValidatorRunRef]:
    normalized = [_normalize_run(raw) for raw in raw_runs]
    normalized.sort(key=_run_sort_key)
    return normalized


def _run_sort_key(run: ValidatorRunRef) -> tuple[str, str, str, str]:
    return (
        run.request_hash or "",
        run.formula_hash or "",
        run.created_at or "",
        run.run_id or "",
    )


def _pair_key(run: ValidatorRunRef) -> tuple[str, str] | None:
    if not run.request_hash or not run.formula_hash:
        return None
    return (run.request_hash, run.formula_hash)


def _latest_run(runs: Iterable[ValidatorRunRef]) -> ValidatorRunRef:
    latest = None
    latest_key: tuple[tuple[int, str], str, str] | None = None
    for run in runs:
        key = (_timestamp_rank(run.created_at), run.created_at or "", run.run_id or "")
        if latest is None or key > latest_key:
            latest = run
            latest_key = key
    assert latest is not None
    return latest


def _parse_timestamp(value: str | None) -> datetime | None:
    if not value:
        return None
    text = value
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    try:
        return datetime.fromisoformat(text)
    except ValueError:
        return None


def _timestamp_rank(value: str | None) -> tuple[int, str]:
    parsed = _parse_timestamp(value)
    if parsed is None:
        return (0, value or "")
    if parsed.tzinfo is not None:
        canonical = parsed.astimezone(timezone.utc).isoformat()
    else:
        canonical = parsed.isoformat()
    return (1, canonical)


def _build_solver_diff(left_runs: Sequence[Any], right_runs: Sequence[Any]) -> SolverDiff:
    left = _normalize_runs(left_runs)
    right = _normalize_runs(right_runs)

    left_by_key: dict[tuple[str, str], list[ValidatorRunRef]] = {}
    right_by_key: dict[tuple[str, str], list[ValidatorRunRef]] = {}
    for run in left:
        key = _pair_key(run)
        if key is not None:
            left_by_key.setdefault(key, []).append(run)
    for run in right:
        key = _pair_key(run)
        if key is not None:
            right_by_key.setdefault(key, []).append(run)

    shared_keys = sorted(set(left_by_key) & set(right_by_key))
    if not shared_keys:
        status_flip = _status_for_missing_pairs(left, right)
        return SolverDiff(
            left_runs=[],
            right_runs=[],
            status_flip=status_flip,
            core_delta=CoreDelta(),
            model_delta=ModelDelta(),
            request_hash_changed=False,
            formula_hash_changed=False,
            unpaired_left_hashes=_sorted_hashes(left_by_key),
            unpaired_right_hashes=_sorted_hashes(right_by_key),
        )

    chosen_pairs = {
        key: (_latest_run(left_by_key[key]), _latest_run(right_by_key[key])) for key in shared_keys
    }
    primary_key = _choose_primary_pair_key(chosen_pairs)
    primary_left, primary_right = chosen_pairs[primary_key]

    core_delta = _diff_unsat_core(primary_left, primary_right)
    model_delta = _diff_model_assignments(primary_left, primary_right)

    left_status = _normalized_status(primary_left.status)
    right_status = _normalized_status(primary_right.status)
    status_flip = f"{left_status}\u2192{right_status}"

    left_runs_out = [chosen_pairs[key][0] for key in shared_keys]
    right_runs_out = [chosen_pairs[key][1] for key in shared_keys]
    return SolverDiff(
        left_runs=left_runs_out,
        right_runs=right_runs_out,
        status_flip=status_flip,
        core_delta=core_delta,
        model_delta=model_delta,
        request_hash_changed=(primary_left.request_hash != primary_right.request_hash),
        formula_hash_changed=(primary_left.formula_hash != primary_right.formula_hash),
        unpaired_left_hashes=sorted(
            _serialize_pair_key(key) for key in set(left_by_key) - set(shared_keys)
        ),
        unpaired_right_hashes=sorted(
            _serialize_pair_key(key) for key in set(right_by_key) - set(shared_keys)
        ),
    )


def _status_for_missing_pairs(
    left: Sequence[ValidatorRunRef],
    right: Sequence[ValidatorRunRef],
) -> str:
    if not left and not right:
        return _STATUS_NO_RUNS
    if not left and right:
        return _STATUS_MISSING_LEFT
    if left and not right:
        return _STATUS_MISSING_RIGHT
    return _STATUS_NO_RUNS


def _sorted_hashes(keyed_runs: dict[tuple[str, str], list[ValidatorRunRef]]) -> list[str]:
    return sorted(_serialize_pair_key(key) for key in keyed_runs)


def _serialize_pair_key(pair_key: tuple[str, str]) -> str:
    return f"{pair_key[0]}:{pair_key[1]}"


def _choose_primary_pair_key(
    pairs: dict[tuple[str, str], tuple[ValidatorRunRef, ValidatorRunRef]]
) -> tuple[str, str]:
    ranked: list[tuple[tuple[int, str], str, str, tuple[str, str]]] = []
    for key, (left, right) in pairs.items():
        left_rank = _timestamp_rank(left.created_at)
        right_rank = _timestamp_rank(right.created_at)
        max_rank = left_rank if left_rank >= right_rank else right_rank
        ranked.append((max_rank, key[0], key[1], key))
    ranked.sort()
    return ranked[-1][3]


def _normalized_status(value: str | None) -> str:
    if value in _STATUS_VALUES:
        return value
    return "UNKNOWN"


def _extract_unsat_core(run: ValidatorRunRef) -> set[str]:
    raw_core = run.evidence_json.get("unsat_core")
    if not isinstance(raw_core, list):
        return set()
    return {str(item) for item in raw_core if str(item)}


def _extract_model(run: ValidatorRunRef) -> dict[str, str]:
    raw_model = run.evidence_json.get("model")
    if not isinstance(raw_model, dict):
        return {}
    out = {}
    for key, value in raw_model.items():
        key_text = str(key)
        value_text = str(value)
        if key_text:
            out[key_text] = value_text
    return out


def _diff_unsat_core(left: ValidatorRunRef, right: ValidatorRunRef) -> CoreDelta:
    left_core = _extract_unsat_core(left)
    right_core = _extract_unsat_core(right)
    return CoreDelta(
        added_atoms=sorted(right_core - left_core),
        removed_atoms=sorted(left_core - right_core),
    )


def _diff_model_assignments(left: ValidatorRunRef, right: ValidatorRunRef) -> ModelDelta:
    left_model = _extract_model(left)
    right_model = _extract_model(right)
    atom_names = sorted(set(left.atom_map_json) | set(right.atom_map_json))

    added: list[ModelAssignment] = []
    removed: list[ModelAssignment] = []
    changed: list[ModelAssignmentChange] = []
    for atom_name in atom_names:
        left_value = left_model.get(atom_name)
        right_value = right_model.get(atom_name)
        if left_value is None and right_value is None:
            continue
        if left_value is None and right_value is not None:
            added.append(ModelAssignment(atom=atom_name, value=right_value))
            continue
        if left_value is not None and right_value is None:
            removed.append(ModelAssignment(atom=atom_name, value=left_value))
            continue
        if left_value != right_value:
            changed.append(
                ModelAssignmentChange(
                    atom=atom_name,
                    left_value=left_value,
                    right_value=right_value,
                )
            )

    return ModelDelta(
        added_assignments=added,
        removed_assignments=removed,
        changed_assignments=changed,
        changed_atoms=sorted(change.atom for change in changed),
    )


def _paths_match_or_overlap(path_a: str | None, path_b: str | None) -> bool:
    if not path_a or not path_b:
        return False
    a = _pointer_segments(path_a)
    b = _pointer_segments(path_b)
    if a == b:
        return True
    if len(a) < len(b):
        return b[: len(a)] == a
    return a[: len(b)] == b


def _build_causal_slice(
    *,
    structural: StructuralDiff,
    solver: SolverDiff,
    left_payload: Any,
    right_payload: Any,
) -> CausalSlice:
    changed_object_ids = set(structural.changed_object_ids)
    changed_paths = set(structural.changed_paths)
    touched_atoms = sorted(
        {
            *solver.core_delta.added_atoms,
            *solver.core_delta.removed_atoms,
            *solver.model_delta.changed_atoms,
        }
    )

    atom_ref_map: dict[str, AtomRef] = {}
    for run in solver.left_runs + solver.right_runs:
        for atom_name, atom_ref in run.atom_map_json.items():
            atom_ref_map.setdefault(atom_name, atom_ref)

    left_resolver = _SpanResolver(left_payload)
    right_resolver = _SpanResolver(right_payload)

    causal_atoms: list[str] = []
    touched_object_ids: set[str] = set()
    touched_json_paths: set[str] = set()
    explanation_items: list[ExplanationItem] = []
    for atom_name in touched_atoms:
        atom_ref = atom_ref_map.get(atom_name)
        if atom_ref is None:
            continue

        object_hit = bool(atom_ref.object_id and atom_ref.object_id in changed_object_ids)
        path_hit = False
        if atom_ref.json_path:
            path_hit = any(
                _paths_match_or_overlap(atom_ref.json_path, path) for path in changed_paths
            )
        if not object_hit and not path_hit:
            continue

        causal_atoms.append(atom_name)
        if atom_ref.object_id:
            touched_object_ids.add(atom_ref.object_id)
        if atom_ref.json_path:
            touched_json_paths.add(atom_ref.json_path)
        span = left_resolver.resolve_span(
            object_id=atom_ref.object_id,
            json_path=atom_ref.json_path,
        )
        if span is None:
            span = right_resolver.resolve_span(
                object_id=atom_ref.object_id,
                json_path=atom_ref.json_path,
            )
        explanation_items.append(
            ExplanationItem(
                atom_name=atom_name,
                object_id=atom_ref.object_id,
                json_path=atom_ref.json_path,
                span=span,
            )
        )

    explanation_items.sort(
        key=lambda item: (item.atom_name, item.object_id or "", item.json_path or "")
    )
    return CausalSlice(
        touched_atoms=sorted(set(causal_atoms)),
        touched_object_ids=sorted(touched_object_ids),
        touched_json_paths=sorted(touched_json_paths),
        explanation_items=explanation_items,
    )


def _build_primary_changes(
    *,
    diff_report: DiffReport,
    left_payload: Any,
    right_payload: Any,
) -> list[PrimaryChange]:
    grouped: dict[tuple[str, str], dict[str, Any]] = {}
    for patch in diff_report.structural.json_patches:
        candidate_paths = [patch.path]
        if patch.from_path:
            candidate_paths.append(patch.from_path)
        object_id = None
        object_kind = "unknown"
        for path in candidate_paths:
            object_kind = _object_kind_for_path(path)
            object_id = _resolve_object_id_for_path(left_payload, right_payload, path)
            if object_id is not None:
                break

        key = (object_kind, object_id or "")
        bucket = grouped.setdefault(
            key,
            {
                "object_kind": object_kind,
                "object_id": object_id,
                "changed_paths": set(),
                "patch_count": 0,
            },
        )
        if patch.path:
            bucket["changed_paths"].add(patch.path)
        if patch.from_path:
            bucket["changed_paths"].add(patch.from_path)
        bucket["patch_count"] += 1

    out = [
        PrimaryChange(
            object_kind=value["object_kind"],
            object_id=value["object_id"],
            changed_paths=sorted(value["changed_paths"]),
            patch_count=value["patch_count"],
        )
        for value in grouped.values()
    ]
    out.sort(key=lambda item: (item.object_kind, item.object_id or "", item.changed_paths))
    return out


def _build_evidence_changes(
    *,
    solver: SolverDiff,
    left_resolver: "_SpanResolver",
    right_resolver: "_SpanResolver",
) -> list[EvidenceChange]:
    atom_ref_map: dict[str, AtomRef] = {}
    for run in solver.left_runs + solver.right_runs:
        for atom_name, atom_ref in run.atom_map_json.items():
            atom_ref_map.setdefault(atom_name, atom_ref)

    changes: list[EvidenceChange] = []
    for atom_name in solver.core_delta.added_atoms:
        changes.append(
            _to_evidence_change(
                atom_name=atom_name,
                evidence_kind="core_added",
                severity="ERROR",
                atom_ref=atom_ref_map.get(atom_name),
                left_resolver=left_resolver,
                right_resolver=right_resolver,
            )
        )
    for atom_name in solver.core_delta.removed_atoms:
        changes.append(
            _to_evidence_change(
                atom_name=atom_name,
                evidence_kind="core_removed",
                severity="ERROR",
                atom_ref=atom_ref_map.get(atom_name),
                left_resolver=left_resolver,
                right_resolver=right_resolver,
            )
        )
    for assignment in solver.model_delta.added_assignments:
        changes.append(
            _to_evidence_change(
                atom_name=assignment.atom,
                evidence_kind="model_added",
                severity="WARN",
                atom_ref=atom_ref_map.get(assignment.atom),
                left_resolver=left_resolver,
                right_resolver=right_resolver,
            )
        )
    for assignment in solver.model_delta.removed_assignments:
        changes.append(
            _to_evidence_change(
                atom_name=assignment.atom,
                evidence_kind="model_removed",
                severity="WARN",
                atom_ref=atom_ref_map.get(assignment.atom),
                left_resolver=left_resolver,
                right_resolver=right_resolver,
            )
        )
    for assignment in solver.model_delta.changed_assignments:
        changes.append(
            _to_evidence_change(
                atom_name=assignment.atom,
                evidence_kind="model_changed",
                severity="WARN",
                atom_ref=atom_ref_map.get(assignment.atom),
                left_resolver=left_resolver,
                right_resolver=right_resolver,
            )
        )

    changes.sort(
        key=lambda item: (
            _SEVERITY_RANK.get(item.severity, 99),
            item.object_kind,
            item.object_id or "",
            item.json_path or "",
            item.atom_name,
            item.evidence_kind,
        )
    )
    return changes


def _to_evidence_change(
    *,
    atom_name: str,
    evidence_kind: str,
    severity: str,
    atom_ref: AtomRef | None,
    left_resolver: "_SpanResolver",
    right_resolver: "_SpanResolver",
) -> EvidenceChange:
    object_id = atom_ref.object_id if atom_ref is not None else None
    json_path = atom_ref.json_path if atom_ref is not None else None
    return EvidenceChange(
        atom_name=atom_name,
        evidence_kind=evidence_kind,
        severity=severity,
        object_kind=_object_kind_for_path(json_path),
        object_id=object_id,
        json_path=json_path,
        left_span=left_resolver.resolve_span(object_id=object_id, json_path=json_path),
        right_span=right_resolver.resolve_span(object_id=object_id, json_path=json_path),
    )


def _build_cause_chain(evidence_changes: Sequence[EvidenceChange]) -> list[CauseChainItem]:
    out = [
        CauseChainItem(
            severity=change.severity,
            object_kind=change.object_kind,
            object_id=change.object_id,
            json_path=change.json_path,
            atom_name=change.atom_name,
            evidence_kind=change.evidence_kind,
            message=_cause_message(change),
            left_span=change.left_span,
            right_span=change.right_span,
        )
        for change in evidence_changes
    ]
    out.sort(
        key=lambda item: (
            _SEVERITY_RANK.get(item.severity, 99),
            item.object_kind,
            item.object_id or "",
            item.json_path or "",
            item.atom_name,
        )
    )
    return out


def _cause_message(change: EvidenceChange) -> str:
    if change.evidence_kind == "core_added":
        return "Atom entered UNSAT core on the right variant."
    if change.evidence_kind == "core_removed":
        return "Atom left UNSAT core compared to the left variant."
    if change.evidence_kind == "model_added":
        return "Atom assignment exists only in the right SAT model."
    if change.evidence_kind == "model_removed":
        return "Atom assignment exists only in the left SAT model."
    return "Atom assignment value changed across SAT models."


def _build_repair_hints(
    cause_chain: Sequence[CauseChainItem],
    *,
    max_hints: int,
) -> list[RepairHint]:
    hints: dict[tuple[str, str, str, str], RepairHint] = {}
    for item in cause_chain:
        hint_text = _hint_for_cause(item)
        key = (
            item.object_kind,
            item.object_id or "",
            item.json_path or "",
            hint_text,
        )
        hints[key] = RepairHint(
            object_kind=item.object_kind,
            object_id=item.object_id,
            json_path=item.json_path,
            hint=hint_text,
        )
    out = [hints[key] for key in sorted(hints)]
    return out[: max(0, max_hints)]


def _hint_for_cause(item: CauseChainItem) -> str:
    if item.object_kind == "claim":
        return "Review claim sense selection; it drives the solver atom involved in the flip."
    if item.object_kind == "link":
        return (
            "Review inferential link direction/type; "
            "it participates directly in the solver delta."
        )
    if item.object_kind == "ambiguity":
        return (
            "Review ambiguity option choice; "
            "it affects atom activation in the compared variants."
        )
    if item.object_kind == "statement":
        return "Review norm kind/scope and attached exceptions for this statement."
    if item.object_kind == "exception":
        return "Review exception condition/priority; it can change active conflict atoms."
    if item.object_kind == "sense":
        return (
            "Review sense assignment and linked claims; "
            "this sense appears in changed solver evidence."
        )
    return "Review this node and nearby constraints; it appears in changed solver evidence."


def _object_kind_for_path(path: str | None) -> str:
    parts = _pointer_segments(path)
    if not parts:
        return "unknown"
    if parts[0] == "D_norm":
        if len(parts) >= 2 and parts[1] == "statements":
            return "statement"
        if len(parts) >= 2 and parts[1] == "exceptions":
            return "exception"
        return "norm"
    if parts[0] == "bridges":
        return "bridge"
    if parts[0] == "ambiguity":
        return "ambiguity"
    if parts[0] == "claims":
        return "claim"
    if parts[0] == "links":
        return "link"
    if parts[0] == "senses":
        return "sense"
    if parts[0] == "terms":
        return "term"
    if parts[0] == "people":
        return "person"
    if parts[0] == "statements":
        return "statement"
    return "unknown"


def _parse_span(value: Any) -> SourceSpan | None:
    if not isinstance(value, dict):
        return None
    start = value.get("start")
    end = value.get("end")
    if not isinstance(start, int) or not isinstance(end, int):
        return None
    try:
        return SourceSpan.model_validate({"start": start, "end": end})
    except Exception:
        return None


def _extract_span_from_node(node: Any) -> SourceSpan | None:
    if not isinstance(node, dict):
        return None
    provenance = node.get("provenance")
    if isinstance(provenance, dict):
        prov_span = _parse_span(provenance.get("span"))
        if prov_span is not None:
            return prov_span
    node_span = _parse_span(node.get("span"))
    if node_span is not None:
        return node_span
    return None


class _SpanResolver:
    def __init__(self, payload: Any) -> None:
        self._payload = payload
        self._id_to_span: dict[str, SourceSpan] = {}
        self._index_ids(payload)

    def _index_ids(self, node: Any) -> None:
        if isinstance(node, dict):
            object_id = node.get("id")
            if isinstance(object_id, str) and object_id and object_id not in self._id_to_span:
                span = _extract_span_from_node(node)
                if span is not None:
                    self._id_to_span[object_id] = span
            for value in node.values():
                self._index_ids(value)
            return
        if isinstance(node, list):
            for item in node:
                self._index_ids(item)

    def resolve_span(self, *, object_id: str | None, json_path: str | None) -> SourceSpan | None:
        if object_id and object_id in self._id_to_span:
            return self._id_to_span[object_id]
        if json_path:
            node = self._resolve_path_root_node(json_path)
            if node is not None:
                return _extract_span_from_node(node)
        return None

    def _resolve_path_root_node(self, path: str) -> Any:
        segments = _pointer_segments(path)
        if len(segments) < 2:
            return None
        list_roots = {
            ("D_norm", "statements"),
            ("D_norm", "exceptions"),
            ("ambiguity",),
            ("bridges",),
            ("claims",),
            ("links",),
        }
        root: tuple[str, ...]
        index_segment: str
        if len(segments) >= 3 and (segments[0], segments[1]) in {
            ("D_norm", "statements"),
            ("D_norm", "exceptions"),
        }:
            root = (segments[0], segments[1])
            index_segment = segments[2]
        else:
            root = (segments[0],)
            index_segment = segments[1]
        if root not in list_roots:
            return None
        try:
            item_index = int(index_segment)
        except ValueError:
            return None
        found, container = _get_node(self._payload, _json_pointer(root))
        if not found or not isinstance(container, list):
            return None
        if item_index < 0 or item_index >= len(container):
            return None
        return container[item_index]
