from __future__ import annotations

import json
from datetime import datetime, timezone
from typing import Any, Iterable, Sequence

from adeu_ir import ValidatorAtomRef
from adeu_ir.models import JsonPatchOp

from .models import (
    AtomRef,
    CausalSlice,
    CoreDelta,
    DiffReport,
    DiffSummary,
    ExplanationItem,
    ModelAssignment,
    ModelAssignmentChange,
    ModelDelta,
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


def build_diff_report(
    left: Any,
    right: Any,
    *,
    left_id: str,
    right_id: str,
    left_runs: Sequence[Any] | None = None,
    right_runs: Sequence[Any] | None = None,
) -> DiffReport:
    left_payload = _to_jsonable(left)
    right_payload = _to_jsonable(right)

    structural = _build_structural_diff(left_payload, right_payload)
    solver = _build_solver_diff(left_runs=left_runs or [], right_runs=right_runs or [])
    causal = _build_causal_slice(structural=structural, solver=solver)
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
    )
    return DiffReport(
        left_id=left_id,
        right_id=right_id,
        structural=structural,
        solver=solver,
        causal_slice=causal,
        summary=summary,
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


def _build_causal_slice(structural: StructuralDiff, solver: SolverDiff) -> CausalSlice:
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
        explanation_items.append(
            ExplanationItem(
                atom_name=atom_name,
                object_id=atom_ref.object_id,
                json_path=atom_ref.json_path,
                span=None,
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
