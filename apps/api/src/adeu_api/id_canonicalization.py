from __future__ import annotations

import json
import re
from collections.abc import Mapping
from typing import Any, Callable

from adeu_ir import AdeuIR, stable_id

_DEFINED_PATTERN = re.compile(r"\(defined\s+([^\s()]+)\)")


def _provenance_key(provenance: Mapping[str, Any] | None) -> str:
    if not provenance:
        return ""
    span = provenance.get("span") or {}
    return "|".join(
        [
            str(provenance.get("doc_ref") or ""),
            str(span.get("start") if isinstance(span, Mapping) else ""),
            str(span.get("end") if isinstance(span, Mapping) else ""),
            str(provenance.get("quote") or ""),
        ]
    )


def _json_key(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def _canonical_id(parts: list[str], *, prefix: str) -> str:
    return stable_id(*parts, prefix=prefix)


def _build_id_map(
    items: list[dict[str, Any]],
    *,
    prefix: str,
    key_parts_fn: Callable[[dict[str, Any], int], list[str]],
    id_key: str = "id",
) -> dict[str, str]:
    mapping: dict[str, str] = {}
    used: set[str] = set()
    for idx, item in enumerate(items):
        old_id = str(item.get(id_key) or "")
        parts = key_parts_fn(item, idx)
        new_id = _canonical_id(parts, prefix=prefix)
        suffix = 0
        while new_id in used:
            suffix += 1
            new_id = _canonical_id(parts + [f"dup:{suffix}"], prefix=prefix)
        used.add(new_id)
        if old_id:
            mapping[old_id] = new_id
        item[id_key] = new_id
    return mapping


def _rewrite_ref(
    ref: dict[str, Any] | None,
    *,
    ent_map: dict[str, str],
    def_map: dict[str, str],
) -> None:
    if ref is None:
        return
    ref_type = ref.get("ref_type")
    if ref_type == "entity":
        old = str(ref.get("entity_id") or "")
        ref["entity_id"] = ent_map.get(old, old)
        return
    if ref_type == "def":
        old = str(ref.get("def_id") or "")
        ref["def_id"] = def_map.get(old, old)


def _normalized_ref(
    ref: dict[str, Any] | None,
    *,
    ent_map: dict[str, str],
    def_map: dict[str, str],
) -> dict[str, Any] | None:
    if ref is None:
        return None
    copied = dict(ref)
    _rewrite_ref(copied, ent_map=ent_map, def_map=def_map)
    return copied


def _rewrite_predicate_def_ids(predicate: str | None, *, def_map: dict[str, str]) -> str | None:
    if predicate is None:
        return None

    def _repl(match: re.Match[str]) -> str:
        old_id = match.group(1)
        new_id = def_map.get(old_id, old_id)
        return f"(defined {new_id})"

    return _DEFINED_PATTERN.sub(_repl, predicate)


def canonicalize_ir_ids(ir: AdeuIR) -> AdeuIR:
    data = ir.model_dump(mode="json", by_alias=True, exclude_none=False)

    o_channel = data.get("O") or {}
    entities = o_channel.get("entities") or []
    definitions = o_channel.get("definitions") or []

    ent_map = _build_id_map(
        entities,
        prefix="ent",
        key_parts_fn=lambda e, idx: [
            str(idx),
            str(e.get("name") or ""),
            str(e.get("kind") or ""),
            _provenance_key(e.get("provenance")),
        ],
    )
    def_map = _build_id_map(
        definitions,
        prefix="def",
        key_parts_fn=lambda d, idx: [
            str(idx),
            str(d.get("term") or ""),
            str(d.get("meaning") or ""),
            _provenance_key(d.get("provenance")),
        ],
    )

    d_norm = data.get("D_norm") or {}
    statements = d_norm.get("statements") or []

    def _statement_key_parts(stmt: dict[str, Any], idx: int) -> list[str]:
        subject = _normalized_ref(stmt.get("subject"), ent_map=ent_map, def_map=def_map)
        action = dict(stmt.get("action") or {})
        action["object"] = _normalized_ref(action.get("object"), ent_map=ent_map, def_map=def_map)
        condition = dict(stmt.get("condition") or {})
        condition["predicate"] = _rewrite_predicate_def_ids(
            condition.get("predicate"), def_map=def_map
        )
        return [
            str(idx),
            str(stmt.get("kind") or ""),
            _json_key(subject or {}),
            _json_key(action),
            _json_key(stmt.get("scope") or {}),
            _provenance_key(stmt.get("provenance")),
            _json_key(condition),
        ]

    statement_map = _build_id_map(
        statements,
        prefix="dn",
        key_parts_fn=_statement_key_parts,
    )
    for stmt in statements:
        _rewrite_ref(stmt.get("subject"), ent_map=ent_map, def_map=def_map)
        action = stmt.get("action") or {}
        _rewrite_ref(action.get("object"), ent_map=ent_map, def_map=def_map)
        condition = stmt.get("condition") or {}
        condition["predicate"] = _rewrite_predicate_def_ids(
            condition.get("predicate"), def_map=def_map
        )

    exceptions = d_norm.get("exceptions") or []

    def _exception_key_parts(ex: dict[str, Any], idx: int) -> list[str]:
        condition = dict(ex.get("condition") or {})
        condition["predicate"] = _rewrite_predicate_def_ids(
            condition.get("predicate"), def_map=def_map
        )
        return [
            str(idx),
            str(ex.get("effect") or ""),
            str(ex.get("priority") or ""),
            _json_key(condition),
            _provenance_key(ex.get("provenance")),
        ]

    _build_id_map(
        exceptions,
        prefix="ex",
        key_parts_fn=_exception_key_parts,
    )
    for ex in exceptions:
        ex["applies_to"] = [statement_map.get(str(x), str(x)) for x in (ex.get("applies_to") or [])]
        condition = ex.get("condition") or {}
        condition["predicate"] = _rewrite_predicate_def_ids(
            condition.get("predicate"), def_map=def_map
        )

    d_phys = data.get("D_phys") or {}
    _build_id_map(
        d_phys.get("constraints") or [],
        prefix="dp",
        key_parts_fn=lambda c, idx: [
            str(idx),
            str(c.get("kind") or ""),
            str(c.get("statement") or ""),
            _provenance_key(c.get("provenance")),
        ],
    )

    e_channel = data.get("E") or {}
    _build_id_map(
        e_channel.get("claims") or [],
        prefix="ec",
        key_parts_fn=lambda c, idx: [
            str(idx),
            str(c.get("kind") or ""),
            str(c.get("statement") or ""),
            _provenance_key(c.get("provenance")),
        ],
    )

    u_channel = data.get("U") or {}
    _build_id_map(
        u_channel.get("goals") or [],
        prefix="ug",
        key_parts_fn=lambda g, idx: [
            str(idx),
            str(g.get("kind") or ""),
            str(g.get("statement") or ""),
            _provenance_key(g.get("provenance")),
        ],
    )

    bridges = data.get("bridges") or []
    _build_id_map(
        bridges,
        prefix="br",
        key_parts_fn=lambda b, idx: [
            str(idx),
            str(b.get("status") or ""),
            str(b.get("bridge_type") or ""),
            str(b.get("from_channel") or ""),
            str(b.get("to_channel") or ""),
            str(b.get("justification_text") or ""),
            _provenance_key(b.get("provenance")),
        ],
    )

    ambiguities = data.get("ambiguity") or []
    _build_id_map(
        ambiguities,
        prefix="amb",
        key_parts_fn=lambda a, idx: [
            str(idx),
            str(a.get("issue") or ""),
            _json_key(a.get("span") or {}),
        ],
    )
    for amb in ambiguities:
        options = amb.get("options") or []
        _build_id_map(
            options,
            prefix="opt",
            id_key="option_id",
            key_parts_fn=lambda option, opt_idx: [
                str(opt_idx),
                str(amb.get("id") or ""),
                str(option.get("label") or ""),
                str(option.get("effect") or ""),
            ],
        )

    canonical_without_ir_id = dict(data)
    canonical_without_ir_id["ir_id"] = "__canonical__"
    data["ir_id"] = _canonical_id(
        [
            str((data.get("context") or {}).get("doc_id") or ""),
            _json_key(canonical_without_ir_id),
        ],
        prefix="ir",
    )
    return AdeuIR.model_validate(data)
