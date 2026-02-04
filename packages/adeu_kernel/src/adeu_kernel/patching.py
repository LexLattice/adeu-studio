from __future__ import annotations

import copy
import json
from dataclasses import dataclass
from typing import Any, Iterable

from adeu_ir import AdeuIR, CheckReason, ReasonCode, ReasonSeverity
from adeu_ir.models import AmbiguityOption, JsonPatchOp
from pydantic import ValidationError

DEFAULT_ALLOWED_PREFIXES = (
    "/D_norm/statements",
    "/D_norm/exceptions",
    "/O/entities",
    "/O/definitions",
    "/bridges",
    "/ambiguity",
    "/context/time_eval",
)


@dataclass(frozen=True)
class PatchValidationError(Exception):
    reason: CheckReason


def _err(message: str, *, json_path: str | None = None) -> PatchValidationError:
    return PatchValidationError(
        reason=CheckReason(
            code=ReasonCode.AMBIGUITY_OPTION_INVALID,
            severity=ReasonSeverity.ERROR,
            message=message,
            json_path=json_path,
        )
    )


def _encode_patch_size_bytes(patch_ops: Iterable[JsonPatchOp]) -> int:
    payload = [
        op.model_dump(mode="json", by_alias=True, exclude_none=True) for op in patch_ops
    ]
    return len(json.dumps(payload, separators=(",", ":"), sort_keys=True).encode("utf-8"))


def _allowed_path(path: str, *, allowed_prefixes: tuple[str, ...]) -> bool:
    for prefix in allowed_prefixes:
        if path == prefix or path.startswith(prefix + "/"):
            return True
    return False


def _parse_pointer(path: str) -> list[str]:
    if not path.startswith("/"):
        raise _err("json pointer path must start with '/'", json_path=path)
    # RFC 6901: split on '/', decode ~0 -> ~ and ~1 -> /
    parts = path.split("/")[1:]
    return [p.replace("~1", "/").replace("~0", "~") for p in parts]


def _resolve_parent(doc: Any, path: str) -> tuple[Any, str]:
    parts = _parse_pointer(path)
    if not parts:
        raise _err("patching the document root is not allowed", json_path=path)

    cur: Any = doc
    for seg in parts[:-1]:
        if isinstance(cur, dict):
            if seg not in cur:
                raise _err("path does not exist", json_path=path)
            cur = cur[seg]
            continue
        if isinstance(cur, list):
            try:
                idx = int(seg)
            except ValueError as e:
                raise _err("list segment must be an int index", json_path=path) from e
            if idx < 0 or idx >= len(cur):
                raise _err("list index out of range", json_path=path)
            cur = cur[idx]
            continue
        raise _err("path traversal hit a non-container", json_path=path)

    return cur, parts[-1]


def _get_value(doc: Any, path: str) -> Any:
    parts = _parse_pointer(path)
    cur: Any = doc
    for seg in parts:
        if isinstance(cur, dict):
            if seg not in cur:
                raise _err("path does not exist", json_path=path)
            cur = cur[seg]
            continue
        if isinstance(cur, list):
            try:
                idx = int(seg)
            except ValueError as e:
                raise _err("list segment must be an int index", json_path=path) from e
            if idx < 0 or idx >= len(cur):
                raise _err("list index out of range", json_path=path)
            cur = cur[idx]
            continue
        raise _err("path traversal hit a non-container", json_path=path)
    return cur


def apply_json_patch(
    ir: AdeuIR,
    patch_ops: list[JsonPatchOp],
    *,
    allowed_prefixes: tuple[str, ...] = DEFAULT_ALLOWED_PREFIXES,
    max_ops: int = 50,
    max_bytes: int = 20_000,
) -> AdeuIR:
    """
    Applies a sandboxed subset of JSON Patch to an ADEU IR.

    Fail-closed semantics: if any op is invalid or would produce an invalid IR,
    no output is returned.
    """
    if len(patch_ops) > max_ops:
        raise _err(f"patch too large: {len(patch_ops)} ops (max {max_ops})")

    size_bytes = _encode_patch_size_bytes(patch_ops)
    if size_bytes > max_bytes:
        raise _err(f"patch too large: {size_bytes} bytes (max {max_bytes})")

    # Work on a copy so we can fail closed.
    doc = copy.deepcopy(ir.model_dump(mode="json", by_alias=True))

    for op in patch_ops:
        if op.op in ("move", "copy"):
            raise _err(f"op {op.op!r} is not allowed", json_path=op.path)

        if not _allowed_path(op.path, allowed_prefixes=allowed_prefixes):
            raise _err("path is not allowed by sandbox", json_path=op.path)

        if op.op in ("add", "replace", "test") and op.value is None:
            raise _err(f"op {op.op!r} requires value", json_path=op.path)

        if op.op in ("remove", "replace", "test"):
            # Existence check
            _get_value(doc, op.path)

        if op.op == "test":
            cur = _get_value(doc, op.path)
            if cur != op.value:
                raise _err("test op failed (value mismatch)", json_path=op.path)
            continue

        parent, last = _resolve_parent(doc, op.path)

        if op.op == "add":
            if isinstance(parent, dict):
                parent[last] = op.value
                continue
            if isinstance(parent, list):
                if last == "-":
                    parent.append(op.value)
                    continue
                try:
                    idx = int(last)
                except ValueError as e:
                    raise _err("list segment must be an int index or '-'", json_path=op.path) from e
                if idx < 0 or idx > len(parent):
                    raise _err("list index out of range for add", json_path=op.path)
                parent.insert(idx, op.value)
                continue
            raise _err("add parent is not a container", json_path=op.path)

        if op.op == "replace":
            if isinstance(parent, dict):
                if last not in parent:
                    raise _err("replace target does not exist", json_path=op.path)
                parent[last] = op.value
                continue
            if isinstance(parent, list):
                try:
                    idx = int(last)
                except ValueError as e:
                    raise _err("list segment must be an int index", json_path=op.path) from e
                if idx < 0 or idx >= len(parent):
                    raise _err("list index out of range", json_path=op.path)
                parent[idx] = op.value
                continue
            raise _err("replace parent is not a container", json_path=op.path)

        if op.op == "remove":
            if isinstance(parent, dict):
                if last not in parent:
                    raise _err("remove target does not exist", json_path=op.path)
                del parent[last]
                continue
            if isinstance(parent, list):
                try:
                    idx = int(last)
                except ValueError as e:
                    raise _err("list segment must be an int index", json_path=op.path) from e
                if idx < 0 or idx >= len(parent):
                    raise _err("list index out of range", json_path=op.path)
                parent.pop(idx)
                continue
            raise _err("remove parent is not a container", json_path=op.path)

        raise _err(f"unsupported op: {op.op!r}", json_path=op.path)

    try:
        return AdeuIR.model_validate(doc)
    except ValidationError as e:
        raise _err(f"patched IR did not validate: {e}") from e


def apply_ambiguity_option_patch(ir: AdeuIR, *, option: AmbiguityOption) -> AdeuIR:
    if option.variant_ir_id is not None:
        raise _err("variant_ir_id options must be applied by loading that variant", json_path=None)
    if not option.patch:
        raise _err("patch option must include at least one op", json_path=None)
    return apply_json_patch(ir, option.patch)
