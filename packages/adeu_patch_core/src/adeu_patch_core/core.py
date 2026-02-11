from __future__ import annotations

import copy
import json
from collections.abc import Iterable
from dataclasses import dataclass
from typing import Any, Literal

from adeu_ir.models import JsonPatchOp

PatchValuePolicy = Literal["explicit_member", "non_null", "none"]


@dataclass(frozen=True)
class PatchCoreError:
    op_index: int
    path: str
    code: str
    message: str


@dataclass(frozen=True)
class PatchCoreValidationError(Exception):
    errors: tuple[PatchCoreError, ...]


def _issue(*, op_index: int, path: str, code: str, message: str) -> PatchCoreError:
    return PatchCoreError(op_index=op_index, path=path, code=code, message=message)


def _sorted_errors(errors: list[PatchCoreError]) -> tuple[PatchCoreError, ...]:
    return tuple(sorted(errors, key=lambda err: (err.op_index, err.path, err.code)))


def _raise_issue(*, op_index: int, path: str, code: str, message: str) -> None:
    error = _issue(op_index=op_index, path=path, code=code, message=message)
    raise PatchCoreValidationError(errors=(error,))


def encode_patch_size_bytes(patch_ops: Iterable[JsonPatchOp]) -> int:
    payload = [
        op.model_dump(mode="json", by_alias=True, exclude_none=True) for op in patch_ops
    ]
    return len(json.dumps(payload, separators=(",", ":"), sort_keys=True).encode("utf-8"))


def is_allowed_path(path: str, *, allowed_prefixes: tuple[str, ...]) -> bool:
    for prefix in allowed_prefixes:
        if path == prefix or path.startswith(prefix + "/"):
            return True
    return False


def _has_value(op: JsonPatchOp, *, value_policy: PatchValuePolicy) -> bool:
    if value_policy == "none":
        return True
    if value_policy == "non_null":
        return op.value is not None
    return "value" in op.model_fields_set


def parse_pointer(
    path: str,
    *,
    op_index: int,
    path_invalid_code: str = "PATCH_PATH_INVALID",
) -> list[str]:
    if not path.startswith("/"):
        _raise_issue(
            op_index=op_index,
            path=path,
            code=path_invalid_code,
            message="json pointer path must start with '/'",
        )
    parts = path.split("/")[1:]
    return [part.replace("~1", "/").replace("~0", "~") for part in parts]


def resolve_parent(
    doc: Any,
    path: str,
    *,
    op_index: int,
    path_invalid_code: str = "PATCH_PATH_INVALID",
    target_missing_code: str = "PATCH_TARGET_MISSING",
) -> tuple[Any, str]:
    parts = parse_pointer(path, op_index=op_index, path_invalid_code=path_invalid_code)
    if not parts:
        _raise_issue(
            op_index=op_index,
            path=path,
            code=path_invalid_code,
            message="patching the document root is not allowed",
        )

    cur: Any = doc
    for seg in parts[:-1]:
        if isinstance(cur, dict):
            if seg not in cur:
                _raise_issue(
                    op_index=op_index,
                    path=path,
                    code=target_missing_code,
                    message="path does not exist",
                )
            cur = cur[seg]
            continue

        if isinstance(cur, list):
            try:
                idx = int(seg)
            except ValueError as exc:
                _raise_issue(
                    op_index=op_index,
                    path=path,
                    code=path_invalid_code,
                    message="list segment must be an int index",
                )
                raise AssertionError("unreachable") from exc
            if idx < 0 or idx >= len(cur):
                _raise_issue(
                    op_index=op_index,
                    path=path,
                    code=target_missing_code,
                    message="list index out of range",
                )
            cur = cur[idx]
            continue

        _raise_issue(
            op_index=op_index,
            path=path,
            code=path_invalid_code,
            message="path traversal hit a non-container",
        )

    return cur, parts[-1]


def get_value(
    doc: Any,
    path: str,
    *,
    op_index: int,
    path_invalid_code: str = "PATCH_PATH_INVALID",
    target_missing_code: str = "PATCH_TARGET_MISSING",
) -> Any:
    parts = parse_pointer(path, op_index=op_index, path_invalid_code=path_invalid_code)
    cur: Any = doc
    for seg in parts:
        if isinstance(cur, dict):
            if seg not in cur:
                _raise_issue(
                    op_index=op_index,
                    path=path,
                    code=target_missing_code,
                    message="path does not exist",
                )
            cur = cur[seg]
            continue

        if isinstance(cur, list):
            try:
                idx = int(seg)
            except ValueError as exc:
                _raise_issue(
                    op_index=op_index,
                    path=path,
                    code=path_invalid_code,
                    message="list segment must be an int index",
                )
                raise AssertionError("unreachable") from exc
            if idx < 0 or idx >= len(cur):
                _raise_issue(
                    op_index=op_index,
                    path=path,
                    code=target_missing_code,
                    message="list index out of range",
                )
            cur = cur[idx]
            continue

        _raise_issue(
            op_index=op_index,
            path=path,
            code=path_invalid_code,
            message="path traversal hit a non-container",
        )
    return cur


def _add_at_path(
    doc: Any,
    path: str,
    value: Any,
    *,
    op_index: int,
    path_invalid_code: str,
    target_missing_code: str,
) -> None:
    parent, last = resolve_parent(
        doc,
        path,
        op_index=op_index,
        path_invalid_code=path_invalid_code,
        target_missing_code=target_missing_code,
    )

    if isinstance(parent, dict):
        parent[last] = value
        return
    if isinstance(parent, list):
        if last == "-":
            parent.append(value)
            return
        try:
            idx = int(last)
        except ValueError as exc:
            _raise_issue(
                op_index=op_index,
                path=path,
                code=path_invalid_code,
                message="list segment must be an int index or '-'",
            )
            raise AssertionError("unreachable") from exc
        if idx < 0 or idx > len(parent):
            _raise_issue(
                op_index=op_index,
                path=path,
                code=target_missing_code,
                message="list index out of range for add",
            )
        parent.insert(idx, value)
        return
    _raise_issue(
        op_index=op_index,
        path=path,
        code=path_invalid_code,
        message="add parent is not a container",
    )


def _replace_at_path(
    doc: Any,
    path: str,
    value: Any,
    *,
    op_index: int,
    path_invalid_code: str,
    target_missing_code: str,
) -> None:
    parent, last = resolve_parent(
        doc,
        path,
        op_index=op_index,
        path_invalid_code=path_invalid_code,
        target_missing_code=target_missing_code,
    )

    if isinstance(parent, dict):
        if last not in parent:
            _raise_issue(
                op_index=op_index,
                path=path,
                code=target_missing_code,
                message="replace target does not exist",
            )
        parent[last] = value
        return
    if isinstance(parent, list):
        try:
            idx = int(last)
        except ValueError as exc:
            _raise_issue(
                op_index=op_index,
                path=path,
                code=path_invalid_code,
                message="list segment must be an int index",
            )
            raise AssertionError("unreachable") from exc
        if idx < 0 or idx >= len(parent):
            _raise_issue(
                op_index=op_index,
                path=path,
                code=target_missing_code,
                message="list index out of range",
            )
        parent[idx] = value
        return
    _raise_issue(
        op_index=op_index,
        path=path,
        code=path_invalid_code,
        message="replace parent is not a container",
    )


def _remove_at_path(
    doc: Any,
    path: str,
    *,
    op_index: int,
    path_invalid_code: str,
    target_missing_code: str,
) -> Any:
    parent, last = resolve_parent(
        doc,
        path,
        op_index=op_index,
        path_invalid_code=path_invalid_code,
        target_missing_code=target_missing_code,
    )

    if isinstance(parent, dict):
        if last not in parent:
            _raise_issue(
                op_index=op_index,
                path=path,
                code=target_missing_code,
                message="remove target does not exist",
            )
        return parent.pop(last)
    if isinstance(parent, list):
        try:
            idx = int(last)
        except ValueError as exc:
            _raise_issue(
                op_index=op_index,
                path=path,
                code=path_invalid_code,
                message="list segment must be an int index",
            )
            raise AssertionError("unreachable") from exc
        if idx < 0 or idx >= len(parent):
            _raise_issue(
                op_index=op_index,
                path=path,
                code=target_missing_code,
                message="list index out of range",
            )
        return parent.pop(idx)
    _raise_issue(
        op_index=op_index,
        path=path,
        code=path_invalid_code,
        message="remove parent is not a container",
    )


def apply_patch_ops(
    doc: Any,
    patch_ops: list[JsonPatchOp],
    *,
    allowed_prefixes: tuple[str, ...] | None = None,
    disallowed_ops: frozenset[str] = frozenset(),
    value_policy: PatchValuePolicy = "explicit_member",
    collect_errors: bool = False,
    op_unsupported_code: str = "PATCH_OP_UNSUPPORTED",
    path_not_allowed_code: str = "PATCH_PATH_NOT_ALLOWED",
    value_required_code: str = "PATCH_VALUE_REQUIRED",
    path_invalid_code: str = "PATCH_PATH_INVALID",
    target_missing_code: str = "PATCH_TARGET_MISSING",
    test_failed_code: str = "PATCH_TEST_FAILED",
    from_required_code: str = "PATCH_FROM_REQUIRED",
) -> None:
    errors: list[PatchCoreError] = []

    def _report(error: PatchCoreError) -> None:
        if collect_errors:
            errors.append(error)
            return
        raise PatchCoreValidationError(errors=(error,))

    for op_index, op in enumerate(patch_ops):
        if op.op in disallowed_ops:
            _report(
                _issue(
                    op_index=op_index,
                    path=op.path,
                    code=op_unsupported_code,
                    message=f"op {op.op!r} is not allowed",
                )
            )
            continue

        if allowed_prefixes is not None and not is_allowed_path(
            op.path, allowed_prefixes=allowed_prefixes
        ):
            _report(
                _issue(
                    op_index=op_index,
                    path=op.path,
                    code=path_not_allowed_code,
                    message="path is not allowed by sandbox",
                )
            )
            continue

        if op.op in ("add", "replace", "test") and not _has_value(op, value_policy=value_policy):
            _report(
                _issue(
                    op_index=op_index,
                    path=op.path,
                    code=value_required_code,
                    message=f"op {op.op!r} requires value",
                )
            )
            continue

        if op.op in ("move", "copy"):
            from_path = op.from_path
            if from_path is None:
                _report(
                    _issue(
                        op_index=op_index,
                        path=op.path,
                        code=from_required_code,
                        message=f"op {op.op!r} requires from path",
                    )
                )
                continue
            if allowed_prefixes is not None and not is_allowed_path(
                from_path, allowed_prefixes=allowed_prefixes
            ):
                _report(
                    _issue(
                        op_index=op_index,
                        path=from_path,
                        code=path_not_allowed_code,
                        message="path is not allowed by sandbox",
                    )
                )
                continue

        try:
            if op.op in ("remove", "replace", "test"):
                get_value(
                    doc,
                    op.path,
                    op_index=op_index,
                    path_invalid_code=path_invalid_code,
                    target_missing_code=target_missing_code,
                )

            if op.op == "test":
                cur = get_value(
                    doc,
                    op.path,
                    op_index=op_index,
                    path_invalid_code=path_invalid_code,
                    target_missing_code=target_missing_code,
                )
                if cur != op.value:
                    _report(
                        _issue(
                            op_index=op_index,
                            path=op.path,
                            code=test_failed_code,
                            message="test op failed (value mismatch)",
                        )
                    )
                continue

            if op.op == "add":
                _add_at_path(
                    doc,
                    op.path,
                    op.value,
                    op_index=op_index,
                    path_invalid_code=path_invalid_code,
                    target_missing_code=target_missing_code,
                )
                continue

            if op.op == "replace":
                _replace_at_path(
                    doc,
                    op.path,
                    op.value,
                    op_index=op_index,
                    path_invalid_code=path_invalid_code,
                    target_missing_code=target_missing_code,
                )
                continue

            if op.op == "remove":
                _remove_at_path(
                    doc,
                    op.path,
                    op_index=op_index,
                    path_invalid_code=path_invalid_code,
                    target_missing_code=target_missing_code,
                )
                continue

            if op.op == "copy":
                copied = copy.deepcopy(
                    get_value(
                        doc,
                        op.from_path or "",
                        op_index=op_index,
                        path_invalid_code=path_invalid_code,
                        target_missing_code=target_missing_code,
                    )
                )
                _add_at_path(
                    doc,
                    op.path,
                    copied,
                    op_index=op_index,
                    path_invalid_code=path_invalid_code,
                    target_missing_code=target_missing_code,
                )
                continue

            if op.op == "move":
                moved = _remove_at_path(
                    doc,
                    op.from_path or "",
                    op_index=op_index,
                    path_invalid_code=path_invalid_code,
                    target_missing_code=target_missing_code,
                )
                _add_at_path(
                    doc,
                    op.path,
                    moved,
                    op_index=op_index,
                    path_invalid_code=path_invalid_code,
                    target_missing_code=target_missing_code,
                )
                continue

            _report(
                _issue(
                    op_index=op_index,
                    path=op.path,
                    code=op_unsupported_code,
                    message=f"unsupported op: {op.op!r}",
                )
            )
        except PatchCoreValidationError as exc:
            if collect_errors:
                errors.extend(exc.errors)
                continue
            raise

    if errors:
        raise PatchCoreValidationError(errors=_sorted_errors(errors))
