from __future__ import annotations

from pathlib import PurePosixPath

from adeu_ir import stable_id

_SUPPORTED_MODULE_KINDS = frozenset({"arc_lock", "slice_spec", "stop_gate"})


def _normalize_text(value: str) -> str:
    return " ".join(value.split()).strip().lower()


def _normalize_rel_path(value: str) -> str:
    normalized = value.replace("\\", "/").strip()
    if not normalized:
        raise ValueError("path must not be empty")
    if normalized.startswith("/"):
        raise ValueError("path must be repository-relative")
    if ".." in PurePosixPath(normalized).parts:
        raise ValueError("path must not contain parent traversal")
    return str(PurePosixPath(normalized))


def stable_commitments_module_id(
    *,
    module_kind: str,
    source_path: str,
    title: str,
    prefix: str = "cir-mod",
) -> str:
    if module_kind not in _SUPPORTED_MODULE_KINDS:
        raise ValueError(f"unsupported module_kind: {module_kind}")
    return stable_id(
        module_kind,
        _normalize_rel_path(source_path),
        _normalize_text(title),
        prefix=prefix,
    )


def stable_commitments_lock_id(
    *,
    module_id: str,
    lock_kind: str,
    target: str,
    prefix: str = "cir-lock",
) -> str:
    normalized_module_id = _normalize_text(module_id)
    normalized_lock_kind = _normalize_text(lock_kind)
    normalized_target = _normalize_text(target)
    return stable_id(
        normalized_module_id,
        normalized_lock_kind,
        normalized_target,
        prefix=prefix,
    )


__all__ = [
    "stable_commitments_module_id",
    "stable_commitments_lock_id",
]
