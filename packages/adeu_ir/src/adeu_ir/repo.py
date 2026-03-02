from __future__ import annotations

import os
from pathlib import Path

_REPO_ROOT_ERROR_PREFIX = "repo_root resolution failed"
_ENV_VAR_NAME = "ADEU_REPO_ROOT"
_REQUIRED_STRUCTURAL_MARKERS: tuple[str, str] = ("pyproject.toml", "packages/urm_runtime")


def _fail(message: str) -> RuntimeError:
    return RuntimeError(f"{_REPO_ROOT_ERROR_PREFIX}: {message}")


def _resolve_strict(path: Path, *, label: str) -> Path:
    try:
        return path.expanduser().resolve(strict=True)
    except FileNotFoundError as exc:
        raise _fail(f"{label} does not exist: {path}") from exc


def _has_required_structural_markers(candidate: Path) -> bool:
    pyproject = candidate / _REQUIRED_STRUCTURAL_MARKERS[0]
    runtime_pkg = candidate / _REQUIRED_STRUCTURAL_MARKERS[1]
    return pyproject.is_file() and runtime_pkg.is_dir()


def _has_git_marker(candidate: Path) -> bool:
    marker = candidate / ".git"
    return marker.is_dir() or marker.is_file()


def _resolve_env_root(raw_value: str) -> Path:
    env_path = Path(raw_value).expanduser()
    if not env_path.is_absolute():
        raise _fail(f"{_ENV_VAR_NAME} must be absolute: {raw_value!r}")

    resolved = _resolve_strict(env_path, label=_ENV_VAR_NAME)
    if not _has_required_structural_markers(resolved):
        raise _fail(
            f"{_ENV_VAR_NAME} missing required markers "
            f"({_REQUIRED_STRUCTURAL_MARKERS[0]!r}, {_REQUIRED_STRUCTURAL_MARKERS[1]!r})"
        )
    return resolved


def _walk_root_candidates(start: Path) -> Path:
    candidates = (start, *start.parents)
    for candidate in candidates:
        if _has_required_structural_markers(candidate):
            return candidate
    for candidate in candidates:
        if _has_git_marker(candidate):
            return candidate
    raise _fail(f"could not locate repository root from anchor {start}")


def repo_root(*, anchor: Path | None = None) -> Path:
    """Resolve repository root deterministically for dev/test workflows."""
    env_root = os.environ.get(_ENV_VAR_NAME)
    if env_root:
        return _resolve_env_root(env_root)

    if anchor is None:
        anchor = Path.cwd()
    start = _resolve_strict(Path(anchor), label="anchor")
    return _walk_root_candidates(start)

