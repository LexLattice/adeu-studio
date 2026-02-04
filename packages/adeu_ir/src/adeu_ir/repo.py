from __future__ import annotations

import os
from functools import lru_cache
from pathlib import Path


@lru_cache(maxsize=1)
def repo_root(*, anchor: Path | None = None) -> Path:
    """
    Best-effort repo root resolver for dev/test workflows.

    - Prefers ADEU_REPO_ROOT if set.
    - Otherwise walks upward looking for `.git/` or a `pyproject.toml` + `packages/` marker.
    """
    env_root = os.environ.get("ADEU_REPO_ROOT")
    if env_root:
        return Path(env_root).expanduser().resolve()

    if anchor is None:
        anchor = Path.cwd()

    start = anchor.resolve()
    for candidate in (start, *start.parents):
        if (candidate / ".git").is_dir():
            return candidate
        if (candidate / "pyproject.toml").is_file() and (candidate / "packages").is_dir():
            return candidate

    raise RuntimeError("Could not locate repo root (set ADEU_REPO_ROOT).")

