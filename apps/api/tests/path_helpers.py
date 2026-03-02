from __future__ import annotations

from pathlib import Path

from adeu_ir.repo import repo_root as canonical_repo_root


def repo_root() -> Path:
    return canonical_repo_root(anchor=Path(__file__).resolve())
