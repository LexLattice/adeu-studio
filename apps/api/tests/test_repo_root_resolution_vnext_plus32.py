from __future__ import annotations

from pathlib import Path

import pytest
from adeu_ir.repo import repo_root


def _touch(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("", encoding="utf-8")


def test_repo_root_prefers_structural_markers_over_git_marker(tmp_path: Path) -> None:
    root = tmp_path / "workspace"
    _touch(root / "pyproject.toml")
    (root / "packages" / "urm_runtime").mkdir(parents=True, exist_ok=True)

    nested_git_parent = root / "submodule"
    (nested_git_parent / ".git").mkdir(parents=True, exist_ok=True)
    anchor = nested_git_parent / "apps" / "api" / "tests" / "dummy.py"
    _touch(anchor)

    assert repo_root(anchor=anchor) == root


def test_repo_root_supports_git_file_fallback(tmp_path: Path) -> None:
    root = tmp_path / "workspace"
    _touch(root / ".git")
    anchor = root / "a" / "b" / "script.py"
    _touch(anchor)

    assert repo_root(anchor=anchor) == root


def test_repo_root_rejects_relative_env_override(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _touch(tmp_path / "anchor.py")
    monkeypatch.setenv("ADEU_REPO_ROOT", ".")

    with pytest.raises(RuntimeError, match="ADEU_REPO_ROOT must be absolute"):
        repo_root(anchor=tmp_path / "anchor.py")


def test_repo_root_rejects_env_override_missing_required_markers(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    env_root = tmp_path / "env_root"
    env_root.mkdir(parents=True)
    _touch(tmp_path / "anchor.py")
    monkeypatch.setenv("ADEU_REPO_ROOT", str(env_root))

    with pytest.raises(RuntimeError, match="ADEU_REPO_ROOT missing required markers"):
        repo_root(anchor=tmp_path / "anchor.py")


def test_repo_root_requires_existing_anchor(tmp_path: Path) -> None:
    missing_anchor = tmp_path / "missing" / "anchor.py"
    with pytest.raises(RuntimeError, match="anchor does not exist"):
        repo_root(anchor=missing_anchor)
