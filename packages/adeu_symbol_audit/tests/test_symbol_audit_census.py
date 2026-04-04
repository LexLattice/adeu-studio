from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_repo_description.models import compute_symbol_id
from adeu_symbol_audit import (
    REFERENCE_ARCHITECTURE_IR_PILOT_SCOPE_SOURCE_FILES,
    build_reference_architecture_ir_scope_manifest,
    build_symbol_census,
)


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v50a" / name


def _read_json(name: str) -> dict[str, object]:
    return json.loads(_fixture_path(name).read_text(encoding="utf-8"))


def test_reference_architecture_ir_scope_manifest_matches_fixture() -> None:
    manifest = build_reference_architecture_ir_scope_manifest(repo_root=_repo_root())

    assert manifest.model_dump(mode="json", by_alias=True, exclude_none=True) == _read_json(
        "reference_symbol_audit_scope_manifest.json"
    )


def test_reference_symbol_census_matches_fixture() -> None:
    manifest = build_reference_architecture_ir_scope_manifest(repo_root=_repo_root())
    census = build_symbol_census(repo_root=_repo_root(), scope_manifest=manifest)

    assert census.model_dump(mode="json", by_alias=True, exclude_none=True) == _read_json(
        "reference_symbol_census.json"
    )


def test_local_function_is_captured_in_reference_census() -> None:
    manifest = build_reference_architecture_ir_scope_manifest(repo_root=_repo_root())
    census = build_symbol_census(repo_root=_repo_root(), scope_manifest=manifest)

    local_functions = [entry for entry in census.symbols if entry.symbol_kind == "local_function"]

    assert local_functions
    assert all(entry.parent_symbol_id is not None for entry in local_functions)


def test_shared_kinds_match_released_symbol_id_law_in_built_census() -> None:
    manifest = build_reference_architecture_ir_scope_manifest(repo_root=_repo_root())
    census = build_symbol_census(repo_root=_repo_root(), scope_manifest=manifest)

    shared_entries = [
        entry for entry in census.symbols if entry.symbol_kind in {"class", "function", "method"}
    ]
    assert shared_entries
    for entry in shared_entries:
        assert entry.symbol_id == compute_symbol_id(
            module_path=entry.module_path,
            qualname=entry.qualname,
            symbol_kind=entry.symbol_kind,
        )


def test_build_symbol_census_rejects_manifest_hash_drift(tmp_path: Path) -> None:
    repo_root = _repo_root()
    for repo_rel_path in REFERENCE_ARCHITECTURE_IR_PILOT_SCOPE_SOURCE_FILES:
        destination = tmp_path / repo_rel_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(repo_root / repo_rel_path, destination)

    manifest = build_reference_architecture_ir_scope_manifest(repo_root=tmp_path)
    drifted_path = tmp_path / REFERENCE_ARCHITECTURE_IR_PILOT_SCOPE_SOURCE_FILES[0]
    drifted_path.write_text(
        drifted_path.read_text(encoding="utf-8") + "\n# drifted after manifest\n",
        encoding="utf-8",
    )

    with pytest.raises(ValueError, match="scope_manifest source file hash"):
        build_symbol_census(repo_root=tmp_path, scope_manifest=manifest)
