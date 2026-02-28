from __future__ import annotations

import ast
import importlib.util
from pathlib import Path
from types import ModuleType

import pytest
import urm_runtime.stop_gate_tools as stop_gate_tools_module
from urm_runtime.stop_gate_registry import (
    ACTIVE_STOP_GATE_MANIFEST_VERSIONS,
    STOP_GATE_MANIFEST_RELATIVE_TEMPLATE,
    default_stop_gate_manifest_path,
)


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("repository root not found")


def _load_build_stop_gate_metrics_module() -> ModuleType:
    module_path = _repo_root() / "apps" / "api" / "scripts" / "build_stop_gate_metrics.py"
    spec = importlib.util.spec_from_file_location("build_stop_gate_metrics_for_tests", module_path)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _manifest_path_constant_versions_from_runtime() -> tuple[int, ...]:
    versions: list[int] = []
    for key in vars(stop_gate_tools_module):
        if not key.startswith("VNEXT_PLUS") or not key.endswith("_MANIFEST_PATH"):
            continue
        version_str = key.removeprefix("VNEXT_PLUS").removesuffix("_MANIFEST_PATH")
        versions.append(int(version_str))
    return tuple(sorted(versions))


def _int_sequence_literal(node: ast.AST) -> tuple[int, ...] | None:
    if not isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        return None
    values: list[int] = []
    for element in node.elts:
        if isinstance(element, ast.Constant) and isinstance(element.value, int):
            values.append(element.value)
            continue
        return None
    return tuple(values)


def _active_tuple_literal_occurrences_outside_registry() -> list[str]:
    repo_root = _repo_root()
    registry_path = (
        repo_root / "packages" / "urm_runtime" / "src" / "urm_runtime" / "stop_gate_registry.py"
    ).resolve()
    search_roots = (
        repo_root / "apps" / "api" / "scripts",
        repo_root / "apps" / "api" / "tests",
        repo_root / "packages" / "urm_runtime" / "src" / "urm_runtime",
    )
    occurrences: list[str] = []
    for root in search_roots:
        for path in sorted(root.rglob("*.py")):
            resolved_path = path.resolve()
            if resolved_path == registry_path:
                continue
            tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
            for node in ast.walk(tree):
                values = _int_sequence_literal(node)
                if values != ACTIVE_STOP_GATE_MANIFEST_VERSIONS:
                    continue
                relative_path = path.relative_to(repo_root)
                occurrences.append(f"{relative_path}:{getattr(node, 'lineno', 0)}")
    return sorted(occurrences)


def test_registry_active_version_set_matches_frozen_v27_baseline() -> None:
    expected_versions = tuple(
        int(value) for value in "7,8,9,10,11,13,14,15,16,17,18,19,20,21,22,23,24,25,26".split(",")
    )
    assert ACTIVE_STOP_GATE_MANIFEST_VERSIONS == expected_versions


def test_registry_default_paths_are_repo_root_anchored_and_byte_identical() -> None:
    repo_root = _repo_root()
    for version in ACTIVE_STOP_GATE_MANIFEST_VERSIONS:
        expected_path = repo_root / STOP_GATE_MANIFEST_RELATIVE_TEMPLATE.format(version=version)
        resolved_path = default_stop_gate_manifest_path(version)
        assert str(resolved_path) == str(expected_path)


def test_registry_consumers_share_active_version_ordering_and_defaults(tmp_path: Path) -> None:
    script_module = _load_build_stop_gate_metrics_module()
    parsed = script_module.parse_args([])
    script_versions = tuple(
        sorted(
            int(name.removeprefix("vnext_plus").removesuffix("_manifest"))
            for name in vars(parsed)
            if name.startswith("vnext_plus") and name.endswith("_manifest")
        )
    )
    assert script_versions == ACTIVE_STOP_GATE_MANIFEST_VERSIONS
    assert _manifest_path_constant_versions_from_runtime() == ACTIVE_STOP_GATE_MANIFEST_VERSIONS

    override_path = tmp_path / "override_vnext_plus7_manifest.json"
    override_args = script_module.parse_args(["--vnext-plus7-manifest", str(override_path)])
    assert override_args.vnext_plus7_manifest == override_path
    assert override_args.vnext_plus8_manifest == default_stop_gate_manifest_path(8)
    assert stop_gate_tools_module.VNEXT_PLUS7_MANIFEST_PATH == default_stop_gate_manifest_path(7)


def test_inactive_manifest_cli_flags_fail_closed_before_output(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    script_module = _load_build_stop_gate_metrics_module()
    out_json = tmp_path / "stop_gate_metrics.json"
    out_md = tmp_path / "stop_gate_metrics.md"
    exit_code = script_module.main(
        [
            "--vnext-plus12-manifest",
            str(tmp_path / "inactive_manifest.json"),
            "--out-json",
            str(out_json),
            "--out-md",
            str(out_md),
        ]
    )
    assert exit_code == 1
    captured = capsys.readouterr()
    assert captured.stdout == ""
    assert captured.err.strip() == (
        "inactive stop-gate manifest flags are unsupported: --vnext-plus12-manifest "
        "(active versions: 7,8,9,10,11,13,14,15,16,17,18,19,20,21,22,23,24,25,26)"
    )
    assert not out_json.exists()
    assert not out_md.exists()


def test_stop_gate_tools_cli_rejects_inactive_manifest_flags(
    capsys: pytest.CaptureFixture[str],
) -> None:
    exit_code = stop_gate_tools_module.main(
        ["--vnext-plus12-manifest", "fixtures/unused.json"]
    )
    assert exit_code == 1
    captured = capsys.readouterr()
    assert captured.stdout == ""
    assert captured.err.strip() == (
        "inactive stop-gate manifest flags are unsupported: --vnext-plus12-manifest "
        "(active versions: 7,8,9,10,11,13,14,15,16,17,18,19,20,21,22,23,24,25,26)"
    )


def test_no_duplicate_active_version_tuple_literals_outside_registry_module() -> None:
    duplicates = _active_tuple_literal_occurrences_outside_registry()
    assert not duplicates, "duplicate active-version tuple literal(s): " + ", ".join(duplicates)
