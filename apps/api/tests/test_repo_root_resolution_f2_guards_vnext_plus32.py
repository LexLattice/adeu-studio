from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
import warnings
from pathlib import Path
from types import ModuleType
from unittest.mock import patch

import urm_runtime.stop_gate_registry as stop_gate_registry_module
from adeu_ir.repo import repo_root as canonical_repo_root
from path_helpers import repo_root as path_helpers_repo_root

_IN_SCOPE_RESOLVER_KEYS: tuple[str, ...] = tuple(
    sorted(
        (
            "canonical_helper",
            "check_s9_script",
            "stop_gate_registry",
            "tests_canonical_json_v27",
            "tests_check_s9",
            "tests_path_helpers",
        )
    )
)


def _repo_root() -> Path:
    return canonical_repo_root(anchor=Path(__file__).resolve())


def _normalize_relative_posix(path: Path, *, base: Path) -> str:
    return path.resolve().relative_to(base.resolve()).as_posix()


def _touch(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("", encoding="utf-8")


def _load_module_from_file(path: Path, module_name: str) -> ModuleType:
    spec = importlib.util.spec_from_file_location(module_name, path)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def _collect_in_scope_resolver_paths() -> dict[str, Path]:
    root = _repo_root()
    check_s9_module = _load_module_from_file(
        root / "apps" / "api" / "scripts" / "check_s9_triggers.py",
        "f2_check_s9_triggers_script",
    )
    tests_check_s9_module = _load_module_from_file(
        root / "apps" / "api" / "tests" / "test_check_s9_triggers.py",
        "f2_test_check_s9_triggers",
    )
    tests_canonical_module = _load_module_from_file(
        root / "apps" / "api" / "tests" / "test_canonical_json_conformance_vnext_plus27.py",
        "f2_test_canonical_json_conformance_vnext_plus27",
    )

    with warnings.catch_warnings():
        warnings.simplefilter("ignore", DeprecationWarning)
        stop_gate_registry_path = (
            root
            / "packages"
            / "urm_runtime"
            / "src"
            / "urm_runtime"
            / "stop_gate_registry.py"
        )
        stop_gate_registry_root = stop_gate_registry_module.discover_repo_root(
            stop_gate_registry_path
        )

    assert stop_gate_registry_root is not None
    return {
        "canonical_helper": canonical_repo_root(anchor=Path(__file__).resolve()),
        "check_s9_script": check_s9_module._repo_root(),
        "stop_gate_registry": stop_gate_registry_root,
        "tests_canonical_json_v27": tests_canonical_module._repo_root(),
        "tests_check_s9": tests_check_s9_module._repo_root(),
        "tests_path_helpers": path_helpers_repo_root(),
    }


def _build_normalized_in_scope_report() -> dict[str, str]:
    base = _repo_root()
    resolved = _collect_in_scope_resolver_paths()
    report = {
        key: _normalize_relative_posix(value, base=base)
        for key, value in sorted(resolved.items(), key=lambda item: item[0])
    }
    return report


def _subprocess_guard_report(*, cwd: Path) -> dict[str, str]:
    root = _repo_root()
    env = os.environ.copy()
    pythonpath_parts = [
        str(root / "apps" / "api" / "src"),
        str(root / "apps" / "api" / "tests"),
        str(root / "packages" / "adeu_ir" / "src"),
        str(root / "packages" / "urm_runtime" / "src"),
    ]
    existing_pythonpath = env.get("PYTHONPATH")
    if existing_pythonpath:
        pythonpath_parts.append(existing_pythonpath)
    env["PYTHONPATH"] = os.pathsep.join(pythonpath_parts)
    env["F2_REPO_ROOT"] = str(root)

    script = """
import importlib.util
import json
import os
import sys
import warnings
from pathlib import Path

from adeu_ir.repo import repo_root as canonical_repo_root
from path_helpers import repo_root as tests_path_helper_repo_root
import urm_runtime.stop_gate_registry as stop_gate_registry_module

repo_root = Path(os.environ["F2_REPO_ROOT"]).resolve()

def load_module(path: Path, module_name: str):
    spec = importlib.util.spec_from_file_location(module_name, path)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module

check_s9_module = load_module(
    repo_root / "apps" / "api" / "scripts" / "check_s9_triggers.py",
    "f2_subprocess_check_s9_script",
)
tests_check_s9_module = load_module(
    repo_root / "apps" / "api" / "tests" / "test_check_s9_triggers.py",
    "f2_subprocess_test_check_s9",
)
tests_canonical_module = load_module(
    repo_root / "apps" / "api" / "tests" / "test_canonical_json_conformance_vnext_plus27.py",
    "f2_subprocess_test_canonical",
)

with warnings.catch_warnings():
    warnings.simplefilter("ignore", DeprecationWarning)
    stop_gate_registry_root = stop_gate_registry_module.discover_repo_root(
        repo_root
        / "packages"
        / "urm_runtime"
        / "src"
        / "urm_runtime"
        / "stop_gate_registry.py"
    )

assert stop_gate_registry_root is not None
resolved = {
    "canonical_helper": canonical_repo_root(
        anchor=(
            repo_root
            / "apps"
            / "api"
            / "tests"
            / "test_repo_root_resolution_f2_guards_vnext_plus32.py"
        )
    ),
    "check_s9_script": check_s9_module._repo_root(),
    "stop_gate_registry": stop_gate_registry_root,
    "tests_canonical_json_v27": tests_canonical_module._repo_root(),
    "tests_check_s9": tests_check_s9_module._repo_root(),
    "tests_path_helpers": tests_path_helper_repo_root(),
}
normalized = {
    key: resolved[key].resolve().relative_to(repo_root).as_posix()
    for key in sorted(resolved)
}
print(json.dumps(normalized, sort_keys=True))
""".strip()
    completed = subprocess.run(
        [sys.executable, "-c", script],
        check=False,
        capture_output=True,
        text=True,
        cwd=str(cwd),
        env=env,
    )
    assert completed.returncode == 0, completed.stderr
    return json.loads(completed.stdout)


def test_f2_in_scope_callsite_report_is_sorted_and_posix_normalized() -> None:
    report = _build_normalized_in_scope_report()
    assert tuple(report.keys()) == _IN_SCOPE_RESOLVER_KEYS
    assert report == {key: report[key] for key in sorted(report)}
    assert set(report.values()) == {"."}
    assert all("\\" not in value for value in report.values())


def test_f2_in_scope_callsite_report_is_deterministic_across_reruns() -> None:
    first_report = _build_normalized_in_scope_report()
    second_report = _build_normalized_in_scope_report()
    assert second_report == first_report


def test_f2_cross_cwd_report_is_deterministic_via_subprocess() -> None:
    root = _repo_root()
    root_report = _subprocess_guard_report(cwd=root)
    nested_report = _subprocess_guard_report(cwd=root / "apps" / "api")
    assert nested_report == root_report


def test_f2_fixture_parity_matches_frozen_expected_outputs(
    tmp_path: Path, monkeypatch
) -> None:
    structural_root = tmp_path / "case_structural" / "repo"
    _touch(structural_root / "pyproject.toml")
    (structural_root / "packages" / "urm_runtime").mkdir(parents=True, exist_ok=True)
    structural_anchor = structural_root / "nested" / "unit" / "anchor.py"
    _touch(structural_anchor)

    git_root = tmp_path / "case_git" / "repo"
    _touch(git_root / ".git")
    git_anchor = git_root / "nested" / "anchor.py"
    _touch(git_anchor)

    env_root = tmp_path / "case_env" / "env_root"
    _touch(env_root / "pyproject.toml")
    (env_root / "packages" / "urm_runtime").mkdir(parents=True, exist_ok=True)
    env_anchor = tmp_path / "case_env" / "anchor.py"
    _touch(env_anchor)

    resolved = {
        "git_fallback": canonical_repo_root(anchor=git_anchor),
        "structural_marker_precedence": canonical_repo_root(anchor=structural_anchor),
    }
    monkeypatch.setenv("ADEU_REPO_ROOT", str(env_root))
    resolved["env_override"] = canonical_repo_root(anchor=env_anchor)

    normalized = {
        key: _normalize_relative_posix(value, base=tmp_path)
        for key, value in sorted(resolved.items(), key=lambda item: item[0])
    }
    expected = {
        "env_override": "case_env/env_root",
        "git_fallback": "case_git/repo",
        "structural_marker_precedence": "case_structural/repo",
    }
    assert normalized == expected


def test_f2_in_scope_resolver_flows_do_not_trigger_network_side_effects() -> None:
    with (
        patch("socket.socket", side_effect=AssertionError("socket call is out-of-scope")),
        patch(
            "socket.create_connection",
            side_effect=AssertionError("network connection is out-of-scope"),
        ),
        patch(
            "socket.getaddrinfo",
            side_effect=AssertionError("dns resolution is out-of-scope"),
        ),
    ):
        report = _build_normalized_in_scope_report()
    assert set(report.values()) == {"."}
