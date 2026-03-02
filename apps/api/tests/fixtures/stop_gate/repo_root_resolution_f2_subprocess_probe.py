from __future__ import annotations

import importlib.util
import json
import os
import sys
import warnings
from pathlib import Path
from types import ModuleType

import urm_runtime.stop_gate_registry as stop_gate_registry_module
from adeu_ir.repo import repo_root as canonical_repo_root
from path_helpers import repo_root as path_helpers_repo_root


def _load_module_from_file(path: Path, module_name: str) -> ModuleType:
    spec = importlib.util.spec_from_file_location(module_name, path)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def main() -> int:
    repo_root = Path(os.environ["F2_REPO_ROOT"]).resolve()
    check_s9_module = _load_module_from_file(
        repo_root / "apps" / "api" / "scripts" / "check_s9_triggers.py",
        "f2_subprocess_check_s9_script",
    )
    tests_check_s9_module = _load_module_from_file(
        repo_root / "apps" / "api" / "tests" / "test_check_s9_triggers.py",
        "f2_subprocess_test_check_s9",
    )
    tests_canonical_module = _load_module_from_file(
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

    if stop_gate_registry_root is None:
        raise RuntimeError("stop_gate_registry resolver returned no root")

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
        "tests_path_helpers": path_helpers_repo_root(),
    }
    normalized = {
        key: resolved[key].resolve().relative_to(repo_root).as_posix()
        for key in sorted(resolved)
    }
    sys.stdout.write(json.dumps(normalized, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
