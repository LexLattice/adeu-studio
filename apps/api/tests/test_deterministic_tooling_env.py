from __future__ import annotations

import importlib.util
import os
import subprocess
import sys
from pathlib import Path
from types import ModuleType
from unittest.mock import patch

import pytest


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("repository root not found")


def _load_deterministic_env_module() -> ModuleType:
    module_path = (
        _repo_root() / "packages" / "urm_runtime" / "src" / "urm_runtime" / "deterministic_env.py"
    )
    spec = importlib.util.spec_from_file_location("deterministic_env_for_tests", module_path)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_DETERMINISTIC_ENV = _load_deterministic_env_module()
DeterministicToolingEnvError = _DETERMINISTIC_ENV.DeterministicToolingEnvError
ensure_deterministic_tooling_env = _DETERMINISTIC_ENV.ensure_deterministic_tooling_env
_SCRIPT_RUNTIME_DEPS_AVAILABLE = importlib.util.find_spec("pydantic") is not None


def _pythonpath_env() -> dict[str, str]:
    repo_root = _repo_root()
    existing = os.environ.get("PYTHONPATH")
    paths = [
        str(repo_root / "apps" / "api" / "src"),
        str(repo_root / "packages" / "urm_runtime" / "src"),
    ]
    if existing:
        paths.append(existing)
    env = os.environ.copy()
    env["PYTHONPATH"] = os.pathsep.join(paths)
    return env


def _run_script(
    *,
    script_path: Path,
    env_overrides: dict[str, str],
) -> subprocess.CompletedProcess[str]:
    env = _pythonpath_env()
    env.update(env_overrides)
    return subprocess.run(
        [sys.executable, str(script_path)],
        check=False,
        capture_output=True,
        text=True,
        env=env,
    )


def test_ensure_deterministic_tooling_env_sets_missing_values_and_calls_tzset() -> None:
    env: dict[str, str] = {}
    with patch.object(_DETERMINISTIC_ENV.time, "tzset", create=True) as tzset:
        ensure_deterministic_tooling_env(environ=env)

    assert env["TZ"] == "UTC"
    assert env["LC_ALL"] == "C"
    assert tzset.call_count == 1


def test_ensure_deterministic_tooling_env_accepts_correct_values_without_changing_lang() -> None:
    env = {"TZ": "UTC", "LC_ALL": "C", "LANG": "C.UTF-8"}
    with patch.object(_DETERMINISTIC_ENV.time, "tzset", create=True) as tzset:
        ensure_deterministic_tooling_env(environ=env)

    assert env["TZ"] == "UTC"
    assert env["LC_ALL"] == "C"
    assert env["LANG"] == "C.UTF-8"
    assert tzset.call_count == 0


def test_ensure_deterministic_tooling_env_normalizes_whitespace_and_calls_tzset() -> None:
    env = {"TZ": " UTC ", "LC_ALL": " C "}
    with patch.object(_DETERMINISTIC_ENV.time, "tzset", create=True) as tzset:
        ensure_deterministic_tooling_env(environ=env)

    assert env["TZ"] == "UTC"
    assert env["LC_ALL"] == "C"
    assert tzset.call_count == 1


def test_ensure_deterministic_tooling_env_rejects_conflicting_values() -> None:
    env = {"TZ": "Europe/Bucharest", "LC_ALL": "C"}
    with pytest.raises(DeterministicToolingEnvError) as excinfo:
        ensure_deterministic_tooling_env(environ=env)

    assert str(excinfo.value) == (
        "deterministic tooling env conflict: expected TZ=UTC, got Europe/Bucharest"
    )
    assert excinfo.value.key == "TZ"
    assert excinfo.value.expected == "UTC"
    assert excinfo.value.actual == "Europe/Bucharest"


def test_ensure_deterministic_tooling_env_rejects_empty_or_whitespace_values() -> None:
    env = {"TZ": "UTC", "LC_ALL": "   "}
    with pytest.raises(DeterministicToolingEnvError) as excinfo:
        ensure_deterministic_tooling_env(environ=env)

    assert (
        str(excinfo.value)
        == "deterministic tooling env conflict: expected LC_ALL=C, got <empty>"
    )
    assert excinfo.value.key == "LC_ALL"
    assert excinfo.value.expected == "C"
    assert excinfo.value.actual == ""


@pytest.mark.parametrize(
    "script_path",
    [
        Path("apps/api/scripts/build_stop_gate_metrics.py"),
        Path("apps/api/scripts/build_quality_dashboard.py"),
    ],
)
@pytest.mark.skipif(
    not _SCRIPT_RUNTIME_DEPS_AVAILABLE,
    reason="script runtime dependencies not available in local test environment",
)
def test_tooling_scripts_fail_closed_for_conflicting_env(script_path: Path) -> None:
    completed = _run_script(
        script_path=_repo_root() / script_path,
        env_overrides={
            "TZ": "UTC",
            "LC_ALL": "C.UTF-8",
        },
    )

    assert completed.returncode == 1
    assert completed.stdout == ""
    stderr_lines = [line for line in completed.stderr.strip().splitlines() if line.strip()]
    assert stderr_lines[-1] == "deterministic tooling env conflict: expected LC_ALL=C, got C.UTF-8"
