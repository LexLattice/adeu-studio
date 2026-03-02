from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path
from types import ModuleType

from adeu_ir.repo import repo_root as canonical_repo_root
from urm_runtime.hashing import canonical_json

REQUIRED_KEYS = [
    "provider_route_contract_parity_pct",
    "codex_candidate_contract_valid_pct",
    "provider_parity_replay_determinism_pct",
]


def _repo_root() -> Path:
    return canonical_repo_root(anchor=Path(__file__).resolve())


def _script_path() -> Path:
    return _repo_root() / "apps" / "api" / "scripts" / "check_s9_triggers.py"


def _default_metrics_path() -> Path:
    return _repo_root() / "artifacts" / "stop_gate" / "metrics_v25_closeout.json"


def _pythonpath_env() -> dict[str, str]:
    repo_root = _repo_root()
    existing = os.environ.get("PYTHONPATH")
    paths = [
        str(repo_root / "apps" / "api" / "src"),
        str(repo_root / "packages" / "adeu_ir" / "src"),
        str(repo_root / "packages" / "urm_runtime" / "src"),
    ]
    if existing:
        paths.append(existing)
    env = os.environ.copy()
    env["PYTHONPATH"] = os.pathsep.join(paths)
    return env


def _run_script(*args: str, cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(_script_path()), *args],
        check=False,
        capture_output=True,
        text=True,
        cwd=str(cwd) if cwd is not None else None,
        env=_pythonpath_env(),
    )


def _assert_stdout_schema(payload: dict[str, object]) -> None:
    assert sorted(payload.keys()) == sorted(
        ["schema", "metrics_path", "threshold", "required_keys", "missing", "below", "pass"]
    )
    assert payload["schema"] == "s9_trigger_check@1"
    assert payload["required_keys"] == REQUIRED_KEYS


def _write_metrics_payload(path: Path, *, metrics: dict[str, object]) -> None:
    payload = {"schema": "stop_gate_metrics@1", "metrics": metrics}
    path.write_text(canonical_json(payload) + "\n", encoding="utf-8")


def _load_script_module() -> ModuleType:
    script_file = _script_path()
    spec = importlib.util.spec_from_file_location("check_s9_triggers_script_module", script_file)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_check_s9_triggers_pass_case_with_default_path() -> None:
    completed = _run_script()
    assert completed.returncode == 0, completed.stderr
    assert completed.stderr == ""

    payload = json.loads(completed.stdout)
    _assert_stdout_schema(payload)
    assert payload["metrics_path"] == "artifacts/stop_gate/metrics_v25_closeout.json"
    assert payload["threshold"] == 100.0
    assert payload["missing"] == []
    assert payload["below"] == []
    assert payload["pass"] is True


def test_check_s9_triggers_cross_cwd_default_path_resolution_is_deterministic() -> None:
    root_run = _run_script(cwd=_repo_root())
    nested_run = _run_script(cwd=_repo_root() / "apps" / "api")

    assert root_run.returncode == 0, root_run.stderr
    assert nested_run.returncode == 0, nested_run.stderr
    assert json.loads(root_run.stdout) == json.loads(nested_run.stdout)


def test_check_s9_triggers_missing_default_path_fails_closed(
    tmp_path: Path, monkeypatch, capsys
) -> None:
    module = _load_script_module()
    missing_metrics_path = tmp_path / "missing_metrics.json"
    monkeypatch.setattr(module, "_default_metrics_path", lambda _root: missing_metrics_path)

    exit_code = module.main([])
    assert exit_code == 1
    captured = capsys.readouterr()

    stdout_payload = json.loads(captured.out)
    stderr_payload = json.loads(captured.err)
    _assert_stdout_schema(stdout_payload)
    assert stdout_payload["pass"] is False
    assert stderr_payload["code"] == "S9_TRIGGER_METRICS_PATH_MISSING"


def test_check_s9_triggers_missing_required_key_fails_closed(tmp_path: Path) -> None:
    metrics_path = tmp_path / "missing_key_metrics.json"
    _write_metrics_payload(
        metrics_path,
        metrics={
            "provider_route_contract_parity_pct": 100.0,
            "provider_parity_replay_determinism_pct": 100.0,
        },
    )

    completed = _run_script("--metrics-path", str(metrics_path))
    assert completed.returncode == 1

    stdout_payload = json.loads(completed.stdout)
    stderr_payload = json.loads(completed.stderr)
    _assert_stdout_schema(stdout_payload)
    assert stdout_payload["missing"] == ["codex_candidate_contract_valid_pct"]
    assert stdout_payload["below"] == []
    assert stdout_payload["pass"] is False
    assert stderr_payload["code"] == "S9_TRIGGER_REQUIRED_METRIC_MISSING"


def test_check_s9_triggers_below_threshold_fails_closed(tmp_path: Path) -> None:
    metrics_path = tmp_path / "below_threshold_metrics.json"
    _write_metrics_payload(
        metrics_path,
        metrics={
            "provider_route_contract_parity_pct": 99.0,
            "codex_candidate_contract_valid_pct": 100.0,
            "provider_parity_replay_determinism_pct": 100.0,
        },
    )

    completed = _run_script("--metrics-path", str(metrics_path))
    assert completed.returncode == 1

    stdout_payload = json.loads(completed.stdout)
    stderr_payload = json.loads(completed.stderr)
    _assert_stdout_schema(stdout_payload)
    assert stdout_payload["missing"] == []
    assert stdout_payload["below"] == [{"key": "provider_route_contract_parity_pct", "value": 99.0}]
    assert stdout_payload["pass"] is False
    assert stderr_payload["code"] == "S9_TRIGGER_REQUIRED_THRESHOLD_FAILED"


def test_check_s9_triggers_malformed_payload_fails_closed(tmp_path: Path) -> None:
    metrics_path = tmp_path / "malformed_metrics.json"
    metrics_path.write_text("{", encoding="utf-8")

    completed = _run_script("--metrics-path", str(metrics_path))
    assert completed.returncode == 1

    stdout_payload = json.loads(completed.stdout)
    stderr_payload = json.loads(completed.stderr)
    _assert_stdout_schema(stdout_payload)
    assert stdout_payload["pass"] is False
    assert stderr_payload["code"] == "S9_TRIGGER_PAYLOAD_PARSE_ERROR"


def test_check_s9_triggers_success_and_failure_stdout_keyset() -> None:
    success_completed = _run_script()
    assert success_completed.returncode == 0
    _assert_stdout_schema(json.loads(success_completed.stdout))

    missing_path = _default_metrics_path().with_suffix(".missing")
    failure_completed = _run_script("--metrics-path", str(missing_path))
    assert failure_completed.returncode == 1
    _assert_stdout_schema(json.loads(failure_completed.stdout))
