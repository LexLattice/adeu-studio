from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path
from types import ModuleType


def _repo_root() -> Path:
    current = Path(__file__).resolve()
    for parent in current.parents:
        if (parent / ".git").is_dir():
            return parent
    raise FileNotFoundError("repository root not found")


def _script_path() -> Path:
    return _repo_root() / "apps" / "api" / "scripts" / "lint_l2_boundary_readiness.py"


def _pythonpath_env() -> dict[str, str]:
    repo_root = _repo_root()
    env = os.environ.copy()
    existing = env.get("PYTHONPATH")
    paths = [
        str(repo_root / "apps" / "api" / "src"),
        str(repo_root / "packages" / "urm_runtime" / "src"),
    ]
    if existing:
        paths.append(existing)
    env["PYTHONPATH"] = os.pathsep.join(paths)
    env["TZ"] = "UTC"
    env["LC_ALL"] = "C"
    return env


def _default_base_ref() -> str:
    repo_root = _repo_root()
    for candidate in ("origin/main", "HEAD"):
        completed = subprocess.run(
            ["git", "rev-parse", "--verify", "--quiet", f"{candidate}^{{commit}}"],
            cwd=repo_root,
            check=False,
            capture_output=True,
            text=True,
        )
        if completed.returncode == 0:
            return candidate
    return "HEAD"


def _run_lint(
    *,
    lock_doc: Path | None = None,
    base_ref: str | None = None,
    sentinel_dir: Path | None = None,
) -> subprocess.CompletedProcess[str]:
    repo_root = _repo_root()
    lock_doc_path = lock_doc or repo_root / "docs" / "LOCKED_CONTINUATION_vNEXT_PLUS35.md"
    sentinel_dir_path = (
        sentinel_dir
        or repo_root / "apps" / "api" / "tests" / "fixtures" / "l2_boundary_sentinels"
    )
    base_ref_value = base_ref or _default_base_ref()
    return subprocess.run(
        [
            sys.executable,
            str(_script_path()),
            "--lock-doc",
            str(lock_doc_path),
            "--base-ref",
            base_ref_value,
            "--sentinel-dir",
            str(sentinel_dir_path),
        ],
        cwd=repo_root,
        check=False,
        capture_output=True,
        text=True,
        env=_pythonpath_env(),
    )


def _load_script_module() -> ModuleType:
    module_name = "lint_l2_boundary_readiness_for_tests"
    spec = importlib.util.spec_from_file_location(
        module_name,
        _script_path(),
    )
    if spec is None or spec.loader is None:
        raise RuntimeError("failed to load lint_l2_boundary_readiness module")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def _remove_v31_g_readiness_block(lock_text: str) -> str:
    marker = '"target": "V31-G"'
    marker_index = lock_text.find(marker)
    if marker_index < 0:
        raise RuntimeError("target V31-G block marker not found")
    block_start = lock_text.rfind("```json", 0, marker_index)
    block_end = lock_text.find("```", marker_index)
    if block_start < 0 or block_end < 0:
        raise RuntimeError("unable to isolate V31-G block")
    return lock_text[:block_start] + lock_text[block_end + 3 :]


def test_l2_boundary_readiness_lint_passes_on_current_repo() -> None:
    completed = _run_lint()
    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert completed.stderr == ""
    payload = json.loads(completed.stdout)
    assert payload["schema"] == "l2_boundary_readiness_lint@1"
    assert payload["failures"] == []


def test_l2_boundary_readiness_lint_fails_closed_when_base_ref_missing() -> None:
    completed = _run_lint(base_ref="origin/__missing_ref__")
    assert completed.returncode == 5
    payload = json.loads(completed.stdout)
    failure_codes = {row["code"] for row in payload["failures"]}
    assert "BASE_REF_UNAVAILABLE" in failure_codes


def test_l2_boundary_readiness_lint_fails_on_missing_v31_g_block(tmp_path: Path) -> None:
    repo_root = _repo_root()
    lock_doc = repo_root / "docs" / "LOCKED_CONTINUATION_vNEXT_PLUS35.md"
    modified = _remove_v31_g_readiness_block(lock_doc.read_text(encoding="utf-8"))
    lock_doc_copy = tmp_path / "LOCKED_CONTINUATION_vNEXT_PLUS35.invalid.md"
    lock_doc_copy.write_text(modified, encoding="utf-8")

    completed = _run_lint(lock_doc=lock_doc_copy)
    assert completed.returncode == 2
    payload = json.loads(completed.stdout)
    failure_codes = {row["code"] for row in payload["failures"]}
    assert "READINESS_BLOCK_COUNT_INVALID" in failure_codes


def test_l2_boundary_readiness_lint_fails_on_sentinel_drift(tmp_path: Path) -> None:
    repo_root = _repo_root()
    source_dir = repo_root / "apps" / "api" / "tests" / "fixtures" / "l2_boundary_sentinels"
    sentinel_dir = tmp_path / "l2_boundary_sentinels"
    sentinel_dir.mkdir(parents=True, exist_ok=True)

    for name in (
        "v35_worker_run_response_v34_baseline.json",
        "v35_worker_cancel_response_v34_baseline.json",
    ):
        payload = json.loads((source_dir / name).read_text(encoding="utf-8"))
        (sentinel_dir / name).write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    run_payload = json.loads(
        (sentinel_dir / "v35_worker_run_response_v34_baseline.json").read_text(encoding="utf-8")
    )
    run_payload["response"]["body"]["status"] = "failed"
    (sentinel_dir / "v35_worker_run_response_v34_baseline.json").write_text(
        json.dumps(run_payload, indent=2) + "\n",
        encoding="utf-8",
    )

    completed = _run_lint(sentinel_dir=sentinel_dir)
    assert completed.returncode == 4
    payload = json.loads(completed.stdout)
    failure_codes = {row["code"] for row in payload["failures"]}
    assert "SENTINEL_DRIFT" in failure_codes


def test_no_touch_violations_detect_frozen_runtime_paths() -> None:
    module = _load_script_module()
    changed_paths = {
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS35.md",
        "apps/api/src/adeu_api/main.py",
        "apps/api/scripts/lint_l2_boundary_readiness.py",
    }
    violations = module._no_touch_violations(changed_paths)
    assert violations == ["apps/api/src/adeu_api/main.py"]


def test_extract_json_blocks_keeps_unclosed_block_payload() -> None:
    module = _load_script_module()
    block_text = "```json\n{\"schema\": \"x\""
    blocks = module._extract_json_blocks(block_text)
    assert blocks == ['{"schema": "x"']
