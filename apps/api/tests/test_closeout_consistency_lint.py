from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").is_dir():
            return parent
    raise FileNotFoundError("repository root not found")


def _script_path() -> Path:
    return _repo_root() / "apps" / "api" / "scripts" / "lint_closeout_consistency.py"


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


def _run_lint(*, repo_root: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(_script_path()), "--repo-root", str(repo_root)],
        check=False,
        capture_output=True,
        text=True,
        env=_pythonpath_env(),
    )


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )


def _write_metrics(
    *,
    path: Path,
    metric_keys: list[str],
    quality_baseline: str,
    quality_current: str,
) -> None:
    _write_json(
        path,
        {
            "schema": "stop_gate_metrics@1",
            "metrics": {key: 100.0 for key in metric_keys},
            "inputs": {
                "quality_baseline_path": quality_baseline,
                "quality_current_path": quality_current,
            },
        },
    )


def _assertion_block(*, baseline_metrics_path: str, current_metrics_path: str) -> str:
    payload = {
        "schema": "metric_key_continuity_assertion@1",
        "baseline_metrics_path": baseline_metrics_path,
        "current_metrics_path": current_metrics_path,
        "expected_relation": "exact_keyset_equality",
    }
    return (
        "## Metric-Key Continuity Assertion\n\n```json\n"
        + json.dumps(payload, sort_keys=True, indent=2)
        + "\n```\n"
    )


def _write_doc(path: Path, *, include_block: bool, block_text: str = "") -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    text = "# Closeout\n\n"
    if include_block:
        text += block_text
    path.write_text(text, encoding="utf-8")


def _make_repo_fixture(tmp_path: Path) -> Path:
    root = tmp_path / "repo"
    docs = root / "docs"
    stop_gate = root / "artifacts" / "stop_gate"

    _write_metrics(
        path=stop_gate / "metrics_v28_closeout.json",
        metric_keys=["a", "b"],
        quality_baseline="artifacts/quality_dashboard_v27_closeout.json",
        quality_current="artifacts/quality_dashboard_v28_closeout.json",
    )
    _write_metrics(
        path=stop_gate / "metrics_v29_closeout.json",
        metric_keys=["a", "b"],
        quality_baseline="artifacts/quality_dashboard_v28_closeout.json",
        quality_current="artifacts/quality_dashboard_v29_closeout.json",
    )
    _write_metrics(
        path=stop_gate / "metrics_v30_closeout.json",
        metric_keys=["a", "b"],
        quality_baseline="artifacts/quality_dashboard_v29_closeout.json",
        quality_current="artifacts/quality_dashboard_v30_closeout.json",
    )

    _write_doc(
        docs / "DRAFT_STOP_GATE_DECISION_vNEXT_PLUS29.md",
        include_block=True,
        block_text=_assertion_block(
            baseline_metrics_path="artifacts/stop_gate/metrics_v28_closeout.json",
            current_metrics_path="artifacts/stop_gate/metrics_v29_closeout.json",
        ),
    )
    _write_doc(
        docs / "DRAFT_STOP_GATE_DECISION_vNEXT_PLUS30.md",
        include_block=True,
        block_text=_assertion_block(
            baseline_metrics_path="artifacts/stop_gate/metrics_v29_closeout.json",
            current_metrics_path="artifacts/stop_gate/metrics_v30_closeout.json",
        ),
    )

    return root


def test_lint_passes_for_valid_required_docs(tmp_path: Path) -> None:
    repo_root = _make_repo_fixture(tmp_path)
    completed = _run_lint(repo_root=repo_root)
    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert completed.stderr == ""
    payload = json.loads(completed.stdout)
    assert payload["schema"] == "closeout_consistency_lint@1"
    assert payload["checked_docs"] == [
        "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS29.md",
        "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS30.md",
    ]
    assert payload["failures"] == []


def test_lint_required_doc_missing_block_fails_closed(tmp_path: Path) -> None:
    repo_root = _make_repo_fixture(tmp_path)
    _write_doc(
        repo_root / "docs" / "DRAFT_STOP_GATE_DECISION_vNEXT_PLUS30.md",
        include_block=False,
    )
    completed = _run_lint(repo_root=repo_root)
    assert completed.returncode == 1
    payload = json.loads(completed.stdout)
    assert payload["checked_docs"] == [
        "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS29.md",
        "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS30.md",
    ]
    failure_codes = [(row["doc_path"], row["code"]) for row in payload["failures"]]
    assert ("docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS30.md", "MISSING_BLOCK") in failure_codes


def test_lint_additional_doc_with_keyset_mismatch_fails_closed(tmp_path: Path) -> None:
    repo_root = _make_repo_fixture(tmp_path)
    _write_metrics(
        path=repo_root / "artifacts" / "stop_gate" / "metrics_v31_closeout.json",
        metric_keys=["a", "c"],
        quality_baseline="artifacts/quality_dashboard_v30_closeout.json",
        quality_current="artifacts/quality_dashboard_v31_closeout.json",
    )
    _write_doc(
        repo_root / "docs" / "DRAFT_STOP_GATE_DECISION_vNEXT_PLUS31.md",
        include_block=True,
        block_text=_assertion_block(
            baseline_metrics_path="artifacts/stop_gate/metrics_v30_closeout.json",
            current_metrics_path="artifacts/stop_gate/metrics_v31_closeout.json",
        ),
    )
    completed = _run_lint(repo_root=repo_root)
    assert completed.returncode == 1
    payload = json.loads(completed.stdout)
    assert "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS31.md" in payload["checked_docs"]
    failure_codes = [(row["doc_path"], row["code"]) for row in payload["failures"]]
    assert ("docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS31.md", "KEYSET_MISMATCH") in failure_codes


def test_lint_rejects_backslash_paths(tmp_path: Path) -> None:
    repo_root = _make_repo_fixture(tmp_path)
    _write_doc(
        repo_root / "docs" / "DRAFT_STOP_GATE_DECISION_vNEXT_PLUS29.md",
        include_block=True,
        block_text=_assertion_block(
            baseline_metrics_path="artifacts\\stop_gate\\metrics_v28_closeout.json",
            current_metrics_path="artifacts/stop_gate/metrics_v29_closeout.json",
        ),
    )
    completed = _run_lint(repo_root=repo_root)
    assert completed.returncode == 1
    payload = json.loads(completed.stdout)
    failure_codes = [(row["doc_path"], row["code"]) for row in payload["failures"]]
    assert ("docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS29.md", "PATH_INVALID") in failure_codes


def test_lint_enforces_required_provenance_mapping(tmp_path: Path) -> None:
    repo_root = _make_repo_fixture(tmp_path)
    _write_metrics(
        path=repo_root / "artifacts" / "stop_gate" / "metrics_v30_closeout.json",
        metric_keys=["a", "b"],
        quality_baseline="artifacts/quality_dashboard_v28_closeout.json",
        quality_current="artifacts/quality_dashboard_v30_closeout.json",
    )
    completed = _run_lint(repo_root=repo_root)
    assert completed.returncode == 1
    payload = json.loads(completed.stdout)
    failure_codes = [(row["doc_path"], row["code"]) for row in payload["failures"]]
    assert ("docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS30.md", "PROVENANCE_MISMATCH") in failure_codes


def test_lint_additional_doc_with_invalid_block_is_checked_and_fails(tmp_path: Path) -> None:
    repo_root = _make_repo_fixture(tmp_path)
    invalid_block = (
        "## Metric-Key Continuity Assertion\n\n"
        "```json\n"
        "{\"schema\": \"metric_key_continuity_assertion@1\"}\n"
        "```\n"
    )
    _write_doc(
        repo_root / "docs" / "DRAFT_STOP_GATE_DECISION_vNEXT_PLUS31.md",
        include_block=True,
        block_text=invalid_block,
    )
    completed = _run_lint(repo_root=repo_root)
    assert completed.returncode == 1
    payload = json.loads(completed.stdout)
    assert "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS31.md" in payload["checked_docs"]
    failure_codes = [(row["doc_path"], row["code"]) for row in payload["failures"]]
    assert (
        "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS31.md",
        "BLOCK_SCHEMA_INVALID",
    ) in failure_codes
