from __future__ import annotations

import os
import subprocess
from pathlib import Path

import pytest
from adeu_ir import ProofInput
from adeu_lean import (
    DEFAULT_SEMANTICS_VERSION,
    OBLIGATION_KINDS,
    build_obligation_requests,
    build_proof_mapping_id,
    run_lean_request,
)
from adeu_lean import runner as runner_module


def _seed_project_root(project_root: Path) -> None:
    project_root.mkdir(parents=True, exist_ok=True)
    (project_root / "pyproject.toml").write_text(
        "[project]\nname='adeu-lean-test'\n",
        encoding="utf-8",
    )
    (project_root / "AdeuCore").mkdir(parents=True, exist_ok=True)
    (project_root / "src" / "adeu_lean").mkdir(parents=True, exist_ok=True)


def test_build_obligation_requests_is_deterministic() -> None:
    inputs = [ProofInput(object_id="dn1", json_path="/D_norm/statements/0", formula_hash="f1")]
    left = build_obligation_requests(theorem_prefix="ir_abc", inputs=inputs)
    right = build_obligation_requests(theorem_prefix="ir_abc", inputs=inputs)

    assert [request.theorem_id for request in left] == [request.theorem_id for request in right]
    assert [request.obligation_kind for request in left] == list(OBLIGATION_KINDS)
    assert left[0].semantics_version == DEFAULT_SEMANTICS_VERSION
    assert [request.theorem_src for request in left] == [request.theorem_src for request in right]
    assert all("inputs_hash" in request.metadata for request in left)
    assert all("theorem_src_hash" in request.metadata for request in left)


def test_build_obligation_requests_uses_frozen_theorem_mappings() -> None:
    requests = build_obligation_requests(theorem_prefix="ir_map", inputs=[])
    expected_core_theorems = {
        "pred_closed_world": "AdeuCore.pred_closed_world_missing_false",
        "exception_gating": "AdeuCore.exception_gating_false_not_defeat",
        "conflict_soundness": "AdeuCore.conflict_soundness",
    }
    for request in requests:
        assert request.obligation_kind in expected_core_theorems
        assert expected_core_theorems[str(request.obligation_kind)] in request.theorem_src


def test_build_proof_mapping_id_is_deterministic() -> None:
    first = build_proof_mapping_id(
        theorem_id="ir_map_pred_closed_world",
        obligation_kind="pred_closed_world",
        inputs_hash="a" * 64,
        proof_semantics_version=DEFAULT_SEMANTICS_VERSION,
        theorem_src_hash="b" * 64,
    )
    second = build_proof_mapping_id(
        theorem_id="ir_map_pred_closed_world",
        obligation_kind="pred_closed_world",
        inputs_hash="a" * 64,
        proof_semantics_version=DEFAULT_SEMANTICS_VERSION,
        theorem_src_hash="b" * 64,
    )
    changed = build_proof_mapping_id(
        theorem_id="ir_map_pred_closed_world",
        obligation_kind="pred_closed_world",
        inputs_hash="a" * 64,
        proof_semantics_version=DEFAULT_SEMANTICS_VERSION,
        theorem_src_hash="c" * 64,
    )
    assert first == second
    assert len(first) == 64
    assert first != changed


def test_run_lean_request_missing_binary_returns_failed() -> None:
    request = build_obligation_requests(theorem_prefix="ir_missing", inputs=[])[0]
    result = run_lean_request(
        request,
        timeout_ms=1000,
        lake_bin="/tmp/lake-not-installed",
        lean_bin="/tmp/lean-not-installed",
        project_root=Path(__file__).resolve().parents[1],
    )
    assert result.status == "failed"
    assert "binary not found" in str(result.details.get("error", "")).lower()
    assert len(result.proof_hash) == 64


def test_run_lean_request_hash_is_stable_across_project_roots(monkeypatch, tmp_path: Path) -> None:
    request = build_obligation_requests(theorem_prefix="ir_stable", inputs=[])[0]
    monkeypatch.setattr(runner_module, "_lean_version", lambda **_: None)

    def fake_run_command(
        *,
        cmd: list[str],
        cwd: Path,
        timeout_s: float,
    ) -> subprocess.CompletedProcess[str]:
        del timeout_s
        source_abs = (cwd / cmd[-1]).resolve().as_posix()
        return subprocess.CompletedProcess(
            args=cmd,
            returncode=0,
            stdout=f"\x1b[31mproof\x1b[0m {source_abs}",
            stderr=f"{source_abs}:1: warning",
        )

    monkeypatch.setattr(runner_module, "_run_command", fake_run_command)

    project_root_a = tmp_path / "root_a"
    project_root_b = tmp_path / "root_b"
    _seed_project_root(project_root_a)
    _seed_project_root(project_root_b)
    result_a = run_lean_request(
        request,
        timeout_ms=1000,
        lake_bin="lake",
        lean_bin="lean",
        project_root=project_root_a,
    )
    result_b = run_lean_request(
        request,
        timeout_ms=1000,
        lake_bin="lake",
        lean_bin="lean",
        project_root=project_root_b,
    )

    assert result_a.status == "proved"
    assert result_b.status == "proved"
    assert result_a.proof_hash == result_b.proof_hash
    assert result_a.details["command"][-1] == "<LEAN_SOURCE>"
    assert "<LEAN_SOURCE>" in str(result_a.details.get("stdout", ""))
    assert str(project_root_a.resolve()) not in str(result_a.details.get("stdout", ""))
    assert "\x1b[" not in str(result_a.details.get("stdout", ""))
    assert not list((project_root_a / ".adeu_lean_tmp").rglob("*.lean"))
    assert not list((project_root_b / ".adeu_lean_tmp").rglob("*.lean"))


def test_run_lean_request_overlap_is_fail_closed(monkeypatch, tmp_path: Path) -> None:
    request = build_obligation_requests(theorem_prefix="ir_overlap", inputs=[])[0]
    project_root = tmp_path / "project"
    _seed_project_root(project_root)
    project_dir = project_root.resolve()
    _, workspace_dir, source_path, _ = runner_module._workspace_paths(
        project_dir=project_dir,
        request=request,
    )
    workspace_dir.mkdir(parents=True, exist_ok=False)
    source_path.write_text(request.theorem_src, encoding="utf-8")

    def should_not_run(**kwargs):  # type: ignore[no-untyped-def]
        raise AssertionError(f"runner executed unexpectedly: {kwargs.get('cmd')}")

    monkeypatch.setattr(runner_module, "_run_command", should_not_run)
    result = run_lean_request(
        request,
        timeout_ms=1000,
        lake_bin="lake",
        lean_bin="lean",
        project_root=project_root,
    )
    assert result.status == "failed"
    assert result.details.get("reason") == "DETERMINISTIC_PATH_OVERLAP"


def test_run_lean_request_collision_is_fail_closed(monkeypatch, tmp_path: Path) -> None:
    request = build_obligation_requests(theorem_prefix="ir_collision", inputs=[])[0]
    project_root = tmp_path / "project"
    _seed_project_root(project_root)
    project_dir = project_root.resolve()
    _, workspace_dir, source_path, _ = runner_module._workspace_paths(
        project_dir=project_dir,
        request=request,
    )
    workspace_dir.mkdir(parents=True, exist_ok=False)
    source_path.write_text("theorem bad : True := by exact False.elim ?h", encoding="utf-8")

    def should_not_run(**kwargs):  # type: ignore[no-untyped-def]
        raise AssertionError(f"runner executed unexpectedly: {kwargs.get('cmd')}")

    monkeypatch.setattr(runner_module, "_run_command", should_not_run)
    result = run_lean_request(
        request,
        timeout_ms=1000,
        lake_bin="lake",
        lean_bin="lean",
        project_root=project_root,
    )
    assert result.status == "failed"
    assert result.details.get("reason") == "DETERMINISTIC_PATH_COLLISION"


@pytest.mark.parametrize(
    ("side_effect", "error_fragment"),
    [
        (subprocess.TimeoutExpired(cmd="lean", timeout=1.0), "timeout"),
        (FileNotFoundError("missing binary"), "binary not found"),
    ],
)
def test_run_lean_request_cleans_up_workspace_on_failures(
    monkeypatch,
    tmp_path: Path,
    side_effect: Exception,
    error_fragment: str,
) -> None:
    request = build_obligation_requests(theorem_prefix="ir_cleanup", inputs=[])[0]
    project_root = tmp_path / "project"
    _seed_project_root(project_root)
    temp_root = project_root / ".adeu_lean_tmp"

    def fake_run_command(**kwargs):  # type: ignore[no-untyped-def]
        raise side_effect

    monkeypatch.setattr(runner_module, "_run_command", fake_run_command)
    monkeypatch.setattr(runner_module, "_lean_version", lambda **_: None)
    result = run_lean_request(
        request,
        timeout_ms=1000,
        lake_bin="lake",
        lean_bin="lean",
        project_root=project_root,
    )
    assert result.status == "failed"
    assert error_fragment in str(result.details.get("error", "")).lower()
    assert not list(temp_root.rglob("*.lean"))


def test_run_lean_request_rejects_unresolvable_project_root(tmp_path: Path) -> None:
    request = build_obligation_requests(theorem_prefix="ir_bad_root", inputs=[])[0]
    with pytest.raises(RuntimeError, match="unable to resolve adeu_lean project root"):
        run_lean_request(
            request,
            timeout_ms=1000,
            lake_bin="/tmp/lake-not-installed",
            lean_bin="/tmp/lean-not-installed",
            project_root=tmp_path / "missing_sentinels",
        )


@pytest.mark.skipif(
    not (os.environ.get("ADEU_LEAN_BIN") or os.environ.get("LEAN_BIN")),
    reason="ADEU_LEAN_BIN/LEAN_BIN not set; skipping Lean smoke test",
)
def test_run_lean_request_smoke_with_env_binary() -> None:
    lean_bin = (os.environ.get("ADEU_LEAN_BIN") or os.environ.get("LEAN_BIN") or "").strip()
    request = build_obligation_requests(theorem_prefix="ir_smoke", inputs=[])[0]
    result = run_lean_request(
        request,
        timeout_ms=3000,
        lake_bin="/tmp/lake-not-installed",
        lean_bin=lean_bin,
        project_root=Path(__file__).resolve().parents[1],
    )
    assert result.status in {"proved", "failed"}
    assert len(result.proof_hash) == 64
