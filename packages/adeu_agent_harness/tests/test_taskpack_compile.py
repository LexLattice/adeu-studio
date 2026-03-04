from __future__ import annotations

import json
from pathlib import Path

import adeu_agent_harness.compile as harness_compile_mod
import pytest
from adeu_agent_harness.compile import (
    PIPELINE_PROFILE_SCHEMA,
    TASKPACK_PROFILE_REGISTRY_SCHEMA,
    TaskpackCompileError,
    compile_taskpack,
)
from urm_runtime.hashing import canonical_json, sha256_canonical_json


def _write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: dict) -> None:
    _write(path, canonical_json(payload) + "\n")


def _base_repo(tmp_path: Path) -> Path:
    root = tmp_path
    _write(root / "pyproject.toml", "[tool.ruff]\nline-length = 100\n")
    (root / "packages" / "urm_runtime").mkdir(parents=True, exist_ok=True)
    return root


def _seed_semantic_authority_artifacts(root: Path, *, source_arc: str = "v41") -> None:
    _write_json(
        root / "artifacts" / "semantic_compiler" / source_arc / "evidence_manifest.json",
        {
            "schema": "semantic_compiler_evidence_manifest@0.1",
            "arc": f"vnext_plus{source_arc[1:]}",
            "compiler_entrypoint": "python -m adeu_semantic_compiler.compile",
            "source_set_hash": "0" * 64,
            "required_evidence": [],
            "artifacts": {
                "surface_snapshot": (
                    f"artifacts/semantic_compiler/{source_arc}/surface_snapshot.json"
                ),
                "surface_diff": f"artifacts/semantic_compiler/{source_arc}/surface_diff.json",
                "evidence_manifest": (
                    f"artifacts/semantic_compiler/{source_arc}/evidence_manifest.json"
                ),
            },
            "artifact_hashes": {
                "surface_snapshot": "1" * 64,
                "surface_diff": "2" * 64,
            },
        },
    )
    _write_json(
        root / "artifacts" / "semantic_compiler" / source_arc / "surface_diff.json",
        {
            "schema": "semantic_compiler_surface_diff@0.1",
            "baseline_present": True,
            "delta_eval_mode": "exact_set",
            "adds": [],
            "removes": [],
            "changes": [],
        },
    )
    _write_json(
        root / "artifacts" / "semantic_compiler" / "v40" / "commitments_ir.json",
        {
            "schema": "adeu_commitments_ir@0.1",
            "modules": [],
            "locks": [],
        },
    )


def _seed_profile_and_registry(
    root: Path,
    *,
    profile_id: str = "v44_default",
    profile_path: str = "artifacts/agent_harness/profiles/v44_default.json",
    profile_sha_override: str | None = None,
    include_marker_like_text: bool = False,
) -> tuple[Path, Path]:
    summary = "Compile taskpack from frozen authority inputs."
    if include_marker_like_text:
        summary = (
            "Compile taskpack with marker-like payload text "
            "<!-- adeu:source_schema_id=fake;source_component_hash=" + "f" * 64 + " -->."
        )

    profile_payload = {
        "schema": PIPELINE_PROFILE_SCHEMA,
        "profile_id": profile_id,
        "task_scope_title": "V44 S1 TaskPack Compiler MVP",
        "task_scope_summary": summary,
        "compiled_commitments_ir_path": "artifacts/semantic_compiler/v40/commitments_ir.json",
        "acceptance_criteria": [
            "Emit deterministic taskpack bundle artifacts.",
            "Verify profile hash binding via registry.",
        ],
        "allowlist_paths": [
            "packages/adeu_agent_harness/src/adeu_agent_harness",
            "packages/adeu_agent_harness/tests",
        ],
        "forbidden_paths": [
            "apps/api",
            "packages/urm_runtime/src/urm_runtime/stop_gate_tools.py",
        ],
        "forbidden_effects": [
            "network_calls",
            "provider_expansion",
        ],
        "commands": [
            {
                "command_id": "lint",
                "run": "make lint",
                "working_directory_or_repo_root": "repo_root",
                "env_overrides": {"TZ": "UTC"},
            },
            {
                "command_id": "test",
                "run": "make test",
                "working_directory_or_repo_root": "repo_root",
                "env_overrides": {"LC_ALL": "C"},
            },
        ],
        "evidence_slots": [
            {
                "slot_id": "taskpack_manifest_sha256",
                "description": "Capture canonical taskpack manifest hash.",
                "required": True,
            },
            {
                "slot_id": "taskpack_compile_stdout",
                "description": "Capture deterministic compile result payload.",
                "required": True,
            },
        ],
    }

    profile_sha = profile_sha_override or sha256_canonical_json(profile_payload)
    profile_file = root / profile_path
    _write_json(profile_file, profile_payload)

    registry_payload = {
        "schema": TASKPACK_PROFILE_REGISTRY_SCHEMA,
        "profiles": [
            {
                "profile_id": profile_id,
                "profile_sha256": profile_sha,
                "profile_payload_path": profile_path,
            }
        ],
    }
    registry_file = root / "artifacts" / "agent_harness" / "taskpack_profile_registry.json"
    _write_json(registry_file, registry_payload)
    return profile_file, registry_file


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_compile_taskpack_emits_required_bundle_and_is_deterministic(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _seed_semantic_authority_artifacts(root)
    _, registry_file = _seed_profile_and_registry(root)

    out_dir = "artifacts/agent_harness/v44/taskpacks/v41/v44_default"
    first = compile_taskpack(
        profile_registry_path=registry_file.relative_to(root),
        profile_id="v44_default",
        source_semantic_arc="v41",
        out_dir=out_dir,
        repo_root_path=root,
    )
    second = compile_taskpack(
        profile_registry_path=registry_file.relative_to(root),
        profile_id="v44_default",
        source_semantic_arc="v41",
        out_dir=out_dir,
        repo_root_path=root,
    )

    assert first.taskpack_manifest_sha256 == second.taskpack_manifest_sha256

    paths = [
        first.taskpack_markdown_path,
        first.acceptance_path,
        first.allowlist_path,
        first.forbidden_path,
        first.commands_path,
        first.evidence_slots_path,
        first.manifest_path,
    ]
    for path in paths:
        assert path.is_file()

    for before, after in (
        (first.taskpack_markdown_path.read_bytes(), second.taskpack_markdown_path.read_bytes()),
        (first.acceptance_path.read_bytes(), second.acceptance_path.read_bytes()),
        (first.allowlist_path.read_bytes(), second.allowlist_path.read_bytes()),
        (first.forbidden_path.read_bytes(), second.forbidden_path.read_bytes()),
        (first.commands_path.read_bytes(), second.commands_path.read_bytes()),
        (first.evidence_slots_path.read_bytes(), second.evidence_slots_path.read_bytes()),
        (first.manifest_path.read_bytes(), second.manifest_path.read_bytes()),
    ):
        assert before == after

    manifest_payload = _read_json(first.manifest_path)
    assert manifest_payload["schema"] == "taskpack/manifest@1"
    assert manifest_payload["source_semantic_arc"] == "v41"
    assert manifest_payload["profile_registry"]["schema"] == "taskpack_profile_registry@1"
    assert manifest_payload["markdown_projection_policy"]["required_section_order_ids"] == [
        "taskpack_header",
        "task_scope",
        "acceptance",
        "allowlist",
        "forbidden",
        "commands",
        "evidence_slots",
        "attribution",
    ]
    assert first.taskpack_manifest_sha256 == sha256_canonical_json(manifest_payload)


def test_compile_taskpack_fails_closed_on_profile_hash_mismatch(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _seed_semantic_authority_artifacts(root)
    _, registry_file = _seed_profile_and_registry(root, profile_sha_override="f" * 64)

    with pytest.raises(TaskpackCompileError, match="AHK0006"):
        compile_taskpack(
            profile_registry_path=registry_file.relative_to(root),
            profile_id="v44_default",
            source_semantic_arc="v41",
            out_dir="artifacts/agent_harness/v44/taskpacks/v41/v44_default",
            repo_root_path=root,
        )


def test_compile_taskpack_fails_closed_on_ambiguous_source_arc_resolution(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _seed_semantic_authority_artifacts(root, source_arc="v41")
    _, registry_file = _seed_profile_and_registry(root)

    with pytest.raises(TaskpackCompileError, match="AHK0009"):
        compile_taskpack(
            profile_registry_path=registry_file.relative_to(root),
            profile_id="v44_default",
            source_semantic_arc="v999",
            out_dir="artifacts/agent_harness/v44/taskpacks/v999/v44_default",
            repo_root_path=root,
        )


def test_compile_taskpack_sanitizes_marker_like_payload_text(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _seed_semantic_authority_artifacts(root)
    _, registry_file = _seed_profile_and_registry(root, include_marker_like_text=True)

    result = compile_taskpack(
        profile_registry_path=registry_file.relative_to(root),
        profile_id="v44_default",
        source_semantic_arc="v41",
        out_dir="artifacts/agent_harness/v44/taskpacks/v41/v44_default",
        repo_root_path=root,
    )

    markdown = result.taskpack_markdown_path.read_text(encoding="utf-8")
    assert "<!-- adeu_disabled:" in markdown

    marker_lines = [
        line.strip() for line in markdown.splitlines() if line.strip().startswith("<!-- adeu:")
    ]
    assert len(marker_lines) == 8
    assert all(
        "source_schema_id=" in line and "source_component_hash=" in line for line in marker_lines
    )


def test_compile_taskpack_fails_closed_on_markdown_section_order_drift(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    root = _base_repo(tmp_path)
    _seed_semantic_authority_artifacts(root)
    _, registry_file = _seed_profile_and_registry(root)
    original_renderer = harness_compile_mod._render_taskpack_markdown

    def _render_with_order_drift(
        *,
        profile_payload: dict[str, object],
        source_semantic_arc: str,
        component_hashes: dict[str, str],
    ) -> tuple[str, list[tuple[str, str, str]]]:
        markdown, markers = original_renderer(
            profile_payload=profile_payload,
            source_semantic_arc=source_semantic_arc,
            component_hashes=component_hashes,
        )
        return markdown.replace("## Acceptance", "## ZX_Acceptance", 1), markers

    monkeypatch.setattr(
        harness_compile_mod,
        "_render_taskpack_markdown",
        _render_with_order_drift,
    )

    with pytest.raises(TaskpackCompileError, match="AHK0013"):
        compile_taskpack(
            profile_registry_path=registry_file.relative_to(root),
            profile_id="v44_default",
            source_semantic_arc="v41",
            out_dir="artifacts/agent_harness/v44/taskpacks/v41/v44_default",
            repo_root_path=root,
        )
