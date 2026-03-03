from __future__ import annotations

import json
from pathlib import Path

from adeu_semantic_compiler.compile import (
    SCC0002_INPUT_DIAGNOSTICS_FAIL_CLOSED,
    SCC0007_MODULE_ID_MISSING,
    SCC0014_PASS_HASH_IDENTITY_VIOLATION,
    compile_semantic_compiler,
)
from urm_runtime.hashing import canonical_json, sha256_canonical_json


def _write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _base_repo(tmp_path: Path) -> Path:
    root = tmp_path
    _write(root / "pyproject.toml", "[tool.ruff]\nline-length = 100\n")
    (root / "packages" / "urm_runtime").mkdir(parents=True, exist_ok=True)
    return root


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_semantic_source_artifacts(
    root: Path,
    *,
    files: list[dict],
    source_diagnostics: list[dict] | None = None,
) -> tuple[Path, Path]:
    source_path = (
        root / "artifacts" / "semantic_compiler" / "v39" / "semantic_source.normalized.json"
    )
    diagnostics_path = (
        root / "artifacts" / "semantic_compiler" / "v39" / "semantic_source.diagnostics.json"
    )

    normalized_files: list[dict] = []
    for file_item in files:
        frontmatter = file_item.get("frontmatter_semantic", {})
        blocks = file_item.get("blocks", [])
        semantic_hash_basis = {
            "frontmatter_semantic": frontmatter,
            "blocks": [
                {
                    "label": block.get("label"),
                    "payload": block.get("payload"),
                    "identifier": block.get("identifier"),
                }
                for block in blocks
            ],
        }
        normalized_files.append(
            {
                "path": file_item["path"],
                "frontmatter_semantic": frontmatter,
                "blocks": blocks,
                "semantic_hash": sha256_canonical_json(semantic_hash_basis),
            }
        )

    source_hash_basis = {
        "schema": "semantic_source_collection@0.1",
        "files": [
            {
                "path": item["path"],
                "semantic_hash": item["semantic_hash"],
            }
            for item in normalized_files
        ],
    }

    source_payload = {
        "schema": "semantic_source_collection@0.1",
        "compiler": {
            "name": "adeu_semantic_source",
            "version": "0.0.0",
            "export_call_pattern": "python -m adeu_semantic_source.compile",
        },
        "source_docs_root": "docs",
        "input_interface": {
            "mode": "cli_explicit_paths",
            "inputs": [item["path"] for item in normalized_files],
        },
        "files": normalized_files,
        "semantic_source_hash": sha256_canonical_json(source_hash_basis),
    }

    diagnostics_payload = {
        "schema": "semantic_source_diagnostics@0.1",
        "diagnostics": source_diagnostics or [],
    }

    _write(source_path, canonical_json(source_payload) + "\n")
    _write(diagnostics_path, canonical_json(diagnostics_payload) + "\n")
    return source_path, diagnostics_path


def test_compile_emits_ir_diagnostics_and_pass_manifest(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS40.md",
                "frontmatter_semantic": {"adeu_arc_id": "vnext_plus40"},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus40",
                            "arc_id": "vnext_plus40",
                            "title": "Locked Continuation vNext+40",
                            "effects_declared": ["contract_validation"],
                        },
                        "identifier": "arc:vnext_plus40",
                    },
                    {
                        "label": "adeu.slice_spec",
                        "payload": {
                            "module_id": "slice:vnext_plus40:o1",
                            "arc_id": "vnext_plus40",
                            "slice_id": "o1",
                            "title": "Compiler core pass pipeline MVP",
                            "depends_on": ["arc:vnext_plus40"],
                        },
                        "identifier": "slice:vnext_plus40:o1",
                    },
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is True
    assert result.commitments_ir_payload is not None

    ir_payload = _read_json(result.commitments_ir_output_path)
    diagnostics_payload = _read_json(result.diagnostics_output_path)
    pass_manifest_payload = _read_json(result.pass_manifest_output_path)
    surface_snapshot_payload = _read_json(result.surface_snapshot_output_path)
    surface_diff_payload = _read_json(result.surface_diff_output_path)
    evidence_manifest_payload = _read_json(result.evidence_manifest_output_path)
    pr_splits_markdown = result.pr_splits_output_path.read_text(encoding="utf-8")

    assert ir_payload["schema"] == "adeu_commitments_ir@0.1"
    assert [item["module_kind"] for item in ir_payload["modules"]] == [
        "arc_lock",
        "slice_spec",
    ]
    assert diagnostics_payload == {
        "schema": "semantic_compiler_diagnostics@0.1",
        "diagnostics": [],
    }
    assert pass_manifest_payload["schema"] == "semantic_compiler_pass_manifest@0.1"
    assert [entry["name"] for entry in pass_manifest_payload["pass_manifest"]] == [
        "LoadCollection",
        "ValidateBlocks",
        "RevalidateNormalization",
        "BuildIR",
        "ResolveRefs",
        "TypecheckLocks",
    ]

    by_name = {entry["name"]: entry for entry in pass_manifest_payload["pass_manifest"]}
    assert by_name["LoadCollection"]["input_sha256"] == by_name["LoadCollection"]["output_sha256"]
    assert by_name["BuildIR"]["input_sha256"] != by_name["BuildIR"]["output_sha256"]
    assert by_name["ResolveRefs"]["input_sha256"] != by_name["ResolveRefs"]["output_sha256"]
    assert surface_snapshot_payload["schema"] == "semantic_compiler_surface_snapshot@0.1"
    assert surface_snapshot_payload["surfaces"] == []
    assert surface_diff_payload == {
        "schema": "semantic_compiler_surface_diff@0.1",
        "baseline_present": False,
        "delta_eval_mode": "no_baseline",
        "adds": [],
        "removes": [],
        "changes": [],
    }
    assert evidence_manifest_payload["schema"] == "semantic_compiler_evidence_manifest@0.1"
    assert set(evidence_manifest_payload) == {
        "schema",
        "arc",
        "compiler_entrypoint",
        "source_set_hash",
        "required_evidence",
        "artifacts",
        "artifact_hashes",
    }
    assert "No changed surfaces." in pr_splits_markdown


def test_input_diagnostics_error_fails_closed(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS40.md",
                "frontmatter_semantic": {},
                "blocks": [],
            }
        ],
        source_diagnostics=[
            {
                "code": "SSC1234",
                "severity": "ERROR",
                "message": "source parse failed",
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS40.md",
                "start_line": 1,
                "start_column": 1,
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is False
    codes = {item["code"] for item in result.diagnostics_payload["diagnostics"]}
    assert SCC0002_INPUT_DIAGNOSTICS_FAIL_CLOSED in codes


def test_compile_rerun_is_byte_identical(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS40.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus40",
                            "arc_id": "vnext_plus40",
                            "title": "Locked Continuation vNext+40",
                        },
                        "identifier": "arc:vnext_plus40",
                    }
                ],
            }
        ],
    )

    first = compile_semantic_compiler(repo_root_path=root)
    ir_before = first.commitments_ir_output_path.read_bytes()
    diagnostics_before = first.diagnostics_output_path.read_bytes()
    pass_manifest_before = first.pass_manifest_output_path.read_bytes()
    surface_snapshot_before = first.surface_snapshot_output_path.read_bytes()
    surface_diff_before = first.surface_diff_output_path.read_bytes()
    evidence_manifest_before = first.evidence_manifest_output_path.read_bytes()
    pr_splits_before = first.pr_splits_output_path.read_bytes()

    second = compile_semantic_compiler(repo_root_path=root)
    ir_after = second.commitments_ir_output_path.read_bytes()
    diagnostics_after = second.diagnostics_output_path.read_bytes()
    pass_manifest_after = second.pass_manifest_output_path.read_bytes()
    surface_snapshot_after = second.surface_snapshot_output_path.read_bytes()
    surface_diff_after = second.surface_diff_output_path.read_bytes()
    evidence_manifest_after = second.evidence_manifest_output_path.read_bytes()
    pr_splits_after = second.pr_splits_output_path.read_bytes()

    assert first.success is True
    assert second.success is True
    assert ir_before == ir_after
    assert diagnostics_before == diagnostics_after
    assert pass_manifest_before == pass_manifest_after
    assert surface_snapshot_before == surface_snapshot_after
    assert surface_diff_before == surface_diff_after
    assert evidence_manifest_before == evidence_manifest_after
    assert pr_splits_before == pr_splits_after


def test_missing_module_id_fails_closed_with_empty_module_id_sort_value(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS40.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "arc_id": "vnext_plus40",
                            "title": "Missing module id",
                        },
                        "identifier": None,
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is False
    entries = [
        item
        for item in result.diagnostics_payload["diagnostics"]
        if item["code"] == SCC0007_MODULE_ID_MISSING
    ]
    assert len(entries) == 1
    assert entries[0]["module_id"] == ""
    assert entries[0]["start_line"] == 1


def test_mutating_passes_correctly_mutate_state_on_empty_input(
    tmp_path: Path,
) -> None:
    root = _base_repo(tmp_path)
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS40.md",
                "frontmatter_semantic": {},
                "blocks": [],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    codes = {item["code"] for item in result.diagnostics_payload["diagnostics"]}
    assert SCC0014_PASS_HASH_IDENTITY_VIOLATION not in codes
