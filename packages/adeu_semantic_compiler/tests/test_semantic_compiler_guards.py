from __future__ import annotations

import re
import unicodedata
from pathlib import Path

import pytest
from adeu_semantic_compiler.compile import (
    SCC0001_INPUT_SCHEMA_INVALID,
    SCC0003_INPUT_DIAGNOSTICS_CARRIED,
    SCC0005_BLOCK_LABEL_UNSUPPORTED,
    SCC0009_MODULE_ID_DUPLICATE,
    SCC0010_UNRESOLVED_REFERENCE,
    SCC0011_UNKNOWN_TOKEN,
    SCC0012_LOCK_TYPECHECK_INVALID,
    SCC0017_SURFACE_SIGNATURE_INVALID,
    SCC0018_DELTA_RULE_VIOLATION,
    SCC0020_PR_SPLIT_INVALID,
    assert_artifacts_clean,
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


def _codes(result: dict) -> set[str]:
    return {item["code"] for item in result["diagnostics"]}


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


def _write_v40_surface_baseline(
    root: Path,
    *,
    surface_id: str,
    surface_kind: str,
    selector: str,
    signature_sha256: str,
    keyset: list[str],
) -> None:
    _write(
        root / "artifacts" / "semantic_compiler" / "v40" / "surface_snapshot.json",
        canonical_json(
            {
                "schema": "semantic_compiler_surface_snapshot@0.1",
                "arc": "vnext_plus40",
                "compiler_entrypoint": "python -m adeu_semantic_compiler.compile",
                "surfaces": [
                    {
                        "surface_id": surface_id,
                        "module_id": "arc:vnext_plus40",
                        "module_kind": "arc_lock",
                        "slice_id": "",
                        "surface_kind": surface_kind,
                        "selector": selector,
                        "selector_path": selector,
                        "signature_sha256": signature_sha256,
                        "keyset": keyset,
                    }
                ],
            }
        )
        + "\n",
    )


def test_input_diagnostic_warnings_are_carried_forward_deterministically(
    tmp_path: Path,
) -> None:
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
                        },
                        "identifier": "arc:vnext_plus40",
                    }
                ],
            }
        ],
        source_diagnostics=[
            {
                "code": "SSC0999",
                "severity": "WARN",
                "message": "warning b",
                "path": "docs/z.md",
                "start_line": 7,
                "start_column": 1,
            },
            {
                "code": "SSC0001",
                "severity": "INFO",
                "message": "warning a",
                "path": "docs/a.md",
                "start_line": 2,
                "start_column": 3,
            },
        ],
    )

    first = compile_semantic_compiler(repo_root_path=root)
    second = compile_semantic_compiler(repo_root_path=root)

    assert first.success is True
    assert second.success is True
    assert first.diagnostics_output_path.read_bytes() == second.diagnostics_output_path.read_bytes()

    carried = [
        item
        for item in first.diagnostics_payload["diagnostics"]
        if item["code"] == SCC0003_INPUT_DIAGNOSTICS_CARRIED
    ]
    assert len(carried) == 2
    assert all(item["severity"] == "WARN" for item in carried)
    tuples = [
        (item["module_id"], item.get("path", ""), item["start_line"], item["code"])
        for item in carried
    ]
    assert tuples == sorted(tuples)


def test_unresolved_module_references_fail_closed(tmp_path: Path) -> None:
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
                        },
                        "identifier": "arc:vnext_plus40",
                    },
                    {
                        "label": "adeu.slice_spec",
                        "payload": {
                            "module_id": "slice:vnext_plus40:o2",
                            "arc_id": "vnext_plus40",
                            "slice_id": "o2",
                            "depends_on": ["arc:vnext_plus40", "slice:missing"],
                        },
                        "identifier": "slice:vnext_plus40:o2",
                    },
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is False
    assert SCC0010_UNRESOLVED_REFERENCE in _codes(result.diagnostics_payload)
    unresolved = [
        item
        for item in result.diagnostics_payload["diagnostics"]
        if item["code"] == SCC0010_UNRESOLVED_REFERENCE
    ]
    assert len(unresolved) == 1
    assert unresolved[0]["module_id"] == "slice:vnext_plus40:o2"
    assert unresolved[0]["path"] == "docs/LOCKED_CONTINUATION_vNEXT_PLUS40.md"
    assert unresolved[0]["start_line"] == 1


def test_lock_typecheck_mismatch_fails_closed(tmp_path: Path) -> None:
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
                            "locks": [
                                {
                                    "kind": "exact_set",
                                    "severity": "ERROR",
                                    "target": "stop_gate.metrics",
                                    "params": {"allowed": "not-a-list"},
                                }
                            ],
                        },
                        "identifier": "arc:vnext_plus40",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is False
    assert SCC0012_LOCK_TYPECHECK_INVALID in _codes(result.diagnostics_payload)


def test_unknown_stdlib_tokens_fail_closed(tmp_path: Path) -> None:
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
                            "evidence_requirements": [
                                {
                                    "evidence_type": "doc_json",
                                    "trust_lane": "unknown_lane",
                                    "quality": "high",
                                    "required": True,
                                }
                            ],
                        },
                        "identifier": "arc:vnext_plus40",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is False
    assert SCC0011_UNKNOWN_TOKEN in _codes(result.diagnostics_payload)


def test_duplicate_module_id_reports_sorted_claim_sites(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/a.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:duplicate",
                            "arc_id": "vnext_plus40",
                        },
                        "identifier": "arc:duplicate",
                    }
                ],
            },
            {
                "path": "docs/b.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:duplicate",
                            "arc_id": "vnext_plus40",
                        },
                        "identifier": "arc:duplicate",
                    }
                ],
            },
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is False
    duplicate_diags = [
        item
        for item in result.diagnostics_payload["diagnostics"]
        if item["code"] == SCC0009_MODULE_ID_DUPLICATE
    ]
    assert len(duplicate_diags) == 1
    claim_sites = duplicate_diags[0]["details"]["claim_sites"]
    assert claim_sites == sorted(claim_sites, key=lambda row: (row["path"], row["start_line"]))


def test_diagnostics_follow_contract_sorting_and_code_namespace(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/b.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.unknown",
                        "payload": {},
                        "identifier": None,
                    }
                ],
            },
            {
                "path": "docs/a.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus40",
                            "arc_id": "vnext_plus40",
                            "depends_on": ["missing:dep"],
                        },
                        "identifier": "arc:vnext_plus40",
                    }
                ],
            },
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is False
    diagnostics = result.diagnostics_payload["diagnostics"]
    assert all(re.fullmatch(r"SCC[0-9]{4}", item["code"]) for item in diagnostics)
    assert all(item["start_line"] >= 1 and item["start_column"] >= 1 for item in diagnostics)

    tuples = [
        (item["module_id"], item.get("path", ""), item["start_line"], item["code"])
        for item in diagnostics
    ]
    assert tuples == sorted(tuples)


def test_commitments_ir_and_nested_collections_are_deterministically_sorted(
    tmp_path: Path,
) -> None:
    root = _base_repo(tmp_path)
    _write(root / "a", "surface a\n")
    _write(root / "z", "surface z\n")
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
                            "module_id": "arc:b",
                            "arc_id": "vnext_plus40",
                            "locks": [
                                {
                                    "lock_id": "lock_b",
                                    "kind": "freeze",
                                    "severity": "ERROR",
                                    "target": "z",
                                },
                                {
                                    "lock_id": "lock_a",
                                    "kind": "freeze",
                                    "severity": "ERROR",
                                    "target": "a",
                                },
                            ],
                            "surfaces": [
                                {
                                    "surface_id": "surface_b",
                                    "surface_kind": "file",
                                    "selector": "z",
                                },
                                {
                                    "surface_id": "surface_a",
                                    "surface_kind": "file",
                                    "selector": "a",
                                },
                            ],
                            "assertions": [
                                {
                                    "assertion_id": "assert_b",
                                    "assertion_type": "determinism",
                                    "target": "z",
                                    "expected": {},
                                },
                                {
                                    "assertion_id": "assert_a",
                                    "assertion_type": "determinism",
                                    "target": "a",
                                    "expected": {},
                                },
                            ],
                            "evidence_requirements": [
                                {
                                    "evidence_id": "evidence_b",
                                    "evidence_type": "doc_json",
                                    "trust_lane": "tooling",
                                    "quality": "high",
                                    "required": True,
                                },
                                {
                                    "evidence_id": "evidence_a",
                                    "evidence_type": "doc_json",
                                    "trust_lane": "tooling",
                                    "quality": "high",
                                    "required": True,
                                },
                            ],
                        },
                        "identifier": "arc:b",
                    },
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:a",
                            "arc_id": "vnext_plus40",
                        },
                        "identifier": "arc:a",
                    },
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is True
    assert result.commitments_ir_payload is not None
    modules = result.commitments_ir_payload["modules"]
    assert [module["module_id"] for module in modules] == ["arc:a", "arc:b"]

    module_b = next(item for item in modules if item["module_id"] == "arc:b")
    assert [lock["lock_id"] for lock in module_b["locks"]] == ["lock_a", "lock_b"]
    assert [surface["surface_id"] for surface in module_b["surfaces"]] == ["surface_a", "surface_b"]
    assert [assertion["assertion_id"] for assertion in module_b["assertions"]] == [
        "assert_a",
        "assert_b",
    ]
    assert [evidence["evidence_id"] for evidence in module_b["evidence_requirements"]] == [
        "evidence_a",
        "evidence_b",
    ]


def test_pass_manifest_fields_sequence_and_hash_identity_policy_are_frozen(
    tmp_path: Path,
) -> None:
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
                        },
                        "identifier": "arc:vnext_plus40",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is True
    manifest = result.pass_manifest_payload
    expected_sequence = [
        "LoadCollection",
        "ValidateBlocks",
        "RevalidateNormalization",
        "BuildIR",
        "ResolveRefs",
        "TypecheckLocks",
    ]
    assert manifest["pass_sequence"] == expected_sequence

    entries = manifest["pass_manifest"]
    assert [entry["name"] for entry in entries] == expected_sequence
    assert [entry["index"] for entry in entries] == list(range(len(expected_sequence)))
    for entry in entries:
        assert set(entry) == {"name", "index", "input_sha256", "output_sha256"}
        assert re.fullmatch(r"[0-9a-f]{64}", entry["input_sha256"])
        assert re.fullmatch(r"[0-9a-f]{64}", entry["output_sha256"])

    by_name = {entry["name"]: entry for entry in entries}
    for read_only in (
        "LoadCollection",
        "ValidateBlocks",
        "RevalidateNormalization",
        "TypecheckLocks",
    ):
        assert by_name[read_only]["input_sha256"] == by_name[read_only]["output_sha256"]
    for mutating in ("BuildIR", "ResolveRefs"):
        assert by_name[mutating]["input_sha256"] != by_name[mutating]["output_sha256"]


def test_compiler_is_not_a_markdown_parser_boundary(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "raw.md", "```adeu\nmodule_id: x\n```\n")
    _, diagnostics_path = _write_semantic_source_artifacts(
        root,
        files=[],
        source_diagnostics=[],
    )

    result = compile_semantic_compiler(
        repo_root_path=root,
        semantic_source_path="docs/raw.md",
        semantic_source_diagnostics_path=str(diagnostics_path.relative_to(root)).replace("\\", "/"),
    )

    assert result.success is False
    codes = _codes(result.diagnostics_payload)
    assert SCC0001_INPUT_SCHEMA_INVALID in codes
    assert SCC0005_BLOCK_LABEL_UNSUPPORTED not in codes


def test_v41_surface_snapshot_uses_top_level_keyset_mode(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "schema.json", '{"outer":{"nested":1},"leaf":2}\n')
    _write(
        root / "docs" / "guide.md",
        '```json\n{"schema":"surface.schema","outer":{"a":1},"leaf":2}\n```\n',
    )
    _write(root / "docs" / "payload.bin", "binary-ish\n")
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus41",
                            "arc_id": "vnext_plus41",
                            "surfaces": [
                                {
                                    "surface_id": "surface_file",
                                    "surface_kind": "file",
                                    "selector": "docs/payload.bin",
                                },
                                {
                                    "surface_id": "surface_markdown",
                                    "surface_kind": "markdown_json_block",
                                    "selector": {
                                        "path": "docs/guide.md",
                                        "schema": "surface.schema",
                                    },
                                },
                                {
                                    "surface_id": "surface_schema",
                                    "surface_kind": "schema",
                                    "selector": "docs/schema.json",
                                },
                            ],
                        },
                        "identifier": "arc:vnext_plus41",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is True
    assert result.surface_snapshot_payload is not None
    by_id = {
        row["surface_id"]: row for row in result.surface_snapshot_payload["surfaces"]
    }
    assert by_id["surface_schema"]["keyset"] == ["leaf", "outer"]
    assert by_id["surface_markdown"]["keyset"] == ["leaf", "outer", "schema"]
    assert by_id["surface_file"]["keyset"] == []
    assert result.surface_diff_payload is not None
    assert result.surface_diff_payload["delta_eval_mode"] == "no_baseline"


def test_v41_surface_selector_dot_segments_are_normalized_deterministically(
    tmp_path: Path,
) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "nested" / "schema.json", '{"k":1}\n')
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus41",
                            "arc_id": "vnext_plus41",
                            "surfaces": [
                                {
                                    "surface_id": "surface_schema",
                                    "surface_kind": "schema",
                                    "selector": "docs/nested/../nested/./schema.json",
                                }
                            ],
                        },
                        "identifier": "arc:vnext_plus41",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is True
    assert result.surface_snapshot_payload is not None
    assert (
        result.surface_snapshot_payload["surfaces"][0]["selector_path"]
        == "docs/nested/schema.json"
    )


def test_v41_surface_selector_absolute_paths_fail_closed(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus41",
                            "arc_id": "vnext_plus41",
                            "surfaces": [
                                {
                                    "surface_id": "surface_schema",
                                    "surface_kind": "schema",
                                    "selector": "/tmp/absolute.json",
                                }
                            ],
                        },
                        "identifier": "arc:vnext_plus41",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is False
    assert SCC0017_SURFACE_SIGNATURE_INVALID in _codes(result.diagnostics_payload)


def test_v41_surface_selector_utf8_nfc_normalization_is_enforced(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    nfc_name = unicodedata.normalize("NFC", "café")
    nfd_name = unicodedata.normalize("NFD", "café")
    _write(root / "docs" / f"{nfc_name}.json", '{"ok": true}\n')
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus41",
                            "arc_id": "vnext_plus41",
                            "surfaces": [
                                {
                                    "surface_id": "surface_schema",
                                    "surface_kind": "schema",
                                    "selector": f"docs/{nfd_name}.json",
                                }
                            ],
                        },
                        "identifier": "arc:vnext_plus41",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is True
    assert result.surface_snapshot_payload is not None
    assert (
        result.surface_snapshot_payload["surfaces"][0]["selector_path"]
        == f"docs/{nfc_name}.json"
    )


def test_v41_markdown_surface_missing_schema_selector_fails_closed(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "guide.md", '```json\n{"block_index":0,"value":1}\n```\n')
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus41",
                            "arc_id": "vnext_plus41",
                            "surfaces": [
                                {
                                    "surface_id": "surface_markdown",
                                    "surface_kind": "markdown_json_block",
                                    "selector": {
                                        "path": "docs/guide.md",
                                        "schema": "surface.schema",
                                    },
                                }
                            ],
                        },
                        "identifier": "arc:vnext_plus41",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is False
    assert SCC0017_SURFACE_SIGNATURE_INVALID in _codes(result.diagnostics_payload)


def test_v41_markdown_surface_duplicate_schema_block_index_fails_closed(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(
        root / "docs" / "guide.md",
        (
            '```json\n{"schema":"surface.schema","block_index":0,"value":1}\n```\n'
            '```json\n{"schema":"surface.schema","block_index":0,"value":2}\n```\n'
        ),
    )
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus41",
                            "arc_id": "vnext_plus41",
                            "surfaces": [
                                {
                                    "surface_id": "surface_markdown",
                                    "surface_kind": "markdown_json_block",
                                    "selector": {
                                        "path": "docs/guide.md",
                                        "schema": "surface.schema",
                                    },
                                }
                            ],
                        },
                        "identifier": "arc:vnext_plus41",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is False
    assert SCC0017_SURFACE_SIGNATURE_INVALID in _codes(result.diagnostics_payload)


def test_v41_file_surface_symlink_entries_fail_closed(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "target.txt", "target\n")
    (root / "docs").mkdir(parents=True, exist_ok=True)
    (root / "docs" / "link.txt").symlink_to(root / "docs" / "target.txt")
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus41",
                            "arc_id": "vnext_plus41",
                            "surfaces": [
                                {
                                    "surface_id": "surface_link",
                                    "surface_kind": "file",
                                    "selector": "docs/link.txt",
                                }
                            ],
                        },
                        "identifier": "arc:vnext_plus41",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is False
    assert SCC0017_SURFACE_SIGNATURE_INVALID in _codes(result.diagnostics_payload)


def test_v41_surface_selector_symlink_parent_traversal_fails_closed(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    outside_dir = tmp_path / "outside"
    _write(outside_dir / "data.json", '{"k": 1}\n')
    (root / "docs").mkdir(parents=True, exist_ok=True)
    (root / "docs" / "evil").symlink_to(outside_dir)
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus41",
                            "arc_id": "vnext_plus41",
                            "surfaces": [
                                {
                                    "surface_id": "surface_escape",
                                    "surface_kind": "schema",
                                    "selector": "docs/evil/data.json",
                                }
                            ],
                        },
                        "identifier": "arc:vnext_plus41",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is False
    assert SCC0017_SURFACE_SIGNATURE_INVALID in _codes(result.diagnostics_payload)


def test_v41_surface_large_file_fails_closed(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    huge_size = (8 * 1024 * 1024) + 1
    huge_path = root / "docs" / "huge.bin"
    huge_path.parent.mkdir(parents=True, exist_ok=True)
    huge_path.write_bytes(b"x" * huge_size)
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus41",
                            "arc_id": "vnext_plus41",
                            "surfaces": [
                                {
                                    "surface_id": "surface_large",
                                    "surface_kind": "file",
                                    "selector": "docs/huge.bin",
                                }
                            ],
                        },
                        "identifier": "arc:vnext_plus41",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is False
    assert SCC0017_SURFACE_SIGNATURE_INVALID in _codes(result.diagnostics_payload)


def test_v41_pr_split_multi_owner_surfaces_fail_closed(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "shared.json", '{"k":1}\n')
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus41",
                            "arc_id": "vnext_plus41",
                            "surfaces": [
                                {
                                    "surface_id": "shared_surface",
                                    "surface_kind": "schema",
                                    "selector": "docs/shared.json",
                                }
                            ],
                        },
                        "identifier": "arc:vnext_plus41",
                    },
                    {
                        "label": "adeu.slice_spec",
                        "payload": {
                            "module_id": "slice:vnext_plus41:p1",
                            "arc_id": "vnext_plus41",
                            "slice_id": "p1",
                            "surfaces": [
                                {
                                    "surface_id": "shared_surface",
                                    "surface_kind": "schema",
                                    "selector": "docs/shared.json",
                                }
                            ],
                        },
                        "identifier": "slice:vnext_plus41:p1",
                    },
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is False
    assert SCC0020_PR_SPLIT_INVALID in _codes(result.diagnostics_payload)


def test_v41_freeze_delta_violation_is_fail_closed_when_baseline_present(
    tmp_path: Path,
) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "schema.json", '{"new":2}\n')
    _write_v40_surface_baseline(
        root,
        surface_id="surface_schema",
        surface_kind="schema",
        selector="docs/schema.json",
        signature_sha256="0" * 64,
        keyset=["old"],
    )
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus41",
                            "arc_id": "vnext_plus41",
                            "locks": [
                                {
                                    "kind": "freeze",
                                    "severity": "ERROR",
                                    "target": "surface_schema",
                                }
                            ],
                            "surfaces": [
                                {
                                    "surface_id": "surface_schema",
                                    "surface_kind": "schema",
                                    "selector": "docs/schema.json",
                                }
                            ],
                        },
                        "identifier": "arc:vnext_plus41",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is False
    assert SCC0018_DELTA_RULE_VIOLATION in _codes(result.diagnostics_payload)


def test_v41_exact_set_structured_keyset_violation_fails_closed(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "schema.json", '{"new":2}\n')
    _write_v40_surface_baseline(
        root,
        surface_id="surface_schema",
        surface_kind="schema",
        selector="docs/schema.json",
        signature_sha256="1" * 64,
        keyset=["old"],
    )
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus41",
                            "arc_id": "vnext_plus41",
                            "locks": [
                                {
                                    "kind": "exact_set",
                                    "severity": "ERROR",
                                    "target": "surface_schema",
                                    "params": {"allowed": ["legacy"]},
                                }
                            ],
                            "surfaces": [
                                {
                                    "surface_id": "surface_schema",
                                    "surface_kind": "schema",
                                    "selector": "docs/schema.json",
                                }
                            ],
                        },
                        "identifier": "arc:vnext_plus41",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is False
    assert SCC0018_DELTA_RULE_VIOLATION in _codes(result.diagnostics_payload)


def test_v41_additive_only_structured_keyset_violation_fails_closed(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "schema.json", '{"only_new":2}\n')
    _write_v40_surface_baseline(
        root,
        surface_id="surface_schema",
        surface_kind="schema",
        selector="docs/schema.json",
        signature_sha256="2" * 64,
        keyset=["legacy", "only_new"],
    )
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus41",
                            "arc_id": "vnext_plus41",
                            "locks": [
                                {
                                    "kind": "additive_only",
                                    "severity": "ERROR",
                                    "target": "surface_schema",
                                }
                            ],
                            "surfaces": [
                                {
                                    "surface_id": "surface_schema",
                                    "surface_kind": "schema",
                                    "selector": "docs/schema.json",
                                }
                            ],
                        },
                        "identifier": "arc:vnext_plus41",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is False
    assert SCC0018_DELTA_RULE_VIOLATION in _codes(result.diagnostics_payload)


def test_v41_additive_only_structured_superset_keyset_is_allowed(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "schema.json", '{"legacy":1,"only_new":2}\n')
    _write_v40_surface_baseline(
        root,
        surface_id="surface_schema",
        surface_kind="schema",
        selector="docs/schema.json",
        signature_sha256="3" * 64,
        keyset=["legacy"],
    )
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus41",
                            "arc_id": "vnext_plus41",
                            "locks": [
                                {
                                    "kind": "additive_only",
                                    "severity": "ERROR",
                                    "target": "surface_schema",
                                }
                            ],
                            "surfaces": [
                                {
                                    "surface_id": "surface_schema",
                                    "surface_kind": "schema",
                                    "selector": "docs/schema.json",
                                }
                            ],
                        },
                        "identifier": "arc:vnext_plus41",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is True
    assert SCC0018_DELTA_RULE_VIOLATION not in _codes(result.diagnostics_payload)


def test_v41_exact_set_file_signature_violation_fails_closed(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "payload.bin", "new bytes\n")
    _write_v40_surface_baseline(
        root,
        surface_id="surface_file",
        surface_kind="file",
        selector="docs/payload.bin",
        signature_sha256="4" * 64,
        keyset=[],
    )
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus41",
                            "arc_id": "vnext_plus41",
                            "locks": [
                                {
                                    "kind": "exact_set",
                                    "severity": "ERROR",
                                    "target": "surface_file",
                                    "params": {"allowed": ["bytes"]},
                                }
                            ],
                            "surfaces": [
                                {
                                    "surface_id": "surface_file",
                                    "surface_kind": "file",
                                    "selector": "docs/payload.bin",
                                }
                            ],
                        },
                        "identifier": "arc:vnext_plus41",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is False
    assert SCC0018_DELTA_RULE_VIOLATION in _codes(result.diagnostics_payload)


def test_v41_additive_only_file_signature_violation_fails_closed(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "payload.bin", "new bytes\n")
    _write_v40_surface_baseline(
        root,
        surface_id="surface_file",
        surface_kind="file",
        selector="docs/payload.bin",
        signature_sha256="5" * 64,
        keyset=[],
    )
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus41",
                            "arc_id": "vnext_plus41",
                            "locks": [
                                {
                                    "kind": "additive_only",
                                    "severity": "ERROR",
                                    "target": "surface_file",
                                }
                            ],
                            "surfaces": [
                                {
                                    "surface_id": "surface_file",
                                    "surface_kind": "file",
                                    "selector": "docs/payload.bin",
                                }
                            ],
                        },
                        "identifier": "arc:vnext_plus41",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is False
    assert SCC0018_DELTA_RULE_VIOLATION in _codes(result.diagnostics_payload)


def test_v41_required_evidence_entries_are_deterministically_ordered(
    tmp_path: Path,
) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "schema.json", '{"k":1}\n')
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus41",
                            "arc_id": "vnext_plus41",
                            "surfaces": [
                                {
                                    "surface_id": "surface_schema",
                                    "surface_kind": "schema",
                                    "selector": "docs/schema.json",
                                }
                            ],
                            "evidence_requirements": [
                                {
                                    "evidence_id": "z",
                                    "evidence_type": "doc_json",
                                    "surface_id": "surface_schema",
                                    "trust_lane": "tooling",
                                    "quality": "high",
                                    "required": True,
                                },
                                {
                                    "evidence_id": "a",
                                    "evidence_type": "artifact_hash",
                                    "surface_id": "surface_schema",
                                    "trust_lane": "tooling",
                                    "quality": "high",
                                    "required": True,
                                },
                                {
                                    "evidence_id": "b",
                                    "evidence_type": "artifact_hash",
                                    "surface_id": "",
                                    "trust_lane": "tooling",
                                    "quality": "high",
                                    "required": True,
                                },
                            ],
                        },
                        "identifier": "arc:vnext_plus41",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is True
    assert result.evidence_manifest_payload is not None
    rows = result.evidence_manifest_payload["required_evidence"]
    tuples = [
        (row["evidence_type"], row["surface_id"], row["module_id"], row["evidence_id"])
        for row in rows
    ]
    assert tuples == sorted(tuples)


def test_v41_pr_splits_markdown_is_sorted_by_slice_module_and_surface(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "a.json", '{"a":1}\n')
    _write(root / "docs" / "z.json", '{"z":1}\n')
    _write(root / "docs" / "p1.json", '{"p1":1}\n')
    _write(root / "docs" / "p2.json", '{"p2":1}\n')
    _write_semantic_source_artifacts(
        root,
        files=[
            {
                "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md",
                "frontmatter_semantic": {},
                "blocks": [
                    {
                        "label": "adeu.arc_lock",
                        "payload": {
                            "module_id": "arc:vnext_plus41",
                            "arc_id": "vnext_plus41",
                            "surfaces": [
                                {
                                    "surface_id": "surface_z",
                                    "surface_kind": "schema",
                                    "selector": "docs/z.json",
                                },
                                {
                                    "surface_id": "surface_a",
                                    "surface_kind": "schema",
                                    "selector": "docs/a.json",
                                },
                            ],
                        },
                        "identifier": "arc:vnext_plus41",
                    },
                    {
                        "label": "adeu.slice_spec",
                        "payload": {
                            "module_id": "slice:vnext_plus41:p2",
                            "arc_id": "vnext_plus41",
                            "slice_id": "p2",
                            "surfaces": [
                                {
                                    "surface_id": "surface_p2",
                                    "surface_kind": "schema",
                                    "selector": "docs/p2.json",
                                }
                            ],
                        },
                        "identifier": "slice:vnext_plus41:p2",
                    },
                    {
                        "label": "adeu.slice_spec",
                        "payload": {
                            "module_id": "slice:vnext_plus41:p1",
                            "arc_id": "vnext_plus41",
                            "slice_id": "p1",
                            "surfaces": [
                                {
                                    "surface_id": "surface_p1",
                                    "surface_kind": "schema",
                                    "selector": "docs/p1.json",
                                }
                            ],
                        },
                        "identifier": "slice:vnext_plus41:p1",
                    },
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)

    assert result.success is True
    assert result.pr_splits_markdown is not None
    markdown = result.pr_splits_markdown
    head_arc = "## Slice `<none>` / Module `arc:vnext_plus41`"
    head_p1 = "## Slice `p1` / Module `slice:vnext_plus41:p1`"
    head_p2 = "## Slice `p2` / Module `slice:vnext_plus41:p2`"
    assert markdown.index(head_arc) < markdown.index(head_p1) < markdown.index(head_p2)
    assert markdown.index("- `surface_a` (`schema`) `add`") < markdown.index(
        "- `surface_z` (`schema`) `add`"
    )


def test_generated_artifact_cleanliness_guard_passes_when_outputs_match(tmp_path: Path) -> None:
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
                        },
                        "identifier": "arc:vnext_plus40",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)
    assert result.success is True

    assert_artifacts_clean(repo_root_path=root)


@pytest.mark.parametrize(
    ("target_attr", "error_match"),
    [
        ("commitments_ir_output_path", "generated commitments ir artifact is out of date"),
        ("diagnostics_output_path", "generated compiler diagnostics artifact is out of date"),
        ("pass_manifest_output_path", "generated pass manifest artifact is out of date"),
        ("surface_snapshot_output_path", "generated surface snapshot artifact is out of date"),
        ("surface_diff_output_path", "generated surface diff artifact is out of date"),
        ("evidence_manifest_output_path", "generated evidence manifest artifact is out of date"),
        ("pr_splits_output_path", "generated pr splits artifact is out of date"),
    ],
)
def test_generated_artifact_cleanliness_guard_fails_on_tampered_outputs(
    tmp_path: Path,
    target_attr: str,
    error_match: str,
) -> None:
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
                        },
                        "identifier": "arc:vnext_plus40",
                    }
                ],
            }
        ],
    )

    result = compile_semantic_compiler(repo_root_path=root)
    assert result.success is True

    tampered_path = getattr(result, target_attr)
    tampered_path.write_text("{}\n", encoding="utf-8")

    with pytest.raises(RuntimeError, match=error_match):
        assert_artifacts_clean(repo_root_path=root)
