from __future__ import annotations

import json
from pathlib import Path

from adeu_semantic_source.compile import (
    SSC0002_DUPLICATE_INPUT,
    SSC0003_INPUT_OUTSIDE_DOCS_ROOT,
    SSC0004_MANIFEST_ENTRY_ABSOLUTE_PATH,
    SSC0009_FRONTMATTER_SEMANTIC_KEY_UNKNOWN,
    SSC0010_SEMANTIC_FENCE_STYLE_INVALID,
    SSC0013_DUPLICATE_IDENTIFIER,
    compile_semantic_source,
)


def _write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _base_repo(tmp_path: Path) -> Path:
    root = tmp_path
    _write(root / "pyproject.toml", "[tool.ruff]\nline-length = 100\n")
    (root / "packages" / "urm_runtime").mkdir(parents=True, exist_ok=True)
    (root / "docs").mkdir(parents=True, exist_ok=True)
    return root


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _codes(result_payload: dict) -> set[str]:
    return {item["code"] for item in result_payload["diagnostics"]}


def test_compile_explicit_input_writes_normalized_and_diagnostics(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(
        root / "docs" / "a.md",
        """---
title: Nonsemantic title
adeu_module_id: mod_a
---

# Header

```adeu.module
module_id: mod_a
kind: arc_lock
```
""",
    )

    result = compile_semantic_source(inputs=["docs/a.md"], repo_root_path=root)

    assert result.success is True
    assert result.normalized_payload is not None

    normalized = _read_json(result.normalized_output_path)
    diagnostics = _read_json(result.diagnostics_output_path)

    assert normalized["schema"] == "semantic_source_collection@0.1"
    assert normalized["input_interface"]["inputs"] == ["docs/a.md"]
    assert normalized["files"][0]["frontmatter_semantic"] == {"adeu_module_id": "mod_a"}
    assert len(normalized["files"][0]["blocks"]) == 1
    assert normalized["files"][0]["blocks"][0]["label"] == "adeu.module"
    assert diagnostics == {"schema": "semantic_source_diagnostics@0.1", "diagnostics": []}


def test_manifest_entries_resolve_relative_to_manifest_dir_and_preserve_order(
    tmp_path: Path,
) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "a.md", "```adeu\nmodule_id: a\n```\n")
    _write(root / "docs" / "b.md", "```adeu\nmodule_id: b\n```\n")
    _write(root / "docs" / "manifests" / "inputs.txt", "../b.md\n../a.md\n")

    result = compile_semantic_source(
        inputs=[],
        inputs_manifest="docs/manifests/inputs.txt",
        repo_root_path=root,
    )

    assert result.success is True
    assert result.normalized_payload is not None
    assert [item["path"] for item in result.normalized_payload["files"]] == [
        "docs/b.md",
        "docs/a.md",
    ]


def test_manifest_absolute_entry_fails_closed(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "manifests" / "inputs.txt", "/tmp/nope.md\n")

    result = compile_semantic_source(
        inputs=[],
        inputs_manifest="docs/manifests/inputs.txt",
        repo_root_path=root,
    )

    assert result.success is False
    assert SSC0004_MANIFEST_ENTRY_ABSOLUTE_PATH in _codes(result.diagnostics_payload)


def test_duplicate_input_paths_fail_closed(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "a.md", "```adeu\nmodule_id: a\n```\n")
    _write(root / "docs" / "manifests" / "inputs.txt", "../a.md\n")

    result = compile_semantic_source(
        inputs=["docs/a.md"],
        inputs_manifest="docs/manifests/inputs.txt",
        repo_root_path=root,
    )

    assert result.success is False
    assert SSC0002_DUPLICATE_INPUT in _codes(result.diagnostics_payload)


def test_out_of_docs_root_input_fails_closed(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(root / "README.md", "# outside docs\n")

    result = compile_semantic_source(inputs=["README.md"], repo_root_path=root)

    assert result.success is False
    assert SSC0003_INPUT_OUTSIDE_DOCS_ROOT in _codes(result.diagnostics_payload)


def test_unknown_semantic_frontmatter_key_fails_closed(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(
        root / "docs" / "a.md",
        """---
adeu_unexpected_key: x
---

```adeu
module_id: a
```
""",
    )

    result = compile_semantic_source(inputs=["docs/a.md"], repo_root_path=root)

    assert result.success is False
    assert SSC0009_FRONTMATTER_SEMANTIC_KEY_UNKNOWN in _codes(result.diagnostics_payload)


def test_tilde_semantic_fence_fails_closed(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(
        root / "docs" / "a.md",
        """~~~adeu
module_id: a
~~~
""",
    )

    result = compile_semantic_source(inputs=["docs/a.md"], repo_root_path=root)

    assert result.success is False
    assert SSC0010_SEMANTIC_FENCE_STYLE_INVALID in _codes(result.diagnostics_payload)


def test_duplicate_identifier_diagnostic_includes_all_claim_sites(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "a.md", "```adeu\nmodule_id: same\n```\n")
    _write(root / "docs" / "b.md", "```adeu\nmodule_id: same\n```\n")

    result = compile_semantic_source(inputs=["docs/a.md", "docs/b.md"], repo_root_path=root)

    assert result.success is False
    payload = result.diagnostics_payload
    duplicate_entries = [
        item for item in payload["diagnostics"] if item["code"] == SSC0013_DUPLICATE_IDENTIFIER
    ]
    assert len(duplicate_entries) == 1
    claim_sites = duplicate_entries[0]["claim_sites"]
    assert claim_sites == [
        {"path": "docs/a.md", "start_line": 1},
        {"path": "docs/b.md", "start_line": 1},
    ]
