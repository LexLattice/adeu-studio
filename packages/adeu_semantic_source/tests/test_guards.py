from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_semantic_source.compile import (
    SEMANTIC_SOURCE_COLLECTION_SCHEMA,
    SEMANTIC_SOURCE_DIAGNOSTICS_SCHEMA,
    SSC0003_INPUT_OUTSIDE_DOCS_ROOT,
    SSC0007_FRONTMATTER_YAML_FEATURE_FORBIDDEN,
    SSC0008_FRONTMATTER_YAML_SHAPE_INVALID,
    SSC0009_FRONTMATTER_SEMANTIC_KEY_UNKNOWN,
    SSC0010_SEMANTIC_FENCE_STYLE_INVALID,
    SSC0015_SEMANTIC_DECLARATION_AMBIGUOUS,
    assert_artifacts_clean,
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


def test_parser_rerun_determinism_outputs_are_byte_identical(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(
        root / "docs" / "a.md",
        """---
adeu_module_id: a
---

```adeu.module
module_id: a
kind: arc_lock
```
""",
    )

    first = compile_semantic_source(inputs=["docs/a.md"], repo_root_path=root)
    normalized_before = first.normalized_output_path.read_bytes()
    diagnostics_before = first.diagnostics_output_path.read_bytes()

    second = compile_semantic_source(inputs=["docs/a.md"], repo_root_path=root)
    normalized_after = second.normalized_output_path.read_bytes()
    diagnostics_after = second.diagnostics_output_path.read_bytes()

    assert first.success is True
    assert second.success is True
    assert normalized_before == normalized_after
    assert diagnostics_before == diagnostics_after


def test_generated_artifact_cleanliness_guard_passes_when_files_match(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "a.md", "```adeu\nmodule_id: a\n```\n")

    result = compile_semantic_source(inputs=["docs/a.md"], repo_root_path=root)
    assert result.success is True

    assert_artifacts_clean(inputs=["docs/a.md"], repo_root_path=root)


def test_generated_artifact_cleanliness_guard_fails_on_tampered_output(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "a.md", "```adeu\nmodule_id: a\n```\n")

    result = compile_semantic_source(inputs=["docs/a.md"], repo_root_path=root)
    assert result.success is True

    result.normalized_output_path.write_text("{}\n", encoding="utf-8")

    with pytest.raises(RuntimeError, match="normalized artifact is out of date"):
        assert_artifacts_clean(inputs=["docs/a.md"], repo_root_path=root)


def test_prose_only_edits_do_not_change_semantic_source_hash(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    path = root / "docs" / "a.md"
    _write(
        path,
        """---
title: v1 title
---

Intro prose line.

```adeu
module_id: mod_a
kind: arc_lock
```

Tail prose line.
""",
    )

    first = compile_semantic_source(inputs=["docs/a.md"], repo_root_path=root)
    assert first.success is True
    assert first.normalized_payload is not None
    first_hash = first.normalized_payload["semantic_source_hash"]

    _write(
        path,
        """---
title: v2 title
---

Changed prose line.

```adeu
module_id: mod_a
kind: arc_lock
```

Different nonsemantic paragraph.
""",
    )

    second = compile_semantic_source(inputs=["docs/a.md"], repo_root_path=root)
    assert second.success is True
    assert second.normalized_payload is not None
    second_hash = second.normalized_payload["semantic_source_hash"]

    assert first_hash == second_hash


def test_normalization_stabilizes_line_endings_and_trailing_whitespace(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    path = root / "docs" / "a.md"

    path.write_bytes(
        (
            "```adeu\r\n"
            'module_id: a   \r\n'
            'note: "keep  inner"   \r\n'
            "```\r\n"
        ).encode("utf-8")
    )

    first = compile_semantic_source(inputs=["docs/a.md"], repo_root_path=root)
    assert first.success is True
    assert first.normalized_payload is not None
    first_hash = first.normalized_payload["semantic_source_hash"]

    _write(
        path,
        """```adeu
module_id: a
note: "keep  inner"
```
""",
    )

    second = compile_semantic_source(inputs=["docs/a.md"], repo_root_path=root)
    assert second.success is True
    assert second.normalized_payload is not None
    second_hash = second.normalized_payload["semantic_source_hash"]

    assert first_hash == second_hash
    assert second.normalized_payload["files"][0]["blocks"][0]["payload"]["note"] == "keep  inner"


@pytest.mark.parametrize(
    ("frontmatter", "expected_code"),
    [
        (
            """---
adeu_module_id: &id mod_a
asc_module_id: *id
---
""",
            SSC0007_FRONTMATTER_YAML_FEATURE_FORBIDDEN,
        ),
        (
            """---
- adeu_module_id: mod_a
---
""",
            SSC0008_FRONTMATTER_YAML_SHAPE_INVALID,
        ),
    ],
)
def test_frontmatter_yaml_profile_fail_closed(
    tmp_path: Path,
    frontmatter: str,
    expected_code: str,
) -> None:
    root = _base_repo(tmp_path)
    _write(
        root / "docs" / "a.md",
        frontmatter
        + """
```adeu
module_id: a
```
""",
    )

    result = compile_semantic_source(inputs=["docs/a.md"], repo_root_path=root)

    assert result.success is False
    assert expected_code in _codes(result.diagnostics_payload)


def test_diagnostics_are_sorted_by_path_line_code(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "a.md", "~~~adeu\nmodule_id: a\n~~~\n")
    _write(
        root / "docs" / "b.md",
        """---
adeu_unknown: x
---

```adeu
module_id: b
```
""",
    )

    result = compile_semantic_source(
        inputs=["docs/b.md", "docs/a.md"],
        repo_root_path=root,
    )

    assert result.success is False
    tuples = [
        (item.get("path", ""), item["start_line"], item["code"])
        for item in result.diagnostics_payload["diagnostics"]
    ]
    assert tuples == sorted(tuples)


def test_path_normalization_uses_posix_and_lexical_docs_boundary(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "sub" / "a.md", "```adeu\nmodule_id: a\n```\n")
    _write(root / "README.md", "outside docs\n")

    success_result = compile_semantic_source(
        inputs=[r"docs\sub\..\sub\a.md"],
        repo_root_path=root,
    )
    assert success_result.success is True
    assert success_result.normalized_payload is not None
    assert success_result.normalized_payload["input_interface"]["inputs"] == ["docs/sub/a.md"]

    fail_result = compile_semantic_source(
        inputs=[r"docs\..\README.md"],
        repo_root_path=root,
    )
    assert fail_result.success is False
    assert SSC0003_INPUT_OUTSIDE_DOCS_ROOT in _codes(fail_result.diagnostics_payload)


def test_indented_semantic_fence_fails_closed(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(
        root / "docs" / "a.md",
        """  ```adeu
module_id: a
  ```
""",
    )

    result = compile_semantic_source(inputs=["docs/a.md"], repo_root_path=root)

    assert result.success is False
    codes = _codes(result.diagnostics_payload)
    assert SSC0010_SEMANTIC_FENCE_STYLE_INVALID in codes


def test_ambiguous_identifier_fields_fail_closed(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(
        root / "docs" / "a.md",
        """

```adeu
module_id: x
id: y
```
""",
    )

    result = compile_semantic_source(inputs=["docs/a.md"], repo_root_path=root)

    assert result.success is False
    codes = _codes(result.diagnostics_payload)
    assert SSC0015_SEMANTIC_DECLARATION_AMBIGUOUS in codes


def test_schema_labels_are_stable(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(root / "docs" / "a.md", "```adeu\nmodule_id: a\n```\n")

    result = compile_semantic_source(inputs=["docs/a.md"], repo_root_path=root)

    assert result.success is True
    assert result.normalized_payload is not None
    diagnostics = _read_json(result.diagnostics_output_path)

    assert result.normalized_payload["schema"] == SEMANTIC_SOURCE_COLLECTION_SCHEMA
    assert diagnostics["schema"] == SEMANTIC_SOURCE_DIAGNOSTICS_SCHEMA


def test_diagnostics_use_one_based_positions(tmp_path: Path) -> None:
    root = _base_repo(tmp_path)
    _write(
        root / "docs" / "a.md",
        """---
adeu_unknown: x
---

```adeu
module_id: a
```
""",
    )

    result = compile_semantic_source(inputs=["docs/a.md"], repo_root_path=root)

    assert result.success is False
    first = result.diagnostics_payload["diagnostics"][0]
    assert first["start_line"] == 1
    assert first["start_column"] == 1
    assert first["code"] == SSC0009_FRONTMATTER_SEMANTIC_KEY_UNKNOWN
