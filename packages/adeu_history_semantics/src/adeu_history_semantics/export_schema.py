from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from adeu_ir.repo import repo_root

from .models import (
    ADEU_HISTORY_LEDGER_ENTRY_SCHEMA,
    ADEU_HISTORY_LEDGER_SCHEMA,
    ADEU_HISTORY_PRECLASSIFICATION_SCHEMA,
    ADEU_HISTORY_SLICE_SCHEMA,
    ADEU_HISTORY_SOURCE_ARTIFACT_SCHEMA,
    ADEU_HISTORY_TEXT_SHAPE_SIGNALS_SCHEMA,
    ADEU_HISTORY_THEME_ANCHOR_SCHEMA,
    HistoryLedger,
    HistoryLedgerEntry,
    HistoryPreclassification,
    HistorySlice,
    HistorySourceArtifact,
    HistoryTextShapeSignals,
    HistoryThemeAnchor,
)

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _write_schema(path: Path, schema: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(schema, indent=2, sort_keys=True) + "\n"
    path.write_text(payload, encoding="utf-8")


def _assert_no_absolute_path_material(
    value: Any,
    *,
    repo_root_path: Path,
    node_path: str = "$",
) -> None:
    if isinstance(value, dict):
        for key in sorted(value):
            _assert_no_absolute_path_material(
                value[key],
                repo_root_path=repo_root_path,
                node_path=f"{node_path}.{key}",
            )
        return
    if isinstance(value, list):
        for index, item in enumerate(value):
            _assert_no_absolute_path_material(
                item,
                repo_root_path=repo_root_path,
                node_path=f"{node_path}[{index}]",
            )
        return
    if not isinstance(value, str):
        return

    normalized = value.replace("\\", "/")
    root_text = repo_root_path.as_posix()
    if root_text in normalized:
        raise RuntimeError(
            f"schema export contains repository absolute path material at {node_path}: {value!r}"
        )
    if _WINDOWS_ABSOLUTE_PATH_RE.search(value):
        raise RuntimeError(
            f"schema export contains Windows absolute path material at {node_path}: {value!r}"
        )
    if normalized.startswith("/home/") or normalized.startswith("/Users/"):
        raise RuntimeError(
            f"schema export contains user-home absolute path material at {node_path}: {value!r}"
        )


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    schema_outputs = [
        (
            HistorySourceArtifact,
            ADEU_HISTORY_SOURCE_ARTIFACT_SCHEMA,
            root
            / "packages"
            / "adeu_history_semantics"
            / "schema"
            / "adeu_history_source_artifact.v1.json",
            root / "spec" / "adeu_history_source_artifact.schema.json",
        ),
        (
            HistoryTextShapeSignals,
            ADEU_HISTORY_TEXT_SHAPE_SIGNALS_SCHEMA,
            root
            / "packages"
            / "adeu_history_semantics"
            / "schema"
            / "adeu_history_text_shape_signals.v1.json",
            root / "spec" / "adeu_history_text_shape_signals.schema.json",
        ),
        (
            HistoryPreclassification,
            ADEU_HISTORY_PRECLASSIFICATION_SCHEMA,
            root
            / "packages"
            / "adeu_history_semantics"
            / "schema"
            / "adeu_history_preclassification.v1.json",
            root / "spec" / "adeu_history_preclassification.schema.json",
        ),
        (
            HistoryLedgerEntry,
            ADEU_HISTORY_LEDGER_ENTRY_SCHEMA,
            root
            / "packages"
            / "adeu_history_semantics"
            / "schema"
            / "adeu_history_ledger_entry.v1.json",
            root / "spec" / "adeu_history_ledger_entry.schema.json",
        ),
        (
            HistoryLedger,
            ADEU_HISTORY_LEDGER_SCHEMA,
            root
            / "packages"
            / "adeu_history_semantics"
            / "schema"
            / "adeu_history_ledger.v1.json",
            root / "spec" / "adeu_history_ledger.schema.json",
        ),
        (
            HistorySlice,
            ADEU_HISTORY_SLICE_SCHEMA,
            root
            / "packages"
            / "adeu_history_semantics"
            / "schema"
            / "adeu_history_slice.v1.json",
            root / "spec" / "adeu_history_slice.schema.json",
        ),
        (
            HistoryThemeAnchor,
            ADEU_HISTORY_THEME_ANCHOR_SCHEMA,
            root
            / "packages"
            / "adeu_history_semantics"
            / "schema"
            / "adeu_history_theme_anchor.v1.json",
            root / "spec" / "adeu_history_theme_anchor.schema.json",
        ),
    ]

    for model, expected_schema, authoritative_path, mirror_path in schema_outputs:
        schema = model.model_json_schema(by_alias=True)
        if schema["properties"]["schema"]["const"] != expected_schema:
            raise RuntimeError(f"schema marker drift for {expected_schema}")
        _assert_no_absolute_path_material(schema, repo_root_path=root)
        _write_schema(authoritative_path, schema)
        _write_schema(mirror_path, schema)


if __name__ == "__main__":
    main()
