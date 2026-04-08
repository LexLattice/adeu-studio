from __future__ import annotations

import json
import re
from pathlib import Path

from adeu_history_semantics import (
    ADEU_HISTORY_EVIDENCE_REF_SCHEMA,
    ADEU_HISTORY_LEDGER_ENTRY_SCHEMA,
    ADEU_HISTORY_LEDGER_SCHEMA,
    ADEU_HISTORY_ODEU_LANE_RECONSTRUCTION_SCHEMA,
    ADEU_HISTORY_ODEU_RECONSTRUCTION_PACKET_SCHEMA,
    ADEU_HISTORY_PRECLASSIFICATION_SCHEMA,
    ADEU_HISTORY_SLICE_SCHEMA,
    ADEU_HISTORY_SOURCE_ARTIFACT_SCHEMA,
    ADEU_HISTORY_TEXT_SHAPE_SIGNALS_SCHEMA,
    ADEU_HISTORY_THEME_ANCHOR_SCHEMA,
    ADEU_HISTORY_WORKSPACE_QUESTION_SCHEMA,
    ADEU_HISTORY_WORKSPACE_SNAPSHOT_SCHEMA,
    ADEU_HISTORY_WORKSPACE_THEME_FRAME_SCHEMA,
)
from adeu_history_semantics.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _schema_pairs() -> dict[str, tuple[Path, Path]]:
    root = repo_root(anchor=Path(__file__))
    return {
        ADEU_HISTORY_SOURCE_ARTIFACT_SCHEMA: (
            root
            / "packages"
            / "adeu_history_semantics"
            / "schema"
            / "adeu_history_source_artifact.v1.json",
            root / "spec" / "adeu_history_source_artifact.schema.json",
        ),
        ADEU_HISTORY_TEXT_SHAPE_SIGNALS_SCHEMA: (
            root
            / "packages"
            / "adeu_history_semantics"
            / "schema"
            / "adeu_history_text_shape_signals.v1.json",
            root / "spec" / "adeu_history_text_shape_signals.schema.json",
        ),
        ADEU_HISTORY_PRECLASSIFICATION_SCHEMA: (
            root
            / "packages"
            / "adeu_history_semantics"
            / "schema"
            / "adeu_history_preclassification.v1.json",
            root / "spec" / "adeu_history_preclassification.schema.json",
        ),
        ADEU_HISTORY_LEDGER_ENTRY_SCHEMA: (
            root
            / "packages"
            / "adeu_history_semantics"
            / "schema"
            / "adeu_history_ledger_entry.v1.json",
            root / "spec" / "adeu_history_ledger_entry.schema.json",
        ),
        ADEU_HISTORY_LEDGER_SCHEMA: (
            root
            / "packages"
            / "adeu_history_semantics"
            / "schema"
            / "adeu_history_ledger.v1.json",
            root / "spec" / "adeu_history_ledger.schema.json",
        ),
        ADEU_HISTORY_SLICE_SCHEMA: (
            root
            / "packages"
            / "adeu_history_semantics"
            / "schema"
            / "adeu_history_slice.v1.json",
            root / "spec" / "adeu_history_slice.schema.json",
        ),
        ADEU_HISTORY_THEME_ANCHOR_SCHEMA: (
            root
            / "packages"
            / "adeu_history_semantics"
            / "schema"
            / "adeu_history_theme_anchor.v1.json",
            root / "spec" / "adeu_history_theme_anchor.schema.json",
        ),
        ADEU_HISTORY_EVIDENCE_REF_SCHEMA: (
            root
            / "packages"
            / "adeu_history_semantics"
            / "schema"
            / "adeu_history_evidence_ref.v1.json",
            root / "spec" / "adeu_history_evidence_ref.schema.json",
        ),
        ADEU_HISTORY_ODEU_LANE_RECONSTRUCTION_SCHEMA: (
            root
            / "packages"
            / "adeu_history_semantics"
            / "schema"
            / "adeu_history_odeu_lane_reconstruction.v1.json",
            root / "spec" / "adeu_history_odeu_lane_reconstruction.schema.json",
        ),
        ADEU_HISTORY_ODEU_RECONSTRUCTION_PACKET_SCHEMA: (
            root
            / "packages"
            / "adeu_history_semantics"
            / "schema"
            / "adeu_history_odeu_reconstruction_packet.v1.json",
            root / "spec" / "adeu_history_odeu_reconstruction_packet.schema.json",
        ),
        ADEU_HISTORY_WORKSPACE_QUESTION_SCHEMA: (
            root
            / "packages"
            / "adeu_history_semantics"
            / "schema"
            / "adeu_history_workspace_question.v1.json",
            root / "spec" / "adeu_history_workspace_question.schema.json",
        ),
        ADEU_HISTORY_WORKSPACE_THEME_FRAME_SCHEMA: (
            root
            / "packages"
            / "adeu_history_semantics"
            / "schema"
            / "adeu_history_workspace_theme_frame.v1.json",
            root / "spec" / "adeu_history_workspace_theme_frame.schema.json",
        ),
        ADEU_HISTORY_WORKSPACE_SNAPSHOT_SCHEMA: (
            root
            / "packages"
            / "adeu_history_semantics"
            / "schema"
            / "adeu_history_workspace_snapshot.v1.json",
            root / "spec" / "adeu_history_workspace_snapshot.schema.json",
        ),
    }


def test_authoritative_and_mirror_schema_are_byte_identical() -> None:
    for authoritative, mirror in _schema_pairs().values():
        assert authoritative.read_bytes() == mirror.read_bytes()


def test_schema_export_rerun_is_clean_and_deterministic() -> None:
    pairs = _schema_pairs()
    before = {
        schema: (authoritative.read_bytes(), mirror.read_bytes())
        for schema, (authoritative, mirror) in pairs.items()
    }
    export_schema_main()
    after_first = {
        schema: (authoritative.read_bytes(), mirror.read_bytes())
        for schema, (authoritative, mirror) in pairs.items()
    }
    export_schema_main()
    after_second = {
        schema: (authoritative.read_bytes(), mirror.read_bytes())
        for schema, (authoritative, mirror) in pairs.items()
    }
    assert before == after_first == after_second


def test_exported_schema_has_stable_contract_markers() -> None:
    for expected_schema, (authoritative, _mirror) in _schema_pairs().items():
        payload = json.loads(authoritative.read_text(encoding="utf-8"))
        assert payload["properties"]["schema"]["const"] == expected_schema


def test_exported_schema_has_no_absolute_path_material() -> None:
    root = repo_root(anchor=Path(__file__))
    root_text = root.as_posix()

    def _check_node(node: object) -> None:
        if isinstance(node, dict):
            for value in node.values():
                _check_node(value)
            return
        if isinstance(node, list):
            for item in node:
                _check_node(item)
            return
        if not isinstance(node, str):
            return
        normalized = node.replace("\\", "/")
        assert root_text not in normalized
        assert not normalized.startswith("/home/")
        assert not normalized.startswith("/Users/")
        assert _WINDOWS_ABSOLUTE_PATH_RE.search(node) is None

    for authoritative, mirror in _schema_pairs().values():
        _check_node(json.loads(authoritative.read_text(encoding="utf-8")))
        _check_node(json.loads(mirror.read_text(encoding="utf-8")))
