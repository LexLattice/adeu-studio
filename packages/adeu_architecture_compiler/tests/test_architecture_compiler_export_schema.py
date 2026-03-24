from __future__ import annotations

import json
import re
from pathlib import Path

from adeu_architecture_compiler import ADEU_ARCHITECTURE_CONFORMANCE_REPORT_SCHEMA
from adeu_architecture_compiler.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\\\")


def _schema_paths() -> tuple[Path, Path]:
    root = repo_root(anchor=Path(__file__))
    return (
        root
        / "packages"
        / "adeu_architecture_compiler"
        / "schema"
        / "adeu_architecture_conformance_report.v1.json",
        root / "spec" / "adeu_architecture_conformance_report.schema.json",
    )


def test_authoritative_and_mirror_schema_are_byte_identical() -> None:
    authoritative, mirror = _schema_paths()
    assert authoritative.read_bytes() == mirror.read_bytes()


def test_schema_export_rerun_is_clean_and_deterministic() -> None:
    authoritative, mirror = _schema_paths()
    before = (authoritative.read_bytes(), mirror.read_bytes())
    export_schema_main()
    after_first = (authoritative.read_bytes(), mirror.read_bytes())
    export_schema_main()
    after_second = (authoritative.read_bytes(), mirror.read_bytes())
    assert before == after_first == after_second


def test_exported_schema_has_stable_contract_marker() -> None:
    authoritative, _mirror = _schema_paths()
    payload = json.loads(authoritative.read_text(encoding="utf-8"))
    assert payload["properties"]["schema"]["const"] == ADEU_ARCHITECTURE_CONFORMANCE_REPORT_SCHEMA


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

    authoritative, mirror = _schema_paths()
    _check_node(json.loads(authoritative.read_text(encoding="utf-8")))
    _check_node(json.loads(mirror.read_text(encoding="utf-8")))
