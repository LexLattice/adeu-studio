from __future__ import annotations

import json
import re
from pathlib import Path

from adeu_edge_ledger import (
    ADEU_EDGE_CLASS_CATALOG_SCHEMA,
    ADEU_EDGE_PROBE_TEMPLATE_CATALOG_SCHEMA,
    ADEU_SYMBOL_EDGE_ADJUDICATION_LEDGER_SCHEMA,
    ADEU_SYMBOL_EDGE_APPLICABILITY_FRAME_SCHEMA,
)
from adeu_edge_ledger.export_schema import _assert_no_absolute_path_material
from adeu_edge_ledger.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\\\")


def _schema_paths() -> list[tuple[Path, Path]]:
    root = repo_root(anchor=Path(__file__))
    return [
        (
            root / "packages" / "adeu_edge_ledger" / "schema" / "adeu_edge_class_catalog.v1.json",
            root / "spec" / "adeu_edge_class_catalog.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_edge_ledger"
            / "schema"
            / "adeu_edge_probe_template_catalog.v1.json",
            root / "spec" / "adeu_edge_probe_template_catalog.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_edge_ledger"
            / "schema"
            / "adeu_symbol_edge_applicability_frame.v1.json",
            root / "spec" / "adeu_symbol_edge_applicability_frame.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_edge_ledger"
            / "schema"
            / "adeu_symbol_edge_adjudication_ledger.v1.json",
            root / "spec" / "adeu_symbol_edge_adjudication_ledger.schema.json",
        ),
    ]


def test_exported_schemas_are_valid_and_mirrored() -> None:
    for authoritative, mirror in _schema_paths():
        authoritative_payload = json.loads(authoritative.read_text(encoding="utf-8"))
        mirror_payload = json.loads(mirror.read_text(encoding="utf-8"))
        Draft202012Validator.check_schema(authoritative_payload)
        Draft202012Validator.check_schema(mirror_payload)
        assert authoritative_payload == mirror_payload


def test_schema_export_rerun_is_clean_and_deterministic() -> None:
    before = [
        (authoritative.read_bytes(), mirror.read_bytes())
        for authoritative, mirror in _schema_paths()
    ]
    export_schema_main()
    after_first = [
        (authoritative.read_bytes(), mirror.read_bytes())
        for authoritative, mirror in _schema_paths()
    ]
    export_schema_main()
    after_second = [
        (authoritative.read_bytes(), mirror.read_bytes())
        for authoritative, mirror in _schema_paths()
    ]
    assert before == after_first == after_second


def test_exported_schema_has_stable_contract_markers() -> None:
    expected_consts = {
        "adeu_edge_class_catalog.v1.json": ADEU_EDGE_CLASS_CATALOG_SCHEMA,
        "adeu_edge_probe_template_catalog.v1.json": ADEU_EDGE_PROBE_TEMPLATE_CATALOG_SCHEMA,
        "adeu_symbol_edge_applicability_frame.v1.json": ADEU_SYMBOL_EDGE_APPLICABILITY_FRAME_SCHEMA,
        "adeu_symbol_edge_adjudication_ledger.v1.json": ADEU_SYMBOL_EDGE_ADJUDICATION_LEDGER_SCHEMA,
    }
    for authoritative, _mirror in _schema_paths():
        payload = json.loads(authoritative.read_text(encoding="utf-8"))
        assert payload["properties"]["schema"]["const"] == expected_consts[authoritative.name]


def test_exported_schema_has_no_absolute_path_material() -> None:
    root = repo_root(anchor=Path(__file__))

    for authoritative, mirror in _schema_paths():
        authoritative_payload = json.loads(authoritative.read_text(encoding="utf-8"))
        mirror_payload = json.loads(mirror.read_text(encoding="utf-8"))
        _assert_no_absolute_path_material(authoritative_payload, repo_root_path=root)
        _assert_no_absolute_path_material(mirror_payload, repo_root_path=root)
        serialized = authoritative.read_text(encoding="utf-8") + mirror.read_text(encoding="utf-8")
        assert root.as_posix() not in serialized.replace("\\", "/")
        assert _WINDOWS_ABSOLUTE_PATH_RE.search(serialized) is None
