from __future__ import annotations

import json
import re
from pathlib import Path

from adeu_ir.repo import repo_root
from adeu_obligation_broker import (
    REPO_HIERARCHICAL_OBLIGATION_CATALOG_SCHEMA,
    REPO_INHERITED_OBLIGATION_LEDGER_SCHEMA,
    REPO_OBLIGATION_ACTIVATION_ASSESSMENT_SCHEMA,
    REPO_OBLIGATION_BROKER_NON_AUTHORITY_GUARDRAIL_SCHEMA,
    REPO_OBLIGATION_TRAVERSAL_VALIDATION_REPORT_SCHEMA,
)
from adeu_obligation_broker.export_schema import main as export_schema_main

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\\\")


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _schema_paths() -> list[tuple[Path, Path]]:
    root = _repo_root()
    return [
        (
            root
            / "packages"
            / "adeu_obligation_broker"
            / "schema"
            / "repo_hierarchical_obligation_catalog.v1.json",
            root / "spec" / "repo_hierarchical_obligation_catalog.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_obligation_broker"
            / "schema"
            / "repo_obligation_activation_assessment.v1.json",
            root / "spec" / "repo_obligation_activation_assessment.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_obligation_broker"
            / "schema"
            / "repo_inherited_obligation_ledger.v1.json",
            root / "spec" / "repo_inherited_obligation_ledger.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_obligation_broker"
            / "schema"
            / "repo_obligation_traversal_validation_report.v1.json",
            root / "spec" / "repo_obligation_traversal_validation_report.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_obligation_broker"
            / "schema"
            / "repo_obligation_broker_non_authority_guardrail.v1.json",
            root / "spec" / "repo_obligation_broker_non_authority_guardrail.schema.json",
        ),
    ]


def test_authoritative_and_mirror_schema_are_byte_identical() -> None:
    export_schema_main()
    for authoritative, mirror in _schema_paths():
        assert authoritative.read_bytes() == mirror.read_bytes()


def test_schema_export_rerun_is_clean_and_deterministic() -> None:
    export_schema_main()
    before = [
        (authoritative.read_bytes(), mirror.read_bytes())
        for authoritative, mirror in _schema_paths()
    ]
    export_schema_main()
    after = [
        (authoritative.read_bytes(), mirror.read_bytes())
        for authoritative, mirror in _schema_paths()
    ]
    assert before == after


def test_exported_schema_has_stable_contract_markers() -> None:
    export_schema_main()
    expected_consts = {
        "repo_hierarchical_obligation_catalog.v1.json": (
            REPO_HIERARCHICAL_OBLIGATION_CATALOG_SCHEMA
        ),
        "repo_obligation_activation_assessment.v1.json": (
            REPO_OBLIGATION_ACTIVATION_ASSESSMENT_SCHEMA
        ),
        "repo_inherited_obligation_ledger.v1.json": REPO_INHERITED_OBLIGATION_LEDGER_SCHEMA,
        "repo_obligation_traversal_validation_report.v1.json": (
            REPO_OBLIGATION_TRAVERSAL_VALIDATION_REPORT_SCHEMA
        ),
        "repo_obligation_broker_non_authority_guardrail.v1.json": (
            REPO_OBLIGATION_BROKER_NON_AUTHORITY_GUARDRAIL_SCHEMA
        ),
    }
    for authoritative, _mirror in _schema_paths():
        payload = json.loads(authoritative.read_text(encoding="utf-8"))
        assert payload["properties"]["schema"]["const"] == expected_consts[authoritative.name]


def test_exported_schema_has_no_absolute_path_material() -> None:
    export_schema_main()
    root = _repo_root()
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

    for authoritative, mirror in _schema_paths():
        _check_node(json.loads(authoritative.read_text(encoding="utf-8")))
        _check_node(json.loads(mirror.read_text(encoding="utf-8")))
