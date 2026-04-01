from __future__ import annotations

import json
import re
from pathlib import Path

from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_ARC_DEPENDENCY_REGISTER_SCHEMA,
    REPO_ARC_DEPENDENCY_REGISTER_V1_SCHEMA,
    REPO_DEPENDENCY_GRAPH_SCHEMA,
    REPO_ENTITY_CATALOG_SCHEMA,
    REPO_SCHEMA_FAMILY_REGISTRY_SCHEMA,
    REPO_SYMBOL_CATALOG_SCHEMA,
    REPO_TEST_INTENT_MATRIX_SCHEMA,
)
from adeu_repo_description.export_schema import main as export_schema_main

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _schema_pairs() -> dict[str, tuple[Path, Path]]:
    root = repo_root(anchor=Path(__file__))
    return {
        REPO_ARC_DEPENDENCY_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_arc_dependency_register.v2.json",
            root / "spec" / "repo_arc_dependency_register.schema.json",
        ),
        REPO_DEPENDENCY_GRAPH_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_dependency_graph.v1.json",
            root / "spec" / "repo_dependency_graph.schema.json",
        ),
        REPO_SCHEMA_FAMILY_REGISTRY_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_schema_family_registry.v1.json",
            root / "spec" / "repo_schema_family_registry.schema.json",
        ),
        REPO_ENTITY_CATALOG_SCHEMA: (
            root / "packages" / "adeu_repo_description" / "schema" / "repo_entity_catalog.v1.json",
            root / "spec" / "repo_entity_catalog.schema.json",
        ),
        REPO_SYMBOL_CATALOG_SCHEMA: (
            root / "packages" / "adeu_repo_description" / "schema" / "repo_symbol_catalog.v1.json",
            root / "spec" / "repo_symbol_catalog.schema.json",
        ),
        REPO_TEST_INTENT_MATRIX_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_test_intent_matrix.v1.json",
            root / "spec" / "repo_test_intent_matrix.schema.json",
        ),
    }


def _historical_schema_paths() -> dict[str, Path]:
    root = repo_root(anchor=Path(__file__))
    return {
        REPO_ARC_DEPENDENCY_REGISTER_V1_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_arc_dependency_register.v1.json"
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
    for expected_schema, authoritative in _historical_schema_paths().items():
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
    for authoritative in _historical_schema_paths().values():
        _check_node(json.loads(authoritative.read_text(encoding="utf-8")))
