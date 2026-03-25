from __future__ import annotations

import json
import re
from pathlib import Path

from adeu_architecture_ir import (
    ADEU_ARCHITECTURE_ANALYSIS_REQUEST_SCHEMA,
    ADEU_ARCHITECTURE_BOUNDARY_GRAPH_SCHEMA,
    ADEU_ARCHITECTURE_INTENT_PACKET_SCHEMA,
    ADEU_ARCHITECTURE_ONTOLOGY_FRAME_SCHEMA,
    ADEU_ARCHITECTURE_SEMANTIC_IR_SCHEMA,
    ADEU_ARCHITECTURE_WORLD_HYPOTHESIS_SCHEMA,
)
from adeu_architecture_ir.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\\\")


def _schema_paths() -> list[tuple[Path, Path]]:
    root = repo_root(anchor=Path(__file__))
    return [
        (
            root
            / "packages"
            / "adeu_architecture_ir"
            / "schema"
            / "adeu_architecture_analysis_request.v1.json",
            root / "spec" / "adeu_architecture_analysis_request.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_architecture_ir"
            / "schema"
            / "adeu_architecture_intent_packet.v1.json",
            root / "spec" / "adeu_architecture_intent_packet.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_architecture_ir"
            / "schema"
            / "adeu_architecture_ontology_frame.v1.json",
            root / "spec" / "adeu_architecture_ontology_frame.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_architecture_ir"
            / "schema"
            / "adeu_architecture_boundary_graph.v1.json",
            root / "spec" / "adeu_architecture_boundary_graph.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_architecture_ir"
            / "schema"
            / "adeu_architecture_world_hypothesis.v1.json",
            root / "spec" / "adeu_architecture_world_hypothesis.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_architecture_ir"
            / "schema"
            / "adeu_architecture_semantic_ir.v1.json",
            root / "spec" / "adeu_architecture_semantic_ir.schema.json",
        ),
    ]


def test_authoritative_and_mirror_schema_are_byte_identical() -> None:
    for authoritative, mirror in _schema_paths():
        assert authoritative.read_bytes() == mirror.read_bytes()


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
        "adeu_architecture_analysis_request.v1.json": ADEU_ARCHITECTURE_ANALYSIS_REQUEST_SCHEMA,
        "adeu_architecture_intent_packet.v1.json": ADEU_ARCHITECTURE_INTENT_PACKET_SCHEMA,
        "adeu_architecture_ontology_frame.v1.json": ADEU_ARCHITECTURE_ONTOLOGY_FRAME_SCHEMA,
        "adeu_architecture_boundary_graph.v1.json": ADEU_ARCHITECTURE_BOUNDARY_GRAPH_SCHEMA,
        "adeu_architecture_world_hypothesis.v1.json": ADEU_ARCHITECTURE_WORLD_HYPOTHESIS_SCHEMA,
        "adeu_architecture_semantic_ir.v1.json": ADEU_ARCHITECTURE_SEMANTIC_IR_SCHEMA,
    }
    for authoritative, _mirror in _schema_paths():
        payload = json.loads(authoritative.read_text(encoding="utf-8"))
        assert payload["properties"]["schema"]["const"] == expected_consts[authoritative.name]


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

    for authoritative, mirror in _schema_paths():
        _check_node(json.loads(authoritative.read_text(encoding="utf-8")))
        _check_node(json.loads(mirror.read_text(encoding="utf-8")))
