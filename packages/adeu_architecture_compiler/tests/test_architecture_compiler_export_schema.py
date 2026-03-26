from __future__ import annotations

import json
import re
from pathlib import Path

from adeu_architecture_compiler import (
    ADEU_ARCHITECTURE_CHECKPOINT_TRACE_SCHEMA,
    ADEU_ARCHITECTURE_CONFORMANCE_REPORT_SCHEMA,
    ADEU_ARCHITECTURE_IR_DELTA_SCHEMA,
    ADEU_ARCHITECTURE_OBSERVATION_FRAME_SCHEMA,
    ADEU_ARCHITECTURE_ORACLE_REQUEST_SCHEMA,
    ADEU_ARCHITECTURE_ORACLE_RESOLUTION_SCHEMA,
    ADEU_ARCHITECTURE_PROJECTION_BUNDLE_SCHEMA,
    ADEU_ARCHITECTURE_PROJECTION_MANIFEST_SCHEMA,
    V40F_ARCHITECTURE_RELEASE_INTEGRATION_EVIDENCE_SCHEMA,
)
from adeu_architecture_compiler.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\\\")
_SCHEMA_TARGETS = (
    (
        ADEU_ARCHITECTURE_CONFORMANCE_REPORT_SCHEMA,
        "adeu_architecture_conformance_report.v1.json",
        "adeu_architecture_conformance_report.schema.json",
    ),
    (
        ADEU_ARCHITECTURE_ORACLE_REQUEST_SCHEMA,
        "adeu_architecture_oracle_request.v1.json",
        "adeu_architecture_oracle_request.schema.json",
    ),
    (
        ADEU_ARCHITECTURE_ORACLE_RESOLUTION_SCHEMA,
        "adeu_architecture_oracle_resolution.v1.json",
        "adeu_architecture_oracle_resolution.schema.json",
    ),
    (
        ADEU_ARCHITECTURE_CHECKPOINT_TRACE_SCHEMA,
        "adeu_architecture_checkpoint_trace.v1.json",
        "adeu_architecture_checkpoint_trace.schema.json",
    ),
    (
        ADEU_ARCHITECTURE_OBSERVATION_FRAME_SCHEMA,
        "adeu_architecture_observation_frame.v1.json",
        "adeu_architecture_observation_frame.schema.json",
    ),
    (
        ADEU_ARCHITECTURE_IR_DELTA_SCHEMA,
        "adeu_architecture_ir_delta.v1.json",
        "adeu_architecture_ir_delta.schema.json",
    ),
    (
        ADEU_ARCHITECTURE_PROJECTION_BUNDLE_SCHEMA,
        "adeu_architecture_projection_bundle.v1.json",
        "adeu_architecture_projection_bundle.schema.json",
    ),
    (
        ADEU_ARCHITECTURE_PROJECTION_MANIFEST_SCHEMA,
        "adeu_architecture_projection_manifest.v1.json",
        "adeu_architecture_projection_manifest.schema.json",
    ),
    (
        V40F_ARCHITECTURE_RELEASE_INTEGRATION_EVIDENCE_SCHEMA,
        "v40f_architecture_release_integration_evidence.v1.json",
        "v40f_architecture_release_integration_evidence.schema.json",
    ),
)


def _schema_paths() -> list[tuple[str, Path, Path]]:
    root = repo_root(anchor=Path(__file__))
    return [
        (
            schema_marker,
            root / "packages" / "adeu_architecture_compiler" / "schema" / authoritative_name,
            root / "spec" / mirror_name,
        )
        for schema_marker, authoritative_name, mirror_name in _SCHEMA_TARGETS
    ]


def test_authoritative_and_mirror_schemas_are_byte_identical() -> None:
    for _marker, authoritative, mirror in _schema_paths():
        assert authoritative.read_bytes() == mirror.read_bytes()


def test_schema_export_rerun_is_clean_and_deterministic() -> None:
    before = [
        (authoritative.read_bytes(), mirror.read_bytes())
        for _, authoritative, mirror in _schema_paths()
    ]
    export_schema_main()
    after_first = [
        (authoritative.read_bytes(), mirror.read_bytes())
        for _, authoritative, mirror in _schema_paths()
    ]
    export_schema_main()
    after_second = [
        (authoritative.read_bytes(), mirror.read_bytes())
        for _, authoritative, mirror in _schema_paths()
    ]
    assert before == after_first == after_second


def test_exported_schemas_have_stable_contract_markers() -> None:
    for marker, authoritative, _mirror in _schema_paths():
        payload = json.loads(authoritative.read_text(encoding="utf-8"))
        assert payload["properties"]["schema"]["const"] == marker


def test_exported_schemas_have_no_absolute_path_material() -> None:
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

    for _marker, authoritative, mirror in _schema_paths():
        _check_node(json.loads(authoritative.read_text(encoding="utf-8")))
        _check_node(json.loads(mirror.read_text(encoding="utf-8")))
