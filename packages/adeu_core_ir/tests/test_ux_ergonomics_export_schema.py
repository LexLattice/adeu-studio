from __future__ import annotations

import json
import re
from pathlib import Path

from adeu_core_ir import (
    UX_COMPONENT_ERGONOMIC_REGISTRY_SCHEMA,
    UX_COMPONENT_VISIBILITY_CONTRACT_SCHEMA,
    UX_ERGONOMIC_ADJUDICATION_REQUEST_SCHEMA,
    UX_ERGONOMIC_ADJUDICATION_RESULT_SCHEMA,
    UX_ERGONOMIC_CANDIDATE_PROJECTION_PROFILE_TABLE_SCHEMA,
    UX_ERGONOMIC_CASE_ENVELOPE_SCHEMA,
    UX_ERGONOMIC_RULE_AUTHORITY_STACK_SCHEMA,
    UX_ERGONOMIC_RUNTIME_BRIDGE_REPORT_SCHEMA,
    UX_ERGONOMIC_RUNTIME_MEASUREMENT_EVIDENCE_SCHEMA,
)
from adeu_core_ir.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\\\")


def _schema_paths() -> list[tuple[Path, Path]]:
    root = repo_root(anchor=Path(__file__))
    return [
        (
            root
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / "ux_ergonomic_rule_authority_stack.v1.json",
            root / "spec" / "ux_ergonomic_rule_authority_stack.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / "ux_component_ergonomic_registry.v1.json",
            root / "spec" / "ux_component_ergonomic_registry.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / "ux_component_visibility_contract.v1.json",
            root / "spec" / "ux_component_visibility_contract.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / "ux_ergonomic_candidate_projection_profile_table.v1.json",
            root / "spec" / "ux_ergonomic_candidate_projection_profile_table.schema.json",
        ),
        (
            root / "packages" / "adeu_core_ir" / "schema" / "ux_ergonomic_case_envelope.v1.json",
            root / "spec" / "ux_ergonomic_case_envelope.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / "ux_ergonomic_adjudication_request.v1.json",
            root / "spec" / "ux_ergonomic_adjudication_request.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / "ux_ergonomic_adjudication_result.v1.json",
            root / "spec" / "ux_ergonomic_adjudication_result.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / "ux_ergonomic_runtime_measurement_evidence.v1.json",
            root / "spec" / "ux_ergonomic_runtime_measurement_evidence.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / "ux_ergonomic_runtime_bridge_report.v1.json",
            root / "spec" / "ux_ergonomic_runtime_bridge_report.schema.json",
        ),
    ]


def test_v67a_authoritative_and_mirror_schema_files_are_byte_identical() -> None:
    for authoritative, mirror in _schema_paths():
        assert authoritative.read_bytes() == mirror.read_bytes()


def test_v67a_schema_export_rerun_is_clean_and_deterministic() -> None:
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


def test_v67a_exported_schema_files_have_stable_contract_markers() -> None:
    expected_consts = {
        "ux_ergonomic_rule_authority_stack.v1.json": UX_ERGONOMIC_RULE_AUTHORITY_STACK_SCHEMA,
        "ux_component_ergonomic_registry.v1.json": UX_COMPONENT_ERGONOMIC_REGISTRY_SCHEMA,
        "ux_component_visibility_contract.v1.json": UX_COMPONENT_VISIBILITY_CONTRACT_SCHEMA,
        "ux_ergonomic_candidate_projection_profile_table.v1.json": (
            UX_ERGONOMIC_CANDIDATE_PROJECTION_PROFILE_TABLE_SCHEMA
        ),
        "ux_ergonomic_case_envelope.v1.json": UX_ERGONOMIC_CASE_ENVELOPE_SCHEMA,
        "ux_ergonomic_adjudication_request.v1.json": UX_ERGONOMIC_ADJUDICATION_REQUEST_SCHEMA,
        "ux_ergonomic_adjudication_result.v1.json": UX_ERGONOMIC_ADJUDICATION_RESULT_SCHEMA,
        "ux_ergonomic_runtime_measurement_evidence.v1.json": (
            UX_ERGONOMIC_RUNTIME_MEASUREMENT_EVIDENCE_SCHEMA
        ),
        "ux_ergonomic_runtime_bridge_report.v1.json": UX_ERGONOMIC_RUNTIME_BRIDGE_REPORT_SCHEMA,
    }

    for authoritative, _mirror in _schema_paths():
        payload = json.loads(authoritative.read_text(encoding="utf-8"))
        assert payload["properties"]["schema"]["const"] == expected_consts[authoritative.name]


def test_v67a_exported_schema_files_have_no_absolute_path_material() -> None:
    root = repo_root(anchor=Path(__file__))
    root_text = root.as_posix()

    def _check_node(node: object) -> None:
        if isinstance(node, dict):
            for key in sorted(node):
                _check_node(node[key])
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
        for path in (authoritative, mirror):
            payload = json.loads(path.read_text(encoding="utf-8"))
            _check_node(payload)
