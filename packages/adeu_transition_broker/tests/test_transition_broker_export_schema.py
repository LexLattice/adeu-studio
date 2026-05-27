from __future__ import annotations

import json
import re
from pathlib import Path

from adeu_ir.repo import repo_root
from adeu_transition_broker import (
    REPO_PHASE_BRIDGE_CONTRACT_SCHEMA,
    REPO_PHASE_CIRCUIT_CATALOG_SCHEMA,
    REPO_PHASE_EVIDENCE_POSTURE_PLAN_SCHEMA,
    REPO_PHASE_GATE_EXECUTION_PLAN_SCHEMA,
    REPO_PHASE_LEGAL_FRONTIER_REPORT_SCHEMA,
    REPO_PHASE_OPERATIONALIZATION_REPORT_SCHEMA,
    REPO_PHASE_TRANSITION_CLAIM_SCHEMA,
    REPO_PHASE_TRANSITION_CLOSURE_REPORT_SCHEMA,
    REPO_PHASE_TRANSITION_VALIDATION_REPORT_SCHEMA,
    REPO_PHASE_WORKER_BATON_CONTRACT_SCHEMA,
    REPO_TRANSITION_BROKER_NON_AUTHORITY_GUARDRAIL_SCHEMA,
)
from adeu_transition_broker.export_schema import main as export_schema_main

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\\\")


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _schema_paths() -> list[tuple[Path, Path]]:
    root = _repo_root()
    return [
        (
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_circuit_catalog.v1.json",
            root / "spec" / "repo_phase_circuit_catalog.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_bridge_contract.v1.json",
            root / "spec" / "repo_phase_bridge_contract.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_transition_claim.v1.json",
            root / "spec" / "repo_phase_transition_claim.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_transition_validation_report.v1.json",
            root / "spec" / "repo_phase_transition_validation_report.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_legal_frontier_report.v1.json",
            root / "spec" / "repo_phase_legal_frontier_report.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_transition_broker_non_authority_guardrail.v1.json",
            root / "spec" / "repo_transition_broker_non_authority_guardrail.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_transition_closure_report.v1.json",
            root / "spec" / "repo_phase_transition_closure_report.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_gate_execution_plan.v1.json",
            root / "spec" / "repo_phase_gate_execution_plan.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_worker_baton_contract.v1.json",
            root / "spec" / "repo_phase_worker_baton_contract.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_evidence_posture_plan.v1.json",
            root / "spec" / "repo_phase_evidence_posture_plan.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_operationalization_report.v1.json",
            root / "spec" / "repo_phase_operationalization_report.schema.json",
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
        "repo_phase_circuit_catalog.v1.json": REPO_PHASE_CIRCUIT_CATALOG_SCHEMA,
        "repo_phase_bridge_contract.v1.json": REPO_PHASE_BRIDGE_CONTRACT_SCHEMA,
        "repo_phase_transition_claim.v1.json": REPO_PHASE_TRANSITION_CLAIM_SCHEMA,
        "repo_phase_transition_validation_report.v1.json": (
            REPO_PHASE_TRANSITION_VALIDATION_REPORT_SCHEMA
        ),
        "repo_phase_legal_frontier_report.v1.json": REPO_PHASE_LEGAL_FRONTIER_REPORT_SCHEMA,
        "repo_transition_broker_non_authority_guardrail.v1.json": (
            REPO_TRANSITION_BROKER_NON_AUTHORITY_GUARDRAIL_SCHEMA
        ),
        "repo_phase_transition_closure_report.v1.json": (
            REPO_PHASE_TRANSITION_CLOSURE_REPORT_SCHEMA
        ),
        "repo_phase_gate_execution_plan.v1.json": REPO_PHASE_GATE_EXECUTION_PLAN_SCHEMA,
        "repo_phase_worker_baton_contract.v1.json": REPO_PHASE_WORKER_BATON_CONTRACT_SCHEMA,
        "repo_phase_evidence_posture_plan.v1.json": REPO_PHASE_EVIDENCE_POSTURE_PLAN_SCHEMA,
        "repo_phase_operationalization_report.v1.json": (
            REPO_PHASE_OPERATIONALIZATION_REPORT_SCHEMA
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
