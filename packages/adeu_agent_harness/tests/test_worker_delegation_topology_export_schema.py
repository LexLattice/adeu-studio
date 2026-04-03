from __future__ import annotations

import json
from pathlib import Path

from adeu_agent_harness.export_schema import main as export_schema_main
from adeu_agent_harness.worker_delegation_topology import (
    WORKER_DELEGATION_TOPOLOGY_SCHEMA,
)
from adeu_ir.repo import repo_root


def _schema_pair() -> tuple[Path, Path]:
    root = repo_root(anchor=Path(__file__))
    return (
        root
        / "packages"
        / "adeu_agent_harness"
        / "schema"
        / "worker_delegation_topology.v1.json",
        root / "spec" / "worker_delegation_topology.schema.json",
    )


def test_authoritative_and_mirror_schema_are_byte_identical() -> None:
    authoritative, mirror = _schema_pair()
    assert authoritative.read_bytes() == mirror.read_bytes()


def test_schema_export_rerun_is_clean_and_deterministic() -> None:
    authoritative, mirror = _schema_pair()
    before = {
        authoritative: authoritative.read_bytes(),
        mirror: mirror.read_bytes(),
    }

    export_schema_main()
    after_first = {path: path.read_bytes() for path in before}

    export_schema_main()
    after_second = {path: path.read_bytes() for path in before}

    assert before == after_first == after_second


def test_exported_schema_has_stable_contract_markers() -> None:
    authoritative, _ = _schema_pair()
    schema_payload = json.loads(authoritative.read_text(encoding="utf-8"))

    assert schema_payload["properties"]["schema"]["const"] == WORKER_DELEGATION_TOPOLOGY_SCHEMA
    assert schema_payload["properties"]["delegation_edge_kind"]["const"] == (
        "supervisor_to_worker"
    )
    assert schema_payload["properties"]["topology_scope_posture"]["const"] == (
        "one_parent_one_child_one_edge_only"
    )
    assert schema_payload["properties"]["authority_relation_posture"]["const"] == (
        "same_compiled_boundary_no_widening"
    )
    assert schema_payload["properties"]["handoff_result"]["enum"] == [
        "completed",
        "rejected",
        "incomplete_lineage",
    ]
