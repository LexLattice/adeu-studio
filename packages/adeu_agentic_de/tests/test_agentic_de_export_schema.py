from __future__ import annotations

import json
from pathlib import Path

from adeu_agentic_de import (
    AGENTIC_DE_ACTION_CLASS_TAXONOMY_SCHEMA,
    AGENTIC_DE_ACTION_PROPOSAL_SCHEMA,
    AGENTIC_DE_ACTION_TICKET_SCHEMA,
    AGENTIC_DE_CONFORMANCE_REPORT_SCHEMA,
    AGENTIC_DE_DOMAIN_PACKET_SCHEMA,
    AGENTIC_DE_GOVERNANCE_CALIBRATION_REGISTER_SCHEMA,
    AGENTIC_DE_INTERACTION_CONTRACT_SCHEMA,
    AGENTIC_DE_LANE_DRIFT_RECORD_SCHEMA,
    AGENTIC_DE_MEMBRANE_CHECKPOINT_SCHEMA,
    AGENTIC_DE_MIGRATION_DECISION_REGISTER_SCHEMA,
    AGENTIC_DE_MORPH_DIAGNOSTICS_SCHEMA,
    AGENTIC_DE_MORPH_IR_SCHEMA,
    AGENTIC_DE_RUNTIME_HARVEST_RECORD_SCHEMA,
    AGENTIC_DE_RUNTIME_STATE_SCHEMA,
)
from adeu_agentic_de.export_schema import _assert_no_absolute_path_material
from adeu_agentic_de.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root


def _schema_pairs() -> dict[str, tuple[Path, Path]]:
    root = repo_root(anchor=Path(__file__))
    return {
        AGENTIC_DE_DOMAIN_PACKET_SCHEMA: (
            root / "packages" / "adeu_agentic_de" / "schema" / "agentic_de_domain_packet.v1.json",
            root / "spec" / "agentic_de_domain_packet.schema.json",
        ),
        AGENTIC_DE_MORPH_IR_SCHEMA: (
            root / "packages" / "adeu_agentic_de" / "schema" / "agentic_de_morph_ir.v1.json",
            root / "spec" / "agentic_de_morph_ir.schema.json",
        ),
        AGENTIC_DE_INTERACTION_CONTRACT_SCHEMA: (
            root
            / "packages"
            / "adeu_agentic_de"
            / "schema"
            / "agentic_de_interaction_contract.v1.json",
            root / "spec" / "agentic_de_interaction_contract.schema.json",
        ),
        AGENTIC_DE_ACTION_PROPOSAL_SCHEMA: (
            root / "packages" / "adeu_agentic_de" / "schema" / "agentic_de_action_proposal.v1.json",
            root / "spec" / "agentic_de_action_proposal.schema.json",
        ),
        AGENTIC_DE_ACTION_CLASS_TAXONOMY_SCHEMA: (
            root
            / "packages"
            / "adeu_agentic_de"
            / "schema"
            / "agentic_de_action_class_taxonomy.v1.json",
            root / "spec" / "agentic_de_action_class_taxonomy.schema.json",
        ),
        AGENTIC_DE_MEMBRANE_CHECKPOINT_SCHEMA: (
            root
            / "packages"
            / "adeu_agentic_de"
            / "schema"
            / "agentic_de_membrane_checkpoint.v1.json",
            root / "spec" / "agentic_de_membrane_checkpoint.schema.json",
        ),
        AGENTIC_DE_MORPH_DIAGNOSTICS_SCHEMA: (
            root
            / "packages"
            / "adeu_agentic_de"
            / "schema"
            / "agentic_de_morph_diagnostics.v1.json",
            root / "spec" / "agentic_de_morph_diagnostics.schema.json",
        ),
        AGENTIC_DE_CONFORMANCE_REPORT_SCHEMA: (
            root
            / "packages"
            / "adeu_agentic_de"
            / "schema"
            / "agentic_de_conformance_report.v1.json",
            root / "spec" / "agentic_de_conformance_report.schema.json",
        ),
        AGENTIC_DE_RUNTIME_STATE_SCHEMA: (
            root / "packages" / "adeu_agentic_de" / "schema" / "agentic_de_runtime_state.v1.json",
            root / "spec" / "agentic_de_runtime_state.schema.json",
        ),
        AGENTIC_DE_ACTION_TICKET_SCHEMA: (
            root / "packages" / "adeu_agentic_de" / "schema" / "agentic_de_action_ticket.v1.json",
            root / "spec" / "agentic_de_action_ticket.schema.json",
        ),
        AGENTIC_DE_LANE_DRIFT_RECORD_SCHEMA: (
            root
            / "packages"
            / "adeu_agentic_de"
            / "schema"
            / "agentic_de_lane_drift_record.v1.json",
            root / "spec" / "agentic_de_lane_drift_record.schema.json",
        ),
        AGENTIC_DE_RUNTIME_HARVEST_RECORD_SCHEMA: (
            root
            / "packages"
            / "adeu_agentic_de"
            / "schema"
            / "agentic_de_runtime_harvest_record.v1.json",
            root / "spec" / "agentic_de_runtime_harvest_record.schema.json",
        ),
        AGENTIC_DE_GOVERNANCE_CALIBRATION_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_agentic_de"
            / "schema"
            / "agentic_de_governance_calibration_register.v1.json",
            root / "spec" / "agentic_de_governance_calibration_register.schema.json",
        ),
        AGENTIC_DE_MIGRATION_DECISION_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_agentic_de"
            / "schema"
            / "agentic_de_migration_decision_register.v1.json",
            root / "spec" / "agentic_de_migration_decision_register.schema.json",
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
    for authoritative, mirror in _schema_pairs().values():
        _assert_no_absolute_path_material(
            json.loads(authoritative.read_text(encoding="utf-8")),
            repo_root_path=root,
        )
        _assert_no_absolute_path_material(
            json.loads(mirror.read_text(encoding="utf-8")),
            repo_root_path=root,
        )
