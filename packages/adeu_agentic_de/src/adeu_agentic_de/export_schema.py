from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from adeu_ir.repo import repo_root

from .models import (
    AGENTIC_DE_ACTION_CLASS_TAXONOMY_SCHEMA,
    AGENTIC_DE_ACTION_PROPOSAL_SCHEMA,
    AGENTIC_DE_ACTION_TICKET_SCHEMA,
    AGENTIC_DE_CONFORMANCE_REPORT_SCHEMA,
    AGENTIC_DE_DOMAIN_PACKET_SCHEMA,
    AGENTIC_DE_INTERACTION_CONTRACT_SCHEMA,
    AGENTIC_DE_LANE_DRIFT_RECORD_SCHEMA,
    AGENTIC_DE_MEMBRANE_CHECKPOINT_SCHEMA,
    AGENTIC_DE_MORPH_DIAGNOSTICS_SCHEMA,
    AGENTIC_DE_MORPH_IR_SCHEMA,
    AGENTIC_DE_RUNTIME_STATE_SCHEMA,
    AgenticDeActionClassTaxonomy,
    AgenticDeActionProposal,
    AgenticDeActionTicket,
    AgenticDeConformanceReport,
    AgenticDeDomainPacket,
    AgenticDeInteractionContract,
    AgenticDeLaneDriftRecord,
    AgenticDeMembraneCheckpoint,
    AgenticDeMorphDiagnostics,
    AgenticDeMorphIr,
    AgenticDeRuntimeState,
)

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _write_schema(path: Path, schema: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(schema, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _assert_no_absolute_path_material(
    value: Any,
    *,
    repo_root_path: Path,
    node_path: str = "$",
) -> None:
    if isinstance(value, dict):
        for key in sorted(value):
            _assert_no_absolute_path_material(
                value[key],
                repo_root_path=repo_root_path,
                node_path=f"{node_path}.{key}",
            )
        return
    if isinstance(value, list):
        for index, item in enumerate(value):
            _assert_no_absolute_path_material(
                item,
                repo_root_path=repo_root_path,
                node_path=f"{node_path}[{index}]",
            )
        return
    if not isinstance(value, str):
        return
    normalized = value.replace("\\", "/")
    root_text = repo_root_path.as_posix()
    if root_text in normalized:
        raise RuntimeError(
            f"schema export contains repository absolute path material at {node_path}: {value!r}"
        )
    if _WINDOWS_ABSOLUTE_PATH_RE.search(value):
        raise RuntimeError(
            f"schema export contains Windows absolute path material at {node_path}: {value!r}"
        )
    if normalized.startswith("/home/") or normalized.startswith("/Users/"):
        raise RuntimeError(
            f"schema export contains user-home absolute path material at {node_path}: {value!r}"
        )


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    schema_outputs = [
        (
            AgenticDeDomainPacket,
            AGENTIC_DE_DOMAIN_PACKET_SCHEMA,
            root / "packages" / "adeu_agentic_de" / "schema" / "agentic_de_domain_packet.v1.json",
            root / "spec" / "agentic_de_domain_packet.schema.json",
        ),
        (
            AgenticDeMorphIr,
            AGENTIC_DE_MORPH_IR_SCHEMA,
            root / "packages" / "adeu_agentic_de" / "schema" / "agentic_de_morph_ir.v1.json",
            root / "spec" / "agentic_de_morph_ir.schema.json",
        ),
        (
            AgenticDeInteractionContract,
            AGENTIC_DE_INTERACTION_CONTRACT_SCHEMA,
            root
            / "packages"
            / "adeu_agentic_de"
            / "schema"
            / "agentic_de_interaction_contract.v1.json",
            root / "spec" / "agentic_de_interaction_contract.schema.json",
        ),
        (
            AgenticDeActionProposal,
            AGENTIC_DE_ACTION_PROPOSAL_SCHEMA,
            root / "packages" / "adeu_agentic_de" / "schema" / "agentic_de_action_proposal.v1.json",
            root / "spec" / "agentic_de_action_proposal.schema.json",
        ),
        (
            AgenticDeActionClassTaxonomy,
            AGENTIC_DE_ACTION_CLASS_TAXONOMY_SCHEMA,
            root
            / "packages"
            / "adeu_agentic_de"
            / "schema"
            / "agentic_de_action_class_taxonomy.v1.json",
            root / "spec" / "agentic_de_action_class_taxonomy.schema.json",
        ),
        (
            AgenticDeMembraneCheckpoint,
            AGENTIC_DE_MEMBRANE_CHECKPOINT_SCHEMA,
            root
            / "packages"
            / "adeu_agentic_de"
            / "schema"
            / "agentic_de_membrane_checkpoint.v1.json",
            root / "spec" / "agentic_de_membrane_checkpoint.schema.json",
        ),
        (
            AgenticDeMorphDiagnostics,
            AGENTIC_DE_MORPH_DIAGNOSTICS_SCHEMA,
            root
            / "packages"
            / "adeu_agentic_de"
            / "schema"
            / "agentic_de_morph_diagnostics.v1.json",
            root / "spec" / "agentic_de_morph_diagnostics.schema.json",
        ),
        (
            AgenticDeConformanceReport,
            AGENTIC_DE_CONFORMANCE_REPORT_SCHEMA,
            root
            / "packages"
            / "adeu_agentic_de"
            / "schema"
            / "agentic_de_conformance_report.v1.json",
            root / "spec" / "agentic_de_conformance_report.schema.json",
        ),
        (
            AgenticDeRuntimeState,
            AGENTIC_DE_RUNTIME_STATE_SCHEMA,
            root / "packages" / "adeu_agentic_de" / "schema" / "agentic_de_runtime_state.v1.json",
            root / "spec" / "agentic_de_runtime_state.schema.json",
        ),
        (
            AgenticDeActionTicket,
            AGENTIC_DE_ACTION_TICKET_SCHEMA,
            root / "packages" / "adeu_agentic_de" / "schema" / "agentic_de_action_ticket.v1.json",
            root / "spec" / "agentic_de_action_ticket.schema.json",
        ),
        (
            AgenticDeLaneDriftRecord,
            AGENTIC_DE_LANE_DRIFT_RECORD_SCHEMA,
            root
            / "packages"
            / "adeu_agentic_de"
            / "schema"
            / "agentic_de_lane_drift_record.v1.json",
            root / "spec" / "agentic_de_lane_drift_record.schema.json",
        ),
    ]

    for model, expected_schema, authoritative_path, mirror_path in schema_outputs:
        schema = model.model_json_schema(by_alias=True)
        if schema["properties"]["schema"]["const"] != expected_schema:
            raise RuntimeError(f"schema marker drift for {expected_schema}")
        _assert_no_absolute_path_material(schema, repo_root_path=root)
        _write_schema(authoritative_path, schema)
        _write_schema(mirror_path, schema)


if __name__ == "__main__":
    main()
