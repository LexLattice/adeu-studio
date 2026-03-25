from __future__ import annotations

import json
from pathlib import Path

from adeu_ir.repo import repo_root

from .analysis_request import (
    ADEU_ARCHITECTURE_ANALYSIS_REQUEST_SCHEMA,
    AdeuArchitectureAnalysisRequest,
)
from .root_family import (
    ADEU_ARCHITECTURE_BOUNDARY_GRAPH_SCHEMA,
    ADEU_ARCHITECTURE_INTENT_PACKET_SCHEMA,
    ADEU_ARCHITECTURE_ONTOLOGY_FRAME_SCHEMA,
    ADEU_ARCHITECTURE_SEMANTIC_IR_SCHEMA,
    ADEU_ARCHITECTURE_WORLD_HYPOTHESIS_SCHEMA,
    AdeuArchitectureSemanticIR,
    ArchitectureBoundaryGraph,
    ArchitectureIntentPacket,
    ArchitectureOntologyFrame,
    ArchitectureWorldHypothesis,
)


def _write_schema(path: Path, schema: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(schema, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    mappings = [
        (
            AdeuArchitectureAnalysisRequest.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_architecture_ir"
            / "schema"
            / "adeu_architecture_analysis_request.v1.json",
            root / "spec" / "adeu_architecture_analysis_request.schema.json",
            ADEU_ARCHITECTURE_ANALYSIS_REQUEST_SCHEMA,
        ),
        (
            ArchitectureIntentPacket.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_architecture_ir"
            / "schema"
            / "adeu_architecture_intent_packet.v1.json",
            root / "spec" / "adeu_architecture_intent_packet.schema.json",
            ADEU_ARCHITECTURE_INTENT_PACKET_SCHEMA,
        ),
        (
            ArchitectureOntologyFrame.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_architecture_ir"
            / "schema"
            / "adeu_architecture_ontology_frame.v1.json",
            root / "spec" / "adeu_architecture_ontology_frame.schema.json",
            ADEU_ARCHITECTURE_ONTOLOGY_FRAME_SCHEMA,
        ),
        (
            ArchitectureBoundaryGraph.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_architecture_ir"
            / "schema"
            / "adeu_architecture_boundary_graph.v1.json",
            root / "spec" / "adeu_architecture_boundary_graph.schema.json",
            ADEU_ARCHITECTURE_BOUNDARY_GRAPH_SCHEMA,
        ),
        (
            ArchitectureWorldHypothesis.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_architecture_ir"
            / "schema"
            / "adeu_architecture_world_hypothesis.v1.json",
            root / "spec" / "adeu_architecture_world_hypothesis.schema.json",
            ADEU_ARCHITECTURE_WORLD_HYPOTHESIS_SCHEMA,
        ),
        (
            AdeuArchitectureSemanticIR.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_architecture_ir"
            / "schema"
            / "adeu_architecture_semantic_ir.v1.json",
            root / "spec" / "adeu_architecture_semantic_ir.schema.json",
            ADEU_ARCHITECTURE_SEMANTIC_IR_SCHEMA,
        ),
    ]
    for schema, authoritative_path, mirror_path, _schema_id in mappings:
        _write_schema(authoritative_path, schema)
        _write_schema(mirror_path, schema)


if __name__ == "__main__":
    main()
