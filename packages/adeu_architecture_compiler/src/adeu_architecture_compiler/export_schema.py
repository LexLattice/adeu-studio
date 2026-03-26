from __future__ import annotations

import json
from pathlib import Path

from adeu_ir.repo import repo_root

from .conformance import AdeuArchitectureConformanceReport
from .hybrid import (
    AdeuArchitectureCheckpointTrace,
    AdeuArchitectureIRDelta,
    AdeuArchitectureOracleRequest,
    AdeuArchitectureOracleResolution,
)
from .observation import AdeuArchitectureObservationFrame
from .projection import (
    AdeuArchitectureProjectionBundle,
    AdeuArchitectureProjectionManifest,
)
from .release_integration import V40FArchitectureReleaseIntegrationEvidence


def _write_schema(path: Path, schema: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(schema, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    targets = [
        (
            AdeuArchitectureConformanceReport,
            "adeu_architecture_conformance_report.v1.json",
            "adeu_architecture_conformance_report.schema.json",
        ),
        (
            AdeuArchitectureOracleRequest,
            "adeu_architecture_oracle_request.v1.json",
            "adeu_architecture_oracle_request.schema.json",
        ),
        (
            AdeuArchitectureOracleResolution,
            "adeu_architecture_oracle_resolution.v1.json",
            "adeu_architecture_oracle_resolution.schema.json",
        ),
        (
            AdeuArchitectureCheckpointTrace,
            "adeu_architecture_checkpoint_trace.v1.json",
            "adeu_architecture_checkpoint_trace.schema.json",
        ),
        (
            AdeuArchitectureObservationFrame,
            "adeu_architecture_observation_frame.v1.json",
            "adeu_architecture_observation_frame.schema.json",
        ),
        (
            AdeuArchitectureIRDelta,
            "adeu_architecture_ir_delta.v1.json",
            "adeu_architecture_ir_delta.schema.json",
        ),
        (
            AdeuArchitectureProjectionBundle,
            "adeu_architecture_projection_bundle.v1.json",
            "adeu_architecture_projection_bundle.schema.json",
        ),
        (
            AdeuArchitectureProjectionManifest,
            "adeu_architecture_projection_manifest.v1.json",
            "adeu_architecture_projection_manifest.schema.json",
        ),
        (
            V40FArchitectureReleaseIntegrationEvidence,
            "v40f_architecture_release_integration_evidence.v1.json",
            "v40f_architecture_release_integration_evidence.schema.json",
        ),
    ]
    for model, authoritative_name, mirror_name in targets:
        schema = model.model_json_schema(by_alias=True)
        authoritative_path = (
            root
            / "packages"
            / "adeu_architecture_compiler"
            / "schema"
            / authoritative_name
        )
        mirror_path = root / "spec" / mirror_name
        _write_schema(authoritative_path, schema)
        _write_schema(mirror_path, schema)


if __name__ == "__main__":
    main()
