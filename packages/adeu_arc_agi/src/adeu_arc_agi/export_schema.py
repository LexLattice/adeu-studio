from __future__ import annotations

import json
from pathlib import Path

from adeu_ir.repo import repo_root

from .observation_hypothesis import (
    ADEU_ARC_HYPOTHESIS_FRAME_SCHEMA,
    ADEU_ARC_OBSERVATION_FRAME_SCHEMA,
    AdeuArcHypothesisFrame,
    AdeuArcObservationFrame,
)
from .task_packet import ADEU_ARC_TASK_PACKET_SCHEMA, AdeuArcTaskPacket


def _write_schema(path: Path, schema: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(schema, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    task_packet_schema = AdeuArcTaskPacket.model_json_schema(by_alias=True)
    if task_packet_schema["properties"]["schema"]["const"] != ADEU_ARC_TASK_PACKET_SCHEMA:
        raise ValueError("exported schema marker drift for adeu_arc_task_packet@1")
    observation_schema = AdeuArcObservationFrame.model_json_schema(by_alias=True)
    if observation_schema["properties"]["schema"]["const"] != ADEU_ARC_OBSERVATION_FRAME_SCHEMA:
        raise ValueError("exported schema marker drift for adeu_arc_observation_frame@1")
    hypothesis_schema = AdeuArcHypothesisFrame.model_json_schema(by_alias=True)
    if hypothesis_schema["properties"]["schema"]["const"] != ADEU_ARC_HYPOTHESIS_FRAME_SCHEMA:
        raise ValueError("exported schema marker drift for adeu_arc_hypothesis_frame@1")

    _write_schema(
        root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_task_packet.v1.json",
        task_packet_schema,
    )
    _write_schema(
        root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_observation_frame.v1.json",
        observation_schema,
    )
    _write_schema(
        root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_hypothesis_frame.v1.json",
        hypothesis_schema,
    )
    _write_schema(root / "spec" / "adeu_arc_task_packet.schema.json", task_packet_schema)
    _write_schema(
        root / "spec" / "adeu_arc_observation_frame.schema.json",
        observation_schema,
    )
    _write_schema(
        root / "spec" / "adeu_arc_hypothesis_frame.schema.json",
        hypothesis_schema,
    )


if __name__ == "__main__":
    main()
