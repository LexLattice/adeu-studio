from __future__ import annotations

import json
from pathlib import Path

from adeu_ir.repo import repo_root

from .task_packet import ADEU_ARC_TASK_PACKET_SCHEMA, AdeuArcTaskPacket


def _write_schema(path: Path, schema: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(schema, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    schema = AdeuArcTaskPacket.model_json_schema(by_alias=True)
    if schema["properties"]["schema"]["const"] != ADEU_ARC_TASK_PACKET_SCHEMA:
        raise ValueError("exported schema marker drift for adeu_arc_task_packet@1")
    authoritative = (
        root / "packages" / "adeu_arc_agi" / "schema" / "adeu_arc_task_packet.v1.json"
    )
    mirror = root / "spec" / "adeu_arc_task_packet.schema.json"
    _write_schema(authoritative, schema)
    _write_schema(mirror, schema)


if __name__ == "__main__":
    main()

