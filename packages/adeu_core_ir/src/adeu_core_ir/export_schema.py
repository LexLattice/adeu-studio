from __future__ import annotations

import json
from pathlib import Path

from adeu_ir.repo import repo_root

from .models import AdeuCoreIR


def _write_schema(path: Path, schema: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(schema, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    schema = AdeuCoreIR.model_json_schema(by_alias=True)

    authoritative_path = root / "packages" / "adeu_core_ir" / "schema" / "adeu_core_ir.v0_1.json"
    _write_schema(authoritative_path, schema)

    mirror_path = root / "spec" / "adeu_core_ir.schema.json"
    _write_schema(mirror_path, schema)


if __name__ == "__main__":
    main()
