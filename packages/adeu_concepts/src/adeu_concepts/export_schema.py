from __future__ import annotations

import json
from pathlib import Path

from adeu_ir.repo import repo_root

from .models import ConceptIR


def _write_schema(path: Path, schema: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(schema, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    schema_dir = root / "packages" / "adeu_concepts" / "schema"
    _write_schema(
        schema_dir / "adeu.concepts.v0.json",
        ConceptIR.model_json_schema(),
    )


if __name__ == "__main__":
    main()
