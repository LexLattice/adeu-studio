from __future__ import annotations

import json
from pathlib import Path

from .models import AdeuIR, CheckReport
from .repo import repo_root


def _write_schema(path: Path, schema: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(schema, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    schema_dir = root / "packages" / "adeu_ir" / "schema"

    _write_schema(schema_dir / "adeu.ir.v0.json", AdeuIR.model_json_schema())
    _write_schema(schema_dir / "adeu.check_report.v0.json", CheckReport.model_json_schema())


if __name__ == "__main__":
    main()
