from __future__ import annotations

import json
from pathlib import Path

from adeu_ir.repo import repo_root

from .models import KnightsKnavesPuzzle, PuzzleSolveResult


def _write_schema(path: Path, schema: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(schema, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    schema_dir = root / "packages" / "adeu_puzzles" / "schema"
    _write_schema(
        schema_dir / "adeu.puzzle.knights_knaves.v0.json",
        KnightsKnavesPuzzle.model_json_schema(),
    )
    _write_schema(
        schema_dir / "adeu.puzzle.solve_result.v0.json",
        PuzzleSolveResult.model_json_schema(),
    )


if __name__ == "__main__":
    main()
