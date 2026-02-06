from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

from adeu_ir.repo import repo_root
from adeu_puzzles import KnightsKnavesPuzzle


@dataclass(frozen=True)
class PuzzleFixtureBundle:
    case_id: str
    puzzle_text: str
    proposals: list[KnightsKnavesPuzzle]


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _hash_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


@lru_cache(maxsize=1)
def load_puzzle_fixture_bundles() -> dict[str, PuzzleFixtureBundle]:
    root = _repo_root()
    fixtures_root = root / "examples" / "puzzles" / "fixtures"
    if not fixtures_root.is_dir():
        return {}

    bundles: dict[str, PuzzleFixtureBundle] = {}
    for case_dir in sorted(path for path in fixtures_root.iterdir() if path.is_dir()):
        puzzle_path = case_dir / "puzzle.txt"
        if not puzzle_path.exists():
            continue
        puzzle_text = puzzle_path.read_text(encoding="utf-8").strip()
        proposals_dir = case_dir / "proposals"
        proposals: list[KnightsKnavesPuzzle] = []
        if proposals_dir.is_dir():
            for proposal_path in sorted(proposals_dir.glob("*.json")):
                payload = json.loads(proposal_path.read_text(encoding="utf-8"))
                proposals.append(KnightsKnavesPuzzle.model_validate(payload))

        bundle = PuzzleFixtureBundle(
            case_id=case_dir.name,
            puzzle_text=puzzle_text,
            proposals=proposals,
        )
        bundles[puzzle_text] = bundle
        bundles[_hash_text(puzzle_text)] = bundle
    return bundles


def get_puzzle_fixture_bundle(puzzle_text: str) -> PuzzleFixtureBundle | None:
    cleaned = puzzle_text.strip()
    bundles = load_puzzle_fixture_bundles()
    return bundles.get(cleaned) or bundles.get(_hash_text(cleaned))
