from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from adeu_ir import AdeuIR, Context


@dataclass(frozen=True)
class FixtureBundle:
    clause_text: str
    proposals: list[AdeuIR]


def _repo_root() -> Path:
    # apps/api/src/adeu_api/mock_provider.py -> adeu_api -> src -> api -> apps -> repo root
    return Path(__file__).resolve().parents[4]


def load_fixture_bundles() -> dict[str, FixtureBundle]:
    repo_root = _repo_root()
    fixtures_root = repo_root / "examples" / "fixtures"

    bundles: dict[str, FixtureBundle] = {}
    for fixture_dir in sorted([p for p in fixtures_root.iterdir() if p.is_dir()]):
        clause_path = fixture_dir / "clause.txt"
        proposals_dir = fixture_dir / "proposals"
        if not clause_path.is_file() or not proposals_dir.is_dir():
            continue

        clause_text = clause_path.read_text(encoding="utf-8").strip()
        proposals: list[AdeuIR] = []
        for proposal_path in sorted(proposals_dir.glob("*.json")):
            payload = json.loads(proposal_path.read_text(encoding="utf-8"))
            proposals.append(AdeuIR.model_validate(payload))

        bundles[clause_text] = FixtureBundle(clause_text=clause_text, proposals=proposals)

    return bundles


def default_context_for_clause(clause_text: str) -> Context:
    # MVP: derive context from fixtures if present; otherwise fill conservative defaults.
    bundles = load_fixture_bundles()
    bundle = bundles.get(clause_text.strip())
    if bundle and bundle.proposals:
        return bundle.proposals[0].context

    raise ValueError("No fixture context available for clause")

