from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

from adeu_concepts import ConceptIR
from adeu_ir.repo import repo_root


@dataclass(frozen=True)
class ConceptFixtureBundle:
    case_id: str
    source_text: str
    proposals: list[ConceptIR]


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _hash_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


@lru_cache(maxsize=1)
def load_concept_fixture_bundles() -> dict[str, ConceptFixtureBundle]:
    root = _repo_root()
    fixtures_root = root / "examples" / "concepts" / "fixtures"
    if not fixtures_root.is_dir():
        return {}

    bundles: dict[str, ConceptFixtureBundle] = {}
    for case_dir in sorted(path for path in fixtures_root.iterdir() if path.is_dir()):
        source_path = case_dir / "source.txt"
        if not source_path.exists():
            continue
        source_text = source_path.read_text(encoding="utf-8").strip()
        proposals_dir = case_dir / "proposals"
        proposals: list[ConceptIR] = []
        if proposals_dir.is_dir():
            for proposal_path in sorted(proposals_dir.glob("*.json")):
                payload = json.loads(proposal_path.read_text(encoding="utf-8"))
                proposals.append(ConceptIR.model_validate(payload))

        bundle = ConceptFixtureBundle(
            case_id=case_dir.name,
            source_text=source_text,
            proposals=proposals,
        )
        bundles[source_text] = bundle
        bundles[_hash_text(source_text)] = bundle
    return bundles


def get_concept_fixture_bundle(source_text: str) -> ConceptFixtureBundle | None:
    cleaned = source_text.strip()
    bundles = load_concept_fixture_bundles()
    return bundles.get(cleaned) or bundles.get(_hash_text(cleaned))
