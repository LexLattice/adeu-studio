from __future__ import annotations

import json
from pathlib import Path

from adeu_api.adeu_concept_bridge import (
    BRIDGE_MAPPING_VERSION,
    compute_mapping_hash,
    lift_adeu_to_concepts,
)
from adeu_ir import AdeuIR
from adeu_ir.repo import repo_root


def _fixture_ir(*, fixture: str, name: str) -> AdeuIR:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "fixtures" / fixture / "proposals" / name
    return AdeuIR.model_validate(json.loads(path.read_text(encoding="utf-8")))


def test_lift_adeu_to_concepts_is_deterministic_and_sorted() -> None:
    ir = _fixture_ir(fixture="exception_priority_resolves_conflict", name="var2.json")
    left = lift_adeu_to_concepts(ir)
    right = lift_adeu_to_concepts(ir)

    assert left.mapping_hash == right.mapping_hash == compute_mapping_hash()
    assert left.bridge_mapping_version == BRIDGE_MAPPING_VERSION
    assert left.concept_ir.model_dump(mode="json") == right.concept_ir.model_dump(mode="json")

    entries = left.bridge_manifest.entries
    assert entries == sorted(
        entries,
        key=lambda item: (
            item.adeu_object_id,
            item.concept_kind,
            item.concept_object_id,
            item.confidence_tag,
        ),
    )
    map_keys = list(left.bridge_manifest.adeu_to_concept_ids.keys())
    assert map_keys == sorted(map_keys)


def test_lift_adeu_to_concepts_maps_exception_effects_to_links() -> None:
    ir = _fixture_ir(fixture="exception_priority_resolves_conflict", name="var2.json")
    lifted = lift_adeu_to_concepts(ir)
    kinds = {link.kind for link in lifted.concept_ir.links}

    assert "incompatibility" in kinds
    assert "commitment" in kinds
    assert any(
        ambiguity.id.startswith("amb_exception") for ambiguity in lifted.concept_ir.ambiguity
    )

