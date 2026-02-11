from __future__ import annotations

import json
from pathlib import Path

from adeu_api.adeu_concept_bridge import (
    BRIDGE_LOSS_VERSION,
    BRIDGE_MAPPING_VERSION,
    build_bridge_loss_report,
    compute_mapping_hash,
    lift_adeu_to_concepts,
)
from adeu_ir import AdeuIR
from adeu_ir.repo import repo_root


def _fixture_ir(*, fixture: str, name: str) -> AdeuIR:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "fixtures" / fixture / "proposals" / name
    return AdeuIR.model_validate(json.loads(path.read_text(encoding="utf-8")))


def _permuted_ir(ir: AdeuIR) -> AdeuIR:
    return ir.model_copy(
        update={
            "O": ir.O.model_copy(
                update={
                    "entities": list(reversed(ir.O.entities)),
                    "definitions": list(reversed(ir.O.definitions)),
                }
            ),
            "D_norm": ir.D_norm.model_copy(
                update={
                    "statements": list(reversed(ir.D_norm.statements)),
                    "exceptions": list(reversed(ir.D_norm.exceptions)),
                }
            ),
        }
    )


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


def test_build_bridge_loss_report_is_deterministic_and_permutation_invariant() -> None:
    ir = _fixture_ir(fixture="exception_priority_resolves_conflict", name="var2.json")
    permuted = _permuted_ir(ir)

    left = build_bridge_loss_report(ir)
    right = build_bridge_loss_report(ir)
    permuted_report = build_bridge_loss_report(permuted)

    assert left.version == BRIDGE_LOSS_VERSION
    assert left.model_dump(mode="json") == right.model_dump(mode="json")
    assert left.model_dump(mode="json") == permuted_report.model_dump(mode="json")
    assert left.entries == sorted(
        left.entries,
        key=lambda item: (item.feature_key, item.scope, item.status),
    )
    assert len(
        {(item.feature_key, item.scope, item.status) for item in left.entries}
    ) == len(left.entries)

    for entry in left.entries:
        if entry.scope == "structural":
            assert entry.source_paths == []
        else:
            assert entry.source_paths
            assert entry.source_paths == sorted(entry.source_paths)
            assert all(path.startswith("/") for path in entry.source_paths)


def test_build_bridge_loss_report_structural_entries_are_bridge_version_facts() -> None:
    left_ir = _fixture_ir(fixture="exception_priority_resolves_conflict", name="var2.json")
    right_ir = _fixture_ir(fixture="material_breach_trigger", name="var1.json")
    left_structural = [
        item for item in build_bridge_loss_report(left_ir).entries if item.scope == "structural"
    ]
    right_structural = [
        item for item in build_bridge_loss_report(right_ir).entries if item.scope == "structural"
    ]

    assert left_structural == right_structural == sorted(
        left_structural,
        key=lambda item: (item.feature_key, item.scope, item.status),
    )
    assert all(entry.source_paths == [] for entry in left_structural)
