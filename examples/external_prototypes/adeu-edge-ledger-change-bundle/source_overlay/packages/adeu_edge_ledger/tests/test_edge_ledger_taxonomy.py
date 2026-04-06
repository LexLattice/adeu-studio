from __future__ import annotations

import json
from pathlib import Path

from adeu_edge_ledger import (
    EdgeClassCatalog,
    EdgeProbeTemplateCatalog,
    build_starter_edge_class_catalog,
    build_starter_edge_probe_template_catalog,
    catalog_nodes_by_ref,
    leaf_edge_class_refs,
)


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v0" / name


def _read_json(name: str) -> dict[str, object]:
    return json.loads(_fixture_path(name).read_text(encoding="utf-8"))


def test_reference_edge_class_catalog_replays_deterministically() -> None:
    payload = _read_json("reference_edge_class_catalog.json")
    catalog = EdgeClassCatalog.model_validate(payload)

    assert catalog.model_dump(mode="json", by_alias=True, exclude_none=True) == payload


def test_reference_edge_probe_template_catalog_replays_deterministically() -> None:
    payload = _read_json("reference_edge_probe_template_catalog.json")
    catalog = EdgeProbeTemplateCatalog.model_validate(payload)

    assert catalog.model_dump(mode="json", by_alias=True, exclude_none=True) == payload


def test_starter_catalog_matches_reference_fixture() -> None:
    catalog = build_starter_edge_class_catalog()

    assert catalog.model_dump(mode="json", by_alias=True, exclude_none=True) == _read_json(
        "reference_edge_class_catalog.json"
    )


def test_starter_probe_template_catalog_matches_reference_fixture() -> None:
    edge_catalog = build_starter_edge_class_catalog()
    probe_catalog = build_starter_edge_probe_template_catalog(edge_class_catalog=edge_catalog)

    assert probe_catalog.model_dump(mode="json", by_alias=True, exclude_none=True) == _read_json(
        "reference_edge_probe_template_catalog.json"
    )


def test_starter_taxonomy_uses_three_levels_and_expected_family_count() -> None:
    catalog = build_starter_edge_class_catalog()
    nodes_by_ref = catalog_nodes_by_ref(catalog)
    families = [node for node in catalog.nodes if node.node_kind == "family"]
    subfamilies = [node for node in catalog.nodes if node.node_kind == "subfamily"]
    archetypes = [node for node in catalog.nodes if node.node_kind == "archetype"]

    assert len(families) == 8
    assert len(subfamilies) == 16
    assert len(archetypes) == 25
    assert leaf_edge_class_refs(catalog) == [node.edge_class_ref for node in archetypes]
    assert all(node.parent_edge_class_ref is None for node in families)
    assert all(nodes_by_ref[node.parent_edge_class_ref].node_kind == "family" for node in subfamilies)
    assert all(
        nodes_by_ref[node.parent_edge_class_ref].node_kind == "subfamily" for node in archetypes
    )


def test_probe_templates_bind_only_known_leaf_edge_classes() -> None:
    edge_catalog = build_starter_edge_class_catalog()
    probe_catalog = build_starter_edge_probe_template_catalog(edge_class_catalog=edge_catalog)
    known_leaf_refs = set(leaf_edge_class_refs(edge_catalog))

    assert len(probe_catalog.probe_templates) == 13
    assert all(set(probe.suited_edge_class_refs) <= known_leaf_refs for probe in probe_catalog.probe_templates)
    assert any(
        probe.probe_template_ref == "probe:manual_adjudication"
        and probe.execution_postures == ["review_only"]
        for probe in probe_catalog.probe_templates
    )
