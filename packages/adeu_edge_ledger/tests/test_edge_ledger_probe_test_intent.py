from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path

import pytest
from adeu_edge_ledger import (
    BRIDGE_SCOPE,
    SymbolEdgeApplicabilityFrame,
    SymbolEdgeApplicabilityRow,
    build_starter_edge_class_catalog,
    build_starter_edge_probe_template_catalog,
    compute_edge_probe_test_intent_bridge_entry_id,
    compute_edge_probe_test_intent_bridge_id,
    compute_symbol_edge_applicability_frame_id,
    derive_edge_probe_test_intent_bridge,
    validate_edge_probe_test_intent_bridge_bindings,
)
from adeu_edge_ledger.models import _sha256_canonical_payload

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v53d"
V45D_ROOT = Path(__file__).resolve().parents[3] / "apps" / "api" / "fixtures" / "repo_description"


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v53d(name: str) -> dict[str, object]:
    return _load_json(FIXTURE_ROOT / name)


def _v45d_stack() -> tuple[dict[str, object], dict[str, object], dict[str, object]]:
    matrix = _load_json(V45D_ROOT / "vnext_plus103" / "repo_test_intent_matrix_v103_reference.json")
    pair = _load_json(
        V45D_ROOT
        / "vnext_plus103"
        / "repo_test_intent_matrix_pair_v103_reject_mismatched_v45b_snapshot_binding.json"
    )
    symbol_catalog = pair["symbol_catalog"]
    dependency_graph = pair["dependency_graph"]
    assert matrix["bound_symbol_catalog_ref"] == symbol_catalog["repo_symbol_catalog_id"]
    assert matrix["bound_dependency_graph_ref"] == dependency_graph["repo_dependency_graph_id"]
    return matrix, symbol_catalog, dependency_graph


def _split_symbol_id(symbol_id: str) -> tuple[str, str, str]:
    parts = symbol_id.split(":")
    if len(parts) < 4 or parts[0] != "symbol":
        raise ValueError(f"unexpected symbol_id format: {symbol_id}")
    return ":".join(parts[1:-2]), parts[-2], parts[-1]


def _make_single_symbol_frame(
    *,
    symbol_id: str,
    bound_edge_class_catalog_ref: str,
    bound_probe_template_catalog_ref: str,
) -> SymbolEdgeApplicabilityFrame:
    module_path, qualname, symbol_kind = _split_symbol_id(symbol_id)
    rows = [
        SymbolEdgeApplicabilityRow.model_validate(
            {
                "edge_class_ref": (
                    "edge_class:contract_invariant/cross_field_binding/cross_field_consistency"
                ),
                "applicability_status": "applicable",
                "epistemic_posture": "derived_deterministically",
                "matched_cue_tags": ["feature:cross_field_terms"],
                "concrete_binding_refs": [f"symbol:{qualname}"],
                "suggested_probe_template_refs": ["probe:cross_field_invariant"],
                "rationale": "deterministic v53d test frame",
            }
        )
    ]
    payload = {
        "schema": "adeu_symbol_edge_applicability_frame@1",
        "bound_edge_class_catalog_ref": bound_edge_class_catalog_ref,
        "bound_probe_template_catalog_ref": bound_probe_template_catalog_ref,
        "scope_manifest_ref": "scope_manifest:v53d_test",
        "census_hash": "1" * 64,
        "audit_hash": "2" * 64,
        "symbol_id": symbol_id,
        "module_path": module_path,
        "qualname": qualname,
        "symbol_kind": symbol_kind,
        "frame_posture": "v53d_test_only_frame",
        "applicability_rows": [row.model_dump(mode="json", exclude_none=True) for row in rows],
    }
    payload["frame_hash"] = _sha256_canonical_payload(payload)
    payload["frame_id"] = compute_symbol_edge_applicability_frame_id(payload)
    return SymbolEdgeApplicabilityFrame.model_validate(payload)


def _canonicalize_bridge_payload(payload: dict[str, object]) -> dict[str, object]:
    canonical = deepcopy(payload)
    entries = []
    for raw_entry in canonical["bridge_entries"]:
        entry = dict(raw_entry)
        entry.pop("bridge_entry_id", None)
        entry["bridge_entry_id"] = compute_edge_probe_test_intent_bridge_entry_id(entry)
        entries.append(entry)
    entries.sort(key=lambda row: row["test_intent_entry_ref"])
    canonical["bridge_entries"] = entries

    payload_without_identity = {
        "schema": canonical["schema"],
        "bridge_scope": canonical["bridge_scope"],
        "bridge_posture": canonical["bridge_posture"],
        "bound_edge_class_catalog_ref": canonical["bound_edge_class_catalog_ref"],
        "bound_probe_template_catalog_ref": canonical["bound_probe_template_catalog_ref"],
        "bound_test_intent_matrix_ref": canonical["bound_test_intent_matrix_ref"],
        "bound_symbol_catalog_ref": canonical["bound_symbol_catalog_ref"],
        "bound_dependency_graph_ref": canonical["bound_dependency_graph_ref"],
        "bound_applicability_frame_refs": canonical["bound_applicability_frame_refs"],
        "bridge_entries": canonical["bridge_entries"],
    }
    canonical["bridge_hash"] = _sha256_canonical_payload(payload_without_identity)
    canonical["bridge_id"] = compute_edge_probe_test_intent_bridge_id(
        {
            **payload_without_identity,
            "bridge_hash": canonical["bridge_hash"],
        }
    )
    return canonical


def test_reference_probe_test_intent_bridge_replays_deterministically() -> None:
    edge_catalog = build_starter_edge_class_catalog()
    probe_catalog = build_starter_edge_probe_template_catalog(edge_class_catalog=edge_catalog)
    matrix, symbol_catalog, dependency_graph = _v45d_stack()
    expected = _load_v53d("reference_edge_probe_test_intent_bridge.json")

    bridge = validate_edge_probe_test_intent_bridge_bindings(
        bridge_payload=expected,
        test_intent_matrix=matrix,
        symbol_catalog=symbol_catalog,
        dependency_graph=dependency_graph,
        edge_class_catalog=edge_catalog,
        probe_template_catalog=probe_catalog,
        applicability_frames=[],
    )

    assert bridge.bridge_scope == BRIDGE_SCOPE
    assert bridge.model_dump(mode="json", by_alias=True, exclude_none=True) == expected


def test_reference_bridge_fixture_matches_derived_payload() -> None:
    edge_catalog = build_starter_edge_class_catalog()
    probe_catalog = build_starter_edge_probe_template_catalog(edge_class_catalog=edge_catalog)
    matrix, symbol_catalog, dependency_graph = _v45d_stack()

    bridge = derive_edge_probe_test_intent_bridge(
        test_intent_matrix=matrix,
        symbol_catalog=symbol_catalog,
        dependency_graph=dependency_graph,
        edge_class_catalog=edge_catalog,
        probe_template_catalog=probe_catalog,
        applicability_frames=[],
    )

    assert bridge.model_dump(mode="json", by_alias=True, exclude_none=True) == _load_v53d(
        "reference_edge_probe_test_intent_bridge.json"
    )


def test_derivation_maps_rows_only_with_explicit_frame_membership() -> None:
    edge_catalog = build_starter_edge_class_catalog()
    probe_catalog = build_starter_edge_probe_template_catalog(edge_class_catalog=edge_catalog)
    matrix, symbol_catalog, dependency_graph = _v45d_stack()

    target_symbol_id = (
        "symbol:packages/adeu_repo_description/src/adeu_repo_description/models.py:"
        "compute_repo_symbol_catalog_id:function"
    )
    frame = _make_single_symbol_frame(
        symbol_id=target_symbol_id,
        bound_edge_class_catalog_ref=edge_catalog.catalog_id,
        bound_probe_template_catalog_ref=probe_catalog.catalog_id,
    )
    bridge = derive_edge_probe_test_intent_bridge(
        test_intent_matrix=matrix,
        symbol_catalog=symbol_catalog,
        dependency_graph=dependency_graph,
        edge_class_catalog=edge_catalog,
        probe_template_catalog=probe_catalog,
        applicability_frames=[frame],
    )

    mapped_rows = [
        row
        for row in bridge.bridge_entries
        if row.mapping_status == "mapped_from_applicability_frame"
    ]
    assert mapped_rows
    assert all(row.symbol_id == target_symbol_id for row in mapped_rows)
    assert all(
        row.selected_probe_template_refs == ["probe:cross_field_invariant"]
        for row in mapped_rows
    )
    assert all(row.selected_strategy_kinds == ["cross_field_invariant"] for row in mapped_rows)
    assert any(
        row.mapping_status == "out_of_scope_outside_v50_scope" for row in bridge.bridge_entries
    )


def test_reject_probe_mapping_without_explicit_frame_membership() -> None:
    edge_catalog = build_starter_edge_class_catalog()
    probe_catalog = build_starter_edge_probe_template_catalog(edge_class_catalog=edge_catalog)
    matrix, symbol_catalog, dependency_graph = _v45d_stack()
    payload = _load_v53d("reference_edge_probe_test_intent_bridge.json")

    first_internal_symbol = next(
        row
        for row in payload["bridge_entries"]
        if row["guarded_surface_ref_kind"] == "internal_symbol"
    )
    first_internal_symbol["mapping_status"] = "mapped_from_applicability_frame"
    first_internal_symbol["bound_applicability_frame_ref"] = "symbol_edge_applicability_frame:fake"
    first_internal_symbol["applicable_edge_class_refs"] = [
        "edge_class:contract_invariant/cross_field_binding/cross_field_consistency"
    ]
    first_internal_symbol["selected_probe_template_refs"] = ["probe:cross_field_invariant"]
    first_internal_symbol["selected_strategy_kinds"] = ["cross_field_invariant"]
    first_internal_symbol["mapping_rationale"] = "invalid forced mapping"
    payload = _canonicalize_bridge_payload(payload)

    with pytest.raises(
        ValueError,
        match="outside admitted V50 frame membership must remain out_of_scope_outside_v50_scope",
    ):
        validate_edge_probe_test_intent_bridge_bindings(
            bridge_payload=payload,
            test_intent_matrix=matrix,
            symbol_catalog=symbol_catalog,
            dependency_graph=dependency_graph,
            edge_class_catalog=edge_catalog,
            probe_template_catalog=probe_catalog,
            applicability_frames=[],
        )


def test_reject_mapped_probe_templates_not_suggested_by_frame() -> None:
    edge_catalog = build_starter_edge_class_catalog()
    probe_catalog = build_starter_edge_probe_template_catalog(edge_class_catalog=edge_catalog)
    matrix, symbol_catalog, dependency_graph = _v45d_stack()

    target_symbol_id = (
        "symbol:packages/adeu_repo_description/src/adeu_repo_description/models.py:"
        "compute_repo_symbol_catalog_id:function"
    )
    frame = _make_single_symbol_frame(
        symbol_id=target_symbol_id,
        bound_edge_class_catalog_ref=edge_catalog.catalog_id,
        bound_probe_template_catalog_ref=probe_catalog.catalog_id,
    )
    bridge = derive_edge_probe_test_intent_bridge(
        test_intent_matrix=matrix,
        symbol_catalog=symbol_catalog,
        dependency_graph=dependency_graph,
        edge_class_catalog=edge_catalog,
        probe_template_catalog=probe_catalog,
        applicability_frames=[frame],
    ).model_dump(mode="json", by_alias=True, exclude_none=True)

    target_row = next(
        row
        for row in bridge["bridge_entries"]
        if row["mapping_status"] == "mapped_from_applicability_frame"
    )
    target_row["selected_probe_template_refs"] = ["probe:fail_closed_rejection"]
    target_row["selected_strategy_kinds"] = ["fail_closed_rejection"]
    bridge = _canonicalize_bridge_payload(bridge)

    with pytest.raises(
        ValueError,
        match="mapped probe template refs must be suggested by applicable/underdetermined rows",
    ):
        validate_edge_probe_test_intent_bridge_bindings(
            bridge_payload=bridge,
            test_intent_matrix=matrix,
            symbol_catalog=symbol_catalog,
            dependency_graph=dependency_graph,
            edge_class_catalog=edge_catalog,
            probe_template_catalog=probe_catalog,
            applicability_frames=[frame],
        )
