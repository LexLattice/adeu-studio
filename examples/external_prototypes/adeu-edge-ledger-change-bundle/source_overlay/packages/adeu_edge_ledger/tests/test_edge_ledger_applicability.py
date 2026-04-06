from __future__ import annotations

import json
from pathlib import Path

from adeu_edge_ledger import (
    SymbolEdgeApplicabilityFrame,
    build_starter_edge_class_catalog,
    build_starter_edge_probe_template_catalog,
    derive_scope_symbol_edge_applicability_frames,
    derive_symbol_edge_applicability_frame,
)

ANALYSIS_REQUEST_CLASS_SYMBOL_ID = (
    "symbol:packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py:"
    "AdeuArchitectureAnalysisRequest:class"
)


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v0" / name


def _read_json(name: str) -> dict[str, object]:
    return json.loads(_fixture_path(name).read_text(encoding="utf-8"))


def test_reference_applicability_frame_replays_deterministically() -> None:
    payload = _read_json("reference_applicability_frame_analysis_request_class.json")
    frame = SymbolEdgeApplicabilityFrame.model_validate(payload)

    assert frame.model_dump(mode="json", by_alias=True, exclude_none=True) == payload


def test_analysis_request_class_applicability_matches_reference_fixture(released_stack) -> None:
    repo_root, _manifest, census, coverage, audit = released_stack
    edge_catalog = build_starter_edge_class_catalog()
    probe_catalog = build_starter_edge_probe_template_catalog(edge_class_catalog=edge_catalog)

    frame = derive_symbol_edge_applicability_frame(
        repo_root=repo_root,
        census=census,
        coverage_report=coverage,
        semantic_audit=audit,
        symbol_id=ANALYSIS_REQUEST_CLASS_SYMBOL_ID,
        edge_class_catalog=edge_catalog,
        probe_template_catalog=probe_catalog,
    )

    assert frame.model_dump(mode="json", by_alias=True, exclude_none=True) == _read_json(
        "reference_applicability_frame_analysis_request_class.json"
    )


def test_scope_applicability_frames_cover_every_census_symbol(released_stack) -> None:
    repo_root, _manifest, census, coverage, audit = released_stack
    edge_catalog = build_starter_edge_class_catalog()
    probe_catalog = build_starter_edge_probe_template_catalog(edge_class_catalog=edge_catalog)

    frames = derive_scope_symbol_edge_applicability_frames(
        repo_root=repo_root,
        census=census,
        coverage_report=coverage,
        semantic_audit=audit,
        edge_class_catalog=edge_catalog,
        probe_template_catalog=probe_catalog,
    )

    assert len(frames) == census.symbol_count
    assert [frame.symbol_id for frame in frames] == [entry.symbol_id for entry in census.symbols]
    assert all(frame.bound_edge_class_catalog_ref == edge_catalog.catalog_id for frame in frames)
    assert all(frame.bound_probe_template_catalog_ref == probe_catalog.catalog_id for frame in frames)
    assert all(len(frame.applicability_rows) == 25 for frame in frames)


def test_analysis_request_class_has_one_fully_applicable_guard_class(released_stack) -> None:
    repo_root, _manifest, census, coverage, audit = released_stack
    frame = derive_symbol_edge_applicability_frame(
        repo_root=repo_root,
        census=census,
        coverage_report=coverage,
        semantic_audit=audit,
        symbol_id=ANALYSIS_REQUEST_CLASS_SYMBOL_ID,
    )
    applicable_refs = [
        row.edge_class_ref
        for row in frame.applicability_rows
        if row.applicability_status == "applicable"
    ]

    assert applicable_refs == [
        "edge_class:control_partition/guard_short_circuit/guard_before_side_effect"
    ]
