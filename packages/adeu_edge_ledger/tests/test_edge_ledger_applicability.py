from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_edge_ledger import (
    SymbolEdgeApplicabilityFrame,
    derive_scope_symbol_edge_applicability_frames,
    derive_symbol_edge_applicability_frame,
    validate_symbol_edge_applicability_frame_bindings,
)
from adeu_symbol_audit import SymbolAuditCoverageReport
from pydantic import ValidationError


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v53a" / name


def _read_json(name: str) -> dict[str, object]:
    return json.loads(_fixture_path(name).read_text(encoding="utf-8"))


def test_reference_applicability_frame_replays_deterministically(
    released_stack,
    starter_catalogs,
) -> None:
    _repo_root, _manifest, census, coverage, audit = released_stack
    edge_catalog, probe_catalog = starter_catalogs
    payload = _read_json("reference_symbol_edge_applicability_frame.json")

    frame = validate_symbol_edge_applicability_frame_bindings(
        frame_payload=payload,
        edge_class_catalog=edge_catalog,
        probe_template_catalog=probe_catalog,
        census=census,
        coverage_report=coverage,
        semantic_audit=audit,
    )

    assert frame.model_dump(mode="json", by_alias=True, exclude_none=True) == payload


def test_reference_applicability_fixture_matches_derived_frame(
    released_stack,
    starter_catalogs,
) -> None:
    repo_root, _manifest, census, coverage, audit = released_stack
    edge_catalog, probe_catalog = starter_catalogs
    expected_payload = _read_json("reference_symbol_edge_applicability_frame.json")

    frame = derive_symbol_edge_applicability_frame(
        repo_root=repo_root,
        census=census,
        coverage_report=coverage,
        semantic_audit=audit,
        symbol_id=str(expected_payload["symbol_id"]),
        edge_class_catalog=edge_catalog,
        probe_template_catalog=probe_catalog,
    )

    assert frame.model_dump(mode="json", by_alias=True, exclude_none=True) == expected_payload


def test_scope_applicability_frames_cover_every_census_symbol(
    released_stack,
    starter_catalogs,
) -> None:
    repo_root, _manifest, census, coverage, audit = released_stack
    edge_catalog, probe_catalog = starter_catalogs

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
    assert all(
        frame.bound_probe_template_catalog_ref == probe_catalog.catalog_id for frame in frames
    )
    assert all(len(frame.applicability_rows) == 16 for frame in frames)


def test_reject_non_closed_clean_coverage_input_fails_closed(
    released_stack,
    starter_catalogs,
) -> None:
    repo_root, _manifest, census, _coverage, audit = released_stack
    edge_catalog, probe_catalog = starter_catalogs
    coverage = SymbolAuditCoverageReport.model_validate(
        _read_json("reject_symbol_audit_coverage_report_fail_closed_mismatch.json")
    )
    expected_payload = _read_json("reference_symbol_edge_applicability_frame.json")

    with pytest.raises(ValueError, match="coverage_report.coverage_status = closed_clean"):
        derive_symbol_edge_applicability_frame(
            repo_root=repo_root,
            census=census,
            coverage_report=coverage,
            semantic_audit=audit,
            symbol_id=str(expected_payload["symbol_id"]),
            edge_class_catalog=edge_catalog,
            probe_template_catalog=probe_catalog,
        )


def test_reject_sparse_applicability_rows_fail_closed(
    released_stack,
    starter_catalogs,
) -> None:
    _repo_root, _manifest, census, coverage, audit = released_stack
    edge_catalog, probe_catalog = starter_catalogs

    with pytest.raises(
        ValueError,
        match="cover every admitted archetype exactly once in catalog order",
    ):
        validate_symbol_edge_applicability_frame_bindings(
            frame_payload=_read_json("reject_symbol_edge_applicability_frame_sparse_rows.json"),
            edge_class_catalog=edge_catalog,
            probe_template_catalog=probe_catalog,
            census=census,
            coverage_report=coverage,
            semantic_audit=audit,
        )


def test_reject_row_support_cardinality_drift() -> None:
    with pytest.raises(
        ValidationError,
        match="applicable and underdetermined rows require non-empty",
    ):
        SymbolEdgeApplicabilityFrame.model_validate(
            _read_json("reject_symbol_edge_applicability_frame_applicable_empty_support.json")
        )

    with pytest.raises(
        ValidationError,
        match="not_applicable rows require empty matched_cue_tags",
    ):
        SymbolEdgeApplicabilityFrame.model_validate(
            _read_json(
                "reject_symbol_edge_applicability_frame_not_applicable_non_empty_support.json"
            )
        )


def test_reject_symbol_id_drift_and_adjudication_only_fields() -> None:
    with pytest.raises(
        ValidationError,
        match="symbol_id must match canonical module_path",
    ):
        SymbolEdgeApplicabilityFrame.model_validate(
            _read_json("reject_symbol_edge_applicability_frame_symbol_id_drift.json")
        )

    with pytest.raises(ValidationError):
        SymbolEdgeApplicabilityFrame.model_validate(
            _read_json("reject_symbol_edge_applicability_frame_with_adjudication_fields.json")
        )
