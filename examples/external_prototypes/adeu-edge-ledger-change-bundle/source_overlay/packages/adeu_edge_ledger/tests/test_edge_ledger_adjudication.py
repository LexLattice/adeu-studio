from __future__ import annotations

import json
from pathlib import Path

from adeu_edge_ledger import (
    SymbolEdgeAdjudicationLedger,
    derive_symbol_edge_adjudication_ledger,
)

ANALYSIS_REQUEST_CLASS_SYMBOL_ID = (
    "symbol:packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py:"
    "AdeuArchitectureAnalysisRequest:class"
)
CAPTURE_SOURCE_SET_SYMBOL_ID = (
    "symbol:packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py:"
    "capture_adeu_architecture_analysis_source_set_payload:function"
)
RUN_GIT_SYMBOL_ID = (
    "symbol:packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py:"
    "_run_git:function"
)
MATERIALIZE_SETTLEMENT_SYMBOL_ID = (
    "symbol:packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_settlement.py:"
    "materialize_adeu_architecture_analysis_settlement_frame_payload:function"
)

GUARD_BEFORE_SIDE_EFFECT_REF = (
    "edge_class:control_partition/guard_short_circuit/guard_before_side_effect"
)


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v0" / name


def _read_json(name: str) -> dict[str, object]:
    return json.loads(_fixture_path(name).read_text(encoding="utf-8"))


def _row_by_ref(ledger: SymbolEdgeAdjudicationLedger, edge_class_ref: str):
    return next(row for row in ledger.adjudication_rows if row.edge_class_ref == edge_class_ref)


def test_reference_adjudication_ledger_replays_deterministically() -> None:
    payload = _read_json("reference_adjudication_ledger_analysis_request_class.json")
    ledger = SymbolEdgeAdjudicationLedger.model_validate(payload)

    assert ledger.model_dump(mode="json", by_alias=True, exclude_none=True) == payload


def test_analysis_request_class_adjudication_matches_reference_fixture(released_stack) -> None:
    repo_root, _manifest, census, coverage, audit = released_stack

    ledger = derive_symbol_edge_adjudication_ledger(
        repo_root=repo_root,
        census=census,
        coverage_report=coverage,
        semantic_audit=audit,
        symbol_id=ANALYSIS_REQUEST_CLASS_SYMBOL_ID,
    )

    assert ledger.model_dump(mode="json", by_alias=True, exclude_none=True) == _read_json(
        "reference_adjudication_ledger_analysis_request_class.json"
    )


def test_proto_ledger_surfaces_test_covered_structural_safe_unchecked_and_deferred_statuses(
    released_stack,
) -> None:
    repo_root, _manifest, census, coverage, audit = released_stack

    covered_ledger = derive_symbol_edge_adjudication_ledger(
        repo_root=repo_root,
        census=census,
        coverage_report=coverage,
        semantic_audit=audit,
        symbol_id=ANALYSIS_REQUEST_CLASS_SYMBOL_ID,
    )
    covered_row = _row_by_ref(covered_ledger, GUARD_BEFORE_SIDE_EFFECT_REF)
    assert covered_row.adjudication_status == "covered_by_existing_tests"
    assert covered_row.supporting_test_refs == [
        "test:packages/adeu_architecture_ir/tests/test_analysis_request.py#test_v41a_rejects_source_item_outside_scope"
    ]

    structural_ledger = derive_symbol_edge_adjudication_ledger(
        repo_root=repo_root,
        census=census,
        coverage_report=coverage,
        semantic_audit=audit,
        symbol_id=CAPTURE_SOURCE_SET_SYMBOL_ID,
    )
    structural_row = _row_by_ref(structural_ledger, GUARD_BEFORE_SIDE_EFFECT_REF)
    assert structural_row.adjudication_status == "bounded_safe_by_structure"
    assert "cue:feature:raises_value_error" in structural_row.supporting_evidence_refs
    assert "audit_status:audited_hypothesis" in structural_row.supporting_evidence_refs

    unchecked_ledger = derive_symbol_edge_adjudication_ledger(
        repo_root=repo_root,
        census=census,
        coverage_report=coverage,
        semantic_audit=audit,
        symbol_id=MATERIALIZE_SETTLEMENT_SYMBOL_ID,
    )
    unchecked_row = _row_by_ref(unchecked_ledger, GUARD_BEFORE_SIDE_EFFECT_REF)
    assert unchecked_row.adjudication_status == "applicable_unchecked"

    deferred_ledger = derive_symbol_edge_adjudication_ledger(
        repo_root=repo_root,
        census=census,
        coverage_report=coverage,
        semantic_audit=audit,
        symbol_id=RUN_GIT_SYMBOL_ID,
    )
    deferred_row = _row_by_ref(deferred_ledger, GUARD_BEFORE_SIDE_EFFECT_REF)
    assert deferred_row.adjudication_status == "deferred"
    assert "audit_status:audited_low_confidence" in deferred_row.supporting_evidence_refs


def test_explicit_probe_outcomes_can_override_default_statuses(released_stack) -> None:
    repo_root, _manifest, census, coverage, audit = released_stack

    witness_ledger = derive_symbol_edge_adjudication_ledger(
        repo_root=repo_root,
        census=census,
        coverage_report=coverage,
        semantic_audit=audit,
        symbol_id=ANALYSIS_REQUEST_CLASS_SYMBOL_ID,
        witness_summaries={GUARD_BEFORE_SIDE_EFFECT_REF: "guard executed after boundary call"},
    )
    witness_row = _row_by_ref(witness_ledger, GUARD_BEFORE_SIDE_EFFECT_REF)
    assert witness_row.adjudication_status == "witness_found"
    assert witness_row.witness_summary == "guard executed after boundary call"

    checked_no_witness_ledger = derive_symbol_edge_adjudication_ledger(
        repo_root=repo_root,
        census=census,
        coverage_report=coverage,
        semantic_audit=audit,
        symbol_id=MATERIALIZE_SETTLEMENT_SYMBOL_ID,
        checked_no_witness_edge_class_refs={GUARD_BEFORE_SIDE_EFFECT_REF},
    )
    checked_no_witness_row = _row_by_ref(
        checked_no_witness_ledger,
        GUARD_BEFORE_SIDE_EFFECT_REF,
    )
    assert checked_no_witness_row.adjudication_status == "checked_no_witness_found"
