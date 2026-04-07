from __future__ import annotations

from typing import Iterable

from .models import (
    SymbolEdgeAdjudicationLedger,
    SymbolEdgeAdjudicationRow,
    SymbolEdgeApplicabilityFrame,
    WitnessSummaryRecord,
    _sha256_canonical_payload,
    compute_symbol_edge_adjudication_ledger_id,
)

UNDERDETERMINED_PROMOTION_DEFERRAL_REASON = (
    "starter_v53b_does_not_permit_positive_promotion_from_underdetermined_applicability"
)


def _normalize_witness_summaries(
    witness_summaries: Iterable[WitnessSummaryRecord | dict[str, object]],
) -> list[WitnessSummaryRecord]:
    records = [
        witness
        if isinstance(witness, WitnessSummaryRecord)
        else WitnessSummaryRecord.model_validate(witness)
        for witness in witness_summaries
    ]
    witness_refs = [record.witness_ref for record in records]
    if len(witness_refs) != len(set(witness_refs)):
        raise ValueError("witness_summaries witness_ref values must be unique")
    return records


def _normalize_checked_no_witness_edge_class_refs(
    edge_class_refs: Iterable[str],
) -> list[str]:
    ordered = list(edge_class_refs)
    if len(ordered) != len(set(ordered)):
        raise ValueError("checked_no_witness_edge_class_refs must be unique")
    return ordered


def derive_symbol_edge_adjudication_ledger(
    *,
    applicability_frame: SymbolEdgeApplicabilityFrame,
    witness_summaries: Iterable[WitnessSummaryRecord | dict[str, object]] = (),
    checked_no_witness_edge_class_refs: Iterable[str] = (),
) -> SymbolEdgeAdjudicationLedger:
    witness_records = _normalize_witness_summaries(witness_summaries)
    checked_refs = _normalize_checked_no_witness_edge_class_refs(
        checked_no_witness_edge_class_refs
    )

    frame_rows_by_ref = {row.edge_class_ref: row for row in applicability_frame.applicability_rows}

    for record in witness_records:
        if record.edge_class_ref not in frame_rows_by_ref:
            raise ValueError("witness_summaries edge_class_ref must exist in applicability frame")
    for edge_class_ref in checked_refs:
        if edge_class_ref not in frame_rows_by_ref:
            raise ValueError(
                "checked_no_witness_edge_class_refs must exist in applicability frame"
            )

    witness_edge_refs = {record.edge_class_ref for record in witness_records}
    contradictory_refs = witness_edge_refs & set(checked_refs)
    if contradictory_refs:
        raise ValueError("contradictory override input is not allowed")

    for edge_class_ref in list(witness_edge_refs) + checked_refs:
        if frame_rows_by_ref[edge_class_ref].applicability_status == "not_applicable":
            raise ValueError("explicit override input is forbidden for not_applicable rows")

    witness_refs_by_edge: dict[str, list[str]] = {}
    for record in witness_records:
        witness_refs_by_edge.setdefault(record.edge_class_ref, []).append(record.witness_ref)

    rows: list[SymbolEdgeAdjudicationRow] = []
    for applicability_row in applicability_frame.applicability_rows:
        edge_class_ref = applicability_row.edge_class_ref
        source_status = applicability_row.applicability_status
        supporting_witness_refs = witness_refs_by_edge.get(edge_class_ref, [])
        supporting_checked_refs = [edge_class_ref] if edge_class_ref in checked_refs else []

        if source_status == "not_applicable":
            adjudication_status = "not_applicable"
            deferral_reason = None
            supporting_witness_refs = []
            supporting_checked_refs = []
        elif source_status == "applicable":
            if supporting_witness_refs:
                adjudication_status = "witness_found"
                deferral_reason = None
                supporting_checked_refs = []
            elif supporting_checked_refs:
                adjudication_status = "checked_no_witness_found"
                deferral_reason = None
                supporting_witness_refs = []
            else:
                adjudication_status = "applicable_unchecked"
                deferral_reason = None
        else:
            if supporting_witness_refs or supporting_checked_refs:
                adjudication_status = "deferred"
                deferral_reason = UNDERDETERMINED_PROMOTION_DEFERRAL_REASON
            else:
                adjudication_status = "underdetermined"
                deferral_reason = None

        rows.append(
            SymbolEdgeAdjudicationRow(
                edge_class_ref=edge_class_ref,
                source_applicability_status=source_status,
                adjudication_status=adjudication_status,
                supporting_witness_refs=supporting_witness_refs,
                supporting_checked_no_witness_refs=supporting_checked_refs,
                deferral_reason=deferral_reason,
            )
        )

    payload_without_id = {
        "schema": SymbolEdgeAdjudicationLedger.model_fields["schema_id"].default,
        "applicability_frame_ref": applicability_frame.frame_id,
        "bound_edge_class_catalog_ref": applicability_frame.bound_edge_class_catalog_ref,
        "bound_probe_template_catalog_ref": applicability_frame.bound_probe_template_catalog_ref,
        "symbol_id": applicability_frame.symbol_id,
        "module_path": applicability_frame.module_path,
        "qualname": applicability_frame.qualname,
        "symbol_kind": applicability_frame.symbol_kind,
        "adjudication_rows": [row.model_dump(mode="json", exclude_none=True) for row in rows],
    }
    ledger_hash = _sha256_canonical_payload(payload_without_id)
    return SymbolEdgeAdjudicationLedger(
        ledger_id=compute_symbol_edge_adjudication_ledger_id(
            {
                **payload_without_id,
                "ledger_hash": ledger_hash,
            }
        ),
        applicability_frame_ref=applicability_frame.frame_id,
        bound_edge_class_catalog_ref=applicability_frame.bound_edge_class_catalog_ref,
        bound_probe_template_catalog_ref=applicability_frame.bound_probe_template_catalog_ref,
        symbol_id=applicability_frame.symbol_id,
        module_path=applicability_frame.module_path,
        qualname=applicability_frame.qualname,
        symbol_kind=applicability_frame.symbol_kind,
        adjudication_rows=rows,
        ledger_hash=ledger_hash,
    )


def validate_symbol_edge_adjudication_ledger_bindings(
    *,
    ledger_payload: dict[str, object],
    applicability_frame: SymbolEdgeApplicabilityFrame,
) -> SymbolEdgeAdjudicationLedger:
    ledger = SymbolEdgeAdjudicationLedger.model_validate(ledger_payload)
    if ledger.applicability_frame_ref != applicability_frame.frame_id:
        raise ValueError("ledger applicability_frame_ref must match the bound frame")
    if ledger.bound_edge_class_catalog_ref != applicability_frame.bound_edge_class_catalog_ref:
        raise ValueError("ledger must preserve bound_edge_class_catalog_ref from the frame")
    if (
        ledger.bound_probe_template_catalog_ref
        != applicability_frame.bound_probe_template_catalog_ref
    ):
        raise ValueError("ledger must preserve bound_probe_template_catalog_ref from the frame")
    if ledger.symbol_id != applicability_frame.symbol_id:
        raise ValueError("ledger symbol_id must match the bound frame")
    if ledger.module_path != applicability_frame.module_path:
        raise ValueError("ledger module_path must match the bound frame")
    if ledger.qualname != applicability_frame.qualname:
        raise ValueError("ledger qualname must match the bound frame")
    if ledger.symbol_kind != applicability_frame.symbol_kind:
        raise ValueError("ledger symbol_kind must match the bound frame")

    frame_rows = applicability_frame.applicability_rows
    if [row.edge_class_ref for row in ledger.adjudication_rows] != [
        row.edge_class_ref for row in frame_rows
    ]:
        raise ValueError("ledger rows must cover every frame row exactly once in frame order")

    for ledger_row, frame_row in zip(ledger.adjudication_rows, frame_rows, strict=True):
        if ledger_row.source_applicability_status != frame_row.applicability_status:
            raise ValueError(
                "ledger source_applicability_status must match the bound applicability frame"
            )
    return ledger


__all__ = [
    "UNDERDETERMINED_PROMOTION_DEFERRAL_REASON",
    "derive_symbol_edge_adjudication_ledger",
    "validate_symbol_edge_adjudication_ledger_bindings",
]
