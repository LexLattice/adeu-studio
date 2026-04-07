from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_edge_ledger import (
    SymbolEdgeAdjudicationLedger,
    SymbolEdgeApplicabilityFrame,
    SymbolEdgeApplicabilityRow,
    WitnessSummaryRecord,
    compute_symbol_edge_applicability_frame_id,
    derive_symbol_edge_adjudication_ledger,
    validate_symbol_edge_adjudication_ledger_bindings,
)
from adeu_edge_ledger.models import _sha256_canonical_payload
from pydantic import ValidationError

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v53b"


def _load_json(name: str) -> dict[str, object]:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _reference_adjudication_frame(released_stack, starter_catalogs) -> SymbolEdgeApplicabilityFrame:
    _repo_root, manifest, census, _coverage, _audit = released_stack
    edge_catalog, probe_catalog = starter_catalogs
    symbol = census.symbols[0]
    rows = [
        SymbolEdgeApplicabilityRow(
            edge_class_ref="edge_class:boundary_order/numeric_interval/inclusive_exclusive_boundary",
            applicability_status="underdetermined",
            epistemic_posture="inferred_heuristically",
            matched_cue_tags=["feature:boundary_terms", "feature:scope_terms"],
            concrete_binding_refs=["param:repository_root"],
            suggested_probe_template_refs=[
                "probe:boundary_partition",
                "probe:dependency_boundary_fault",
            ],
            rationale="starter underdetermined reference",
        ),
        SymbolEdgeApplicabilityRow(
            edge_class_ref="edge_class:boundary_order/ordering_permutation/stable_ordering_preservation",
            applicability_status="not_applicable",
            epistemic_posture="derived_deterministically",
            matched_cue_tags=[],
            concrete_binding_refs=[],
            suggested_probe_template_refs=["probe:ordering_permutation"],
            rationale="starter not applicable reference",
        ),
        SymbolEdgeApplicabilityRow(
            edge_class_ref="edge_class:canonicalization_representation/normalization_canonical_form/path_or_text_normalization",
            applicability_status="applicable",
            epistemic_posture="derived_deterministically",
            matched_cue_tags=["feature:path_like", "feature:scope_terms"],
            concrete_binding_refs=["param:repository_root", "symbol:_sha256_repo_file"],
            suggested_probe_template_refs=["probe:normalization_round_trip"],
            rationale="starter applicable unchecked reference",
        ),
        SymbolEdgeApplicabilityRow(
            edge_class_ref="edge_class:canonicalization_representation/serialization_identity/round_trip_serialization",
            applicability_status="applicable",
            epistemic_posture="derived_deterministically",
            matched_cue_tags=["feature:model_dump_call"],
            concrete_binding_refs=["call:model_dump"],
            suggested_probe_template_refs=["probe:round_trip_and_idempotence"],
            rationale="starter witness-found reference",
        ),
        SymbolEdgeApplicabilityRow(
            edge_class_ref="edge_class:contract_invariant/cross_field_binding/cross_field_consistency",
            applicability_status="applicable",
            epistemic_posture="derived_deterministically",
            matched_cue_tags=["feature:has_compare"],
            concrete_binding_refs=["line:101"],
            suggested_probe_template_refs=["probe:cross_field_invariant"],
            rationale="starter checked-no-witness reference",
        ),
        SymbolEdgeApplicabilityRow(
            edge_class_ref="edge_class:contract_invariant/vocabulary_order_identity/ordered_unique_sequence_invariant",
            applicability_status="underdetermined",
            epistemic_posture="inferred_heuristically",
            matched_cue_tags=["feature:membership_check"],
            concrete_binding_refs=["line:88"],
            suggested_probe_template_refs=["probe:ordering_permutation"],
            rationale="starter underdetermined carry-forward reference",
        ),
    ]
    payload_without_id = {
        "schema": "adeu_symbol_edge_applicability_frame@1",
        "bound_edge_class_catalog_ref": edge_catalog.catalog_id,
        "bound_probe_template_catalog_ref": probe_catalog.catalog_id,
        "scope_manifest_ref": manifest.scope_manifest_id,
        "census_hash": census.census_hash,
        "audit_hash": "12906d927f08fbfeb52fa384eedb0ce8e70d982810ffb2f0836939ba354242d6",
        "symbol_id": symbol.symbol_id,
        "module_path": symbol.module_path,
        "qualname": symbol.qualname,
        "symbol_kind": symbol.symbol_kind,
        "frame_posture": "starter_taxonomy_applicability_over_released_v50_pilot_scope",
        "applicability_rows": [row.model_dump(mode="json", exclude_none=True) for row in rows],
    }
    frame_hash = _sha256_canonical_payload(payload_without_id)
    return SymbolEdgeApplicabilityFrame(
        frame_id=compute_symbol_edge_applicability_frame_id(
            {
                **payload_without_id,
                "frame_hash": frame_hash,
            }
        ),
        bound_edge_class_catalog_ref=edge_catalog.catalog_id,
        bound_probe_template_catalog_ref=probe_catalog.catalog_id,
        scope_manifest_ref=manifest.scope_manifest_id,
        census_hash=census.census_hash,
        audit_hash="12906d927f08fbfeb52fa384eedb0ce8e70d982810ffb2f0836939ba354242d6",
        symbol_id=symbol.symbol_id,
        module_path=symbol.module_path,
        qualname=symbol.qualname,
        symbol_kind=symbol.symbol_kind,
        frame_posture="starter_taxonomy_applicability_over_released_v50_pilot_scope",
        applicability_rows=rows,
        frame_hash=frame_hash,
    )


def test_reference_adjudication_ledger_replays_deterministically(
    released_stack,
    starter_catalogs,
) -> None:
    frame = _reference_adjudication_frame(released_stack, starter_catalogs)
    expected_payload = _load_json("reference_symbol_edge_adjudication_ledger.json")

    ledger = derive_symbol_edge_adjudication_ledger(
        applicability_frame=frame,
        witness_summaries=[
            WitnessSummaryRecord(
                witness_ref="witness:inclusive_boundary_example",
                edge_class_ref="edge_class:boundary_order/numeric_interval/inclusive_exclusive_boundary",
                summary_text="explicit inclusive/exclusive witness",
            ),
            WitnessSummaryRecord(
                witness_ref="witness:round_trip_serialization_example",
                edge_class_ref="edge_class:canonicalization_representation/serialization_identity/round_trip_serialization",
                summary_text="explicit round-trip serialization witness",
            ),
        ],
        checked_no_witness_edge_class_refs=[
            "edge_class:contract_invariant/cross_field_binding/cross_field_consistency"
        ],
    )

    assert ledger.model_dump(mode="json", by_alias=True, exclude_none=True) == expected_payload
    rebound = validate_symbol_edge_adjudication_ledger_bindings(
        ledger_payload=expected_payload,
        applicability_frame=frame,
    )
    assert rebound.model_dump(mode="json", by_alias=True, exclude_none=True) == expected_payload


def test_reject_contradictory_and_out_of_frame_override_inputs(
    released_stack,
    starter_catalogs,
) -> None:
    frame = _reference_adjudication_frame(released_stack, starter_catalogs)

    with pytest.raises(ValueError, match="contradictory override input"):
        derive_symbol_edge_adjudication_ledger(
            applicability_frame=frame,
            witness_summaries=[
                _load_json("reject_contradictory_witness_input.json"),
            ],
            checked_no_witness_edge_class_refs=[
                "edge_class:canonicalization_representation/serialization_identity/round_trip_serialization"
            ],
        )

    with pytest.raises(ValueError, match="must exist in applicability frame"):
        derive_symbol_edge_adjudication_ledger(
            applicability_frame=frame,
            witness_summaries=[],
            checked_no_witness_edge_class_refs=[
                "edge_class:state_sequence/temporal_reentry/repeat_application_idempotence"
            ],
        )


def test_reject_not_applicable_override_and_support_ref_drift(
    released_stack,
    starter_catalogs,
) -> None:
    frame = _reference_adjudication_frame(released_stack, starter_catalogs)

    with pytest.raises(ValueError, match="forbidden for not_applicable rows"):
        derive_symbol_edge_adjudication_ledger(
            applicability_frame=frame,
            witness_summaries=[
                WitnessSummaryRecord(
                    witness_ref="witness:not_applicable_override",
                    edge_class_ref="edge_class:boundary_order/ordering_permutation/stable_ordering_preservation",
                    summary_text="invalid override against not_applicable row",
                )
            ],
        )

    payload = _load_json("reference_symbol_edge_adjudication_ledger.json")
    payload["adjudication_rows"][4]["supporting_checked_no_witness_refs"] = [
        "edge_class:contract_invariant/vocabulary_order_identity/ordered_unique_sequence_invariant"
    ]
    with pytest.raises(
        ValidationError,
        match="starter checked-no-witness support ref",
    ):
        SymbolEdgeAdjudicationLedger.model_validate(payload)
