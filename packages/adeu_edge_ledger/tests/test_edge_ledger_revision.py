from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest
from adeu_edge_ledger import (
    EdgeTaxonomyRevisionEntry,
    EdgeTaxonomyRevisionRegister,
    SymbolEdgeAdjudicationLedger,
    compute_edge_taxonomy_revision_register_id,
    derive_edge_taxonomy_revision_register,
    validate_edge_taxonomy_revision_register_bindings,
)
from pydantic import ValidationError

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v53c"
ADJUDICATION_FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v53b"


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v53c_fixture(name: str) -> dict[str, object]:
    return _load_json(FIXTURE_ROOT / name)


def _reference_adjudication_ledger() -> SymbolEdgeAdjudicationLedger:
    return SymbolEdgeAdjudicationLedger.model_validate(
        _load_json(ADJUDICATION_FIXTURE_ROOT / "reference_symbol_edge_adjudication_ledger.json")
    )


def _canonicalize_register_payload(payload: dict[str, object]) -> dict[str, object]:
    payload_without_identity = {
        "schema": payload["schema"],
        "bound_edge_class_catalog_ref": payload["bound_edge_class_catalog_ref"],
        "bound_probe_template_catalog_ref": payload["bound_probe_template_catalog_ref"],
        "bound_adjudication_ledger_ref": payload["bound_adjudication_ledger_ref"],
        "prior_revision_register_ref": payload.get("prior_revision_register_ref"),
        "revision_entries": payload["revision_entries"],
    }
    register_hash = hashlib.sha256(
        json.dumps(
            payload_without_identity,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()
    return {
        **payload,
        "register_hash": register_hash,
        "register_id": compute_edge_taxonomy_revision_register_id(
            {
                **payload_without_identity,
                "register_hash": register_hash,
            }
        ),
    }


def test_reference_revision_register_initial_replays_deterministically() -> None:
    ledger = _reference_adjudication_ledger()
    expected_payload = _load_v53c_fixture("reference_edge_taxonomy_revision_register_initial.json")

    register = derive_edge_taxonomy_revision_register(
        adjudication_ledger=ledger,
        revision_entries=expected_payload["revision_entries"],
    )

    assert register.model_dump(mode="json", by_alias=True, exclude_none=True) == expected_payload
    rebound = validate_edge_taxonomy_revision_register_bindings(
        register_payload=expected_payload,
        adjudication_ledger=ledger,
    )
    assert rebound.model_dump(mode="json", by_alias=True, exclude_none=True) == expected_payload


def test_reference_revision_register_append_replays_deterministically() -> None:
    ledger = _reference_adjudication_ledger()
    initial_payload = _load_v53c_fixture("reference_edge_taxonomy_revision_register_initial.json")
    append_payload = _load_v53c_fixture("reference_edge_taxonomy_revision_register_append.json")

    initial_register = EdgeTaxonomyRevisionRegister.model_validate(initial_payload)
    append_register = derive_edge_taxonomy_revision_register(
        adjudication_ledger=ledger,
        prior_revision_register=initial_register,
        revision_entries=[append_payload["revision_entries"][-1]],
    )

    assert (
        append_register.model_dump(mode="json", by_alias=True, exclude_none=True) == append_payload
    )
    rebound = validate_edge_taxonomy_revision_register_bindings(
        register_payload=append_payload,
        adjudication_ledger=ledger,
        prior_revision_register=initial_register,
    )
    assert rebound.model_dump(mode="json", by_alias=True, exclude_none=True) == append_payload


def test_revision_entry_validator_rejects_unexpected_decision_value() -> None:
    entry_payload = _load_v53c_fixture("reference_edge_taxonomy_revision_register_initial.json")[
        "revision_entries"
    ][0]
    entry = EdgeTaxonomyRevisionEntry.model_construct(
        **{
            **entry_payload,
            "revision_decision": "unexpected_revision_decision",
        }
    )

    with pytest.raises(
        ValueError,
        match="unexpected revision_decision 'unexpected_revision_decision'",
    ):
        entry._validate()


@pytest.mark.parametrize(
    ("fixture_name", "expected_message"),
    [
        (
            "reject_edge_taxonomy_revision_register_unknown_parent.json",
            "lineage_parent_entry_refs must resolve inside revision_entries",
        ),
        (
            "reject_edge_taxonomy_revision_register_lineage_cycle.json",
            "lineage_parent_entry_refs must not form cycles",
        ),
        (
            "reject_edge_taxonomy_revision_register_supporting_ledger_drift.json",
            "supporting_adjudication_ledger_ref must match bound_adjudication_ledger_ref",
        ),
        (
            "reject_edge_taxonomy_revision_register_invalid_decision_shape.json",
            "split_existing_class requires exactly one subject ref and non-empty candidate refs",
        ),
        (
            "reject_edge_taxonomy_revision_register_duplicate_candidate_ref.json",
            "candidate_edge_class_refs must be unique",
        ),
        (
            "reject_edge_taxonomy_revision_register_overlapping_candidate_ref.json",
            "candidate_edge_class_refs must not overlap subject_edge_class_refs",
        ),
        (
            "reject_edge_taxonomy_revision_register_inadmissible_candidate_ref.json",
            "candidate_edge_class_refs must use the edge_class: prefix",
        ),
    ],
)
def test_reject_intrinsic_revision_register_shape_fixtures(
    fixture_name: str,
    expected_message: str,
) -> None:
    with pytest.raises(ValidationError, match=expected_message):
        EdgeTaxonomyRevisionRegister.model_validate(_load_v53c_fixture(fixture_name))


@pytest.mark.parametrize(
    ("fixture_name", "expected_message", "requires_prior"),
    [
        (
            "reject_edge_taxonomy_revision_register_cross_ledger_append.json",
            "register must bind the current released adjudication ledger",
            True,
        ),
        (
            "reject_edge_taxonomy_revision_register_deferred_only_support.json",
            "must not use deferred adjudication rows as sole support",
            False,
        ),
        (
            "reject_edge_taxonomy_revision_register_unsupported_status_only_support.json",
            "require at least one witness_found or checked_no_witness_found support row",
            False,
        ),
    ],
)
def test_reject_binding_law_fixtures(
    fixture_name: str,
    expected_message: str,
    requires_prior: bool,
) -> None:
    ledger = _reference_adjudication_ledger()
    prior_register = None
    if requires_prior:
        prior_register = EdgeTaxonomyRevisionRegister.model_validate(
            _load_v53c_fixture("reference_edge_taxonomy_revision_register_initial.json")
        )

    with pytest.raises(ValueError, match=expected_message):
        validate_edge_taxonomy_revision_register_bindings(
            register_payload=_load_v53c_fixture(fixture_name),
            adjudication_ledger=ledger,
            prior_revision_register=prior_register,
        )


def test_reject_append_prefix_rewrite() -> None:
    ledger = _reference_adjudication_ledger()
    initial_payload = _load_v53c_fixture("reference_edge_taxonomy_revision_register_initial.json")
    append_payload = _load_v53c_fixture("reference_edge_taxonomy_revision_register_append.json")
    initial_register = EdgeTaxonomyRevisionRegister.model_validate(initial_payload)

    rewritten = dict(append_payload)
    rewritten["revision_entries"] = [dict(entry) for entry in append_payload["revision_entries"]]
    rewritten["revision_entries"][0]["rationale"] = "rewritten preserved prefix entry"
    rewritten = _canonicalize_register_payload(rewritten)

    with pytest.raises(ValueError, match="preserve prior revision entry order exactly"):
        validate_edge_taxonomy_revision_register_bindings(
            register_payload=rewritten,
            adjudication_ledger=ledger,
            prior_revision_register=initial_register,
        )
