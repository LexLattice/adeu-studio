from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_arc_agi import (
    ADEU_ARC_PUZZLE_INPUT_BUNDLE_SCHEMA,
    AdeuArcPuzzleInputBundle,
    compute_adeu_arc_bundle_identity_hash,
    compute_adeu_arc_puzzle_input_bundle_id,
    compute_adeu_arc_selection_register_hash,
    compute_adeu_arc_selection_register_id,
    derive_v42g1_arc_puzzle_input_bundle,
    materialize_adeu_arc_puzzle_input_bundle_payload,
)
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v95_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus95"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v95(name: str) -> dict[str, Any]:
    return _load_json(_v95_root() / name)


def _bundle_schema_validator() -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_arc_agi"
            / "schema"
            / "adeu_arc_puzzle_input_bundle.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _entry_inputs_from_bundle(bundle: dict[str, Any]) -> list[dict[str, Any]]:
    entry_inputs: list[dict[str, Any]] = []
    for entry in bundle["puzzle_entries"]:
        entry_inputs.append(
            {
                "puzzle_id": entry["puzzle_id"],
                "source_kind": entry["source_kind"],
                "source_ref": entry["source_ref"],
                "normalized_payload_ref": entry["normalized_payload_ref"],
                "normalized_payload": entry["normalized_payload"],
                "provenance_refs": entry["provenance_refs"],
            }
        )
    return entry_inputs


def test_v95_reference_fixture_replays_and_validates() -> None:
    selection_register = _load_v95("adeu_arc_puzzle_selection_register_v95_reference.json")
    bundle = _load_v95("adeu_arc_puzzle_input_bundle_v95_reference.json")
    validated = AdeuArcPuzzleInputBundle.model_validate(bundle)

    assert validated.schema == ADEU_ARC_PUZZLE_INPUT_BUNDLE_SCHEMA
    assert validated.summary_non_authoritative is True
    assert validated.no_retrospective_swap_posture is True
    assert validated.source_precedence_policy == [
        "repo_frozen_fixture",
        "official_toolkit_local_export",
        "approved_imported_local_copy",
    ]
    assert validated.selected_puzzle_ids == selection_register["selected_puzzle_ids"]

    derived = derive_v42g1_arc_puzzle_input_bundle(
        selection_register_ref=bundle["selection_register_ref"],
        selection_basis=bundle["selection_basis"],
        selected_puzzle_ids=bundle["selected_puzzle_ids"],
        source_profile=bundle["source_profile"],
        puzzle_entries=_entry_inputs_from_bundle(bundle),
        provenance_refs=bundle["provenance_refs"],
        evidence_refs=bundle["evidence_refs"],
        source_precedence_policy=bundle["source_precedence_policy"],
        no_retrospective_swap_posture=bundle["no_retrospective_swap_posture"],
        summary_non_authoritative=bundle["summary_non_authoritative"],
    )
    assert derived == bundle


def test_v95_bundle_id_is_deterministic() -> None:
    payload = _load_v95("adeu_arc_puzzle_input_bundle_v95_reference.json")
    without_id = deepcopy(payload)
    without_id.pop("puzzle_input_bundle_id")
    assert (
        compute_adeu_arc_puzzle_input_bundle_id(without_id)
        == payload["puzzle_input_bundle_id"]
    )


def test_v95_materialize_defaults_booleans_before_bundle_id() -> None:
    payload = _load_v95("adeu_arc_puzzle_input_bundle_v95_reference.json")
    without_id = deepcopy(payload)
    without_id.pop("puzzle_input_bundle_id")
    without_id.pop("no_retrospective_swap_posture")
    without_id.pop("summary_non_authoritative")

    materialized = materialize_adeu_arc_puzzle_input_bundle_payload(without_id)
    assert materialized == payload


def test_v95_exported_schema_accepts_reference_fixture() -> None:
    _bundle_schema_validator().validate(_load_v95("adeu_arc_puzzle_input_bundle_v95_reference.json"))


def test_v95_reference_fixture_is_exactly_three_distinct_selected_puzzles() -> None:
    payload = _load_v95("adeu_arc_puzzle_input_bundle_v95_reference.json")
    validated = AdeuArcPuzzleInputBundle.model_validate(payload)
    assert len(validated.selected_puzzle_ids) == 3
    assert len(set(validated.selected_puzzle_ids)) == 3
    assert validated.canonical_puzzle_order == validated.selected_puzzle_ids


def test_v95_rejects_missing_provenance_refs_fixture() -> None:
    payload = _load_v95("adeu_arc_puzzle_input_bundle_v95_reject_missing_provenance_refs.json")
    with pytest.raises(
        ValidationError, match="provenance_refs must include selection_register_ref"
    ):
        AdeuArcPuzzleInputBundle.model_validate(payload)


def test_v95_rejects_source_kind_drift() -> None:
    payload = deepcopy(_load_v95("adeu_arc_puzzle_input_bundle_v95_reference.json"))
    payload["puzzle_entries"][0]["source_kind"] = "open_text_source_kind_drift"
    with pytest.raises(
        ValidationError,
        match="repo_frozen_fixture|official_toolkit_local_export|approved_imported_local_copy",
    ):
        AdeuArcPuzzleInputBundle.model_validate(payload)


def test_v95_rejects_per_puzzle_identity_hash_mismatch_fixture() -> None:
    payload = _load_v95(
        "adeu_arc_puzzle_input_bundle_v95_reject_per_puzzle_identity_hash_mismatch.json"
    )
    with pytest.raises(ValidationError, match="puzzle_identity_hash must match"):
        AdeuArcPuzzleInputBundle.model_validate(payload)


def test_v95_rejects_bundle_identity_hash_mismatch_fixture() -> None:
    payload = _load_v95(
        "adeu_arc_puzzle_input_bundle_v95_reject_bundle_identity_hash_mismatch.json"
    )
    with pytest.raises(ValidationError, match="bundle_identity_hash must match"):
        AdeuArcPuzzleInputBundle.model_validate(payload)


def test_v95_rejects_non_declared_retrospective_swap_fixture() -> None:
    payload = _load_v95("adeu_arc_puzzle_input_bundle_v95_reject_retroactive_selection_swap.json")
    with pytest.raises(ValidationError, match="puzzle_entries must follow canonical_puzzle_order"):
        AdeuArcPuzzleInputBundle.model_validate(payload)


def test_v95_rejects_selection_register_ref_payload_drift_even_if_recomputed() -> None:
    payload = deepcopy(_load_v95("adeu_arc_puzzle_input_bundle_v95_reference.json"))
    swapped_ids = [
        payload["selected_puzzle_ids"][1],
        payload["selected_puzzle_ids"][0],
        payload["selected_puzzle_ids"][2],
    ]
    payload["selected_puzzle_ids"] = swapped_ids
    payload["canonical_puzzle_order"] = swapped_ids
    payload["puzzle_entries"] = [
        payload["puzzle_entries"][1],
        payload["puzzle_entries"][0],
        payload["puzzle_entries"][2],
    ]
    payload["selection_register_id"] = compute_adeu_arc_selection_register_id(
        selection_basis=payload["selection_basis"],
        selected_puzzle_ids=swapped_ids,
        no_retrospective_swap_posture=payload["no_retrospective_swap_posture"],
    )
    payload["selection_register_hash"] = compute_adeu_arc_selection_register_hash(
        selection_register_id=payload["selection_register_id"],
        selection_basis=payload["selection_basis"],
        selected_puzzle_ids=swapped_ids,
        no_retrospective_swap_posture=payload["no_retrospective_swap_posture"],
    )
    payload["bundle_identity_hash"] = compute_adeu_arc_bundle_identity_hash(
        selection_register_hash=payload["selection_register_hash"],
        canonical_puzzle_order=swapped_ids,
        puzzle_entries=payload["puzzle_entries"],
    )
    payload_without_id = deepcopy(payload)
    payload_without_id.pop("puzzle_input_bundle_id")
    payload["puzzle_input_bundle_id"] = compute_adeu_arc_puzzle_input_bundle_id(payload_without_id)

    with pytest.raises(
        ValidationError,
        match=(
            "selection_register_id must match authoritative "
            "selection_register_ref payload"
        ),
    ):
        AdeuArcPuzzleInputBundle.model_validate(payload)


def test_v95_rejects_duplicate_puzzle_identity_fixture() -> None:
    payload = _load_v95("adeu_arc_puzzle_input_bundle_v95_reject_duplicate_puzzle_identity.json")
    with pytest.raises(ValidationError, match="duplicate puzzle identity hashes"):
        AdeuArcPuzzleInputBundle.model_validate(payload)
