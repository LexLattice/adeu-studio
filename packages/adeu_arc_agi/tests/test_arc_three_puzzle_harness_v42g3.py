from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_arc_agi import (
    ADEU_ARC_THREE_PUZZLE_HARNESS_RECORD_SCHEMA,
    AdeuArcThreePuzzleHarnessRecord,
    compute_adeu_arc_three_puzzle_harness_record_id,
    derive_v42g3_arc_three_puzzle_harness_record,
)
from adeu_arc_solver import derive_v42g3_three_puzzle_harness_record
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v95_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus95"


def _v97_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus97"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v95(name: str) -> dict[str, Any]:
    return _load_json(_v95_root() / name)


def _load_v97(name: str) -> dict[str, Any]:
    return _load_json(_v97_root() / name)


def _harness_schema_validator() -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_arc_agi"
            / "schema"
            / "adeu_arc_three_puzzle_harness_record.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _puzzle_run_inputs_from_reference(
    *,
    accepted_harness: dict[str, Any],
    run_records_by_puzzle_id: dict[str, dict[str, Any]],
) -> list[dict[str, Any]]:
    inputs: list[dict[str, Any]] = []
    for entry in accepted_harness["puzzle_run_entries"]:
        puzzle_id = entry["puzzle_id"]
        inputs.append(
            {
                "reasoning_run_record": run_records_by_puzzle_id[puzzle_id],
                "reasoning_run_record_ref": entry["reasoning_run_record_ref"],
                "local_eval_ref": entry["local_eval_ref"],
                "scorecard_manifest_ref": entry["scorecard_manifest_ref"],
                "scorecard_presence_posture": entry["scorecard_presence_posture"],
                "submission_execution_record_ref": entry["submission_execution_record_ref"],
                "submission_presence_posture": entry["submission_presence_posture"],
                "stage_evidence_ref_set": entry["stage_evidence_ref_set"],
            }
        )
    return inputs


def test_v97_reference_fixture_replays_and_validates() -> None:
    puzzle_input_bundle = _load_v95("adeu_arc_puzzle_input_bundle_v95_reference.json")
    run_records = [
        _load_v97("adeu_arc_reasoning_run_record_v97_reference_p001.json"),
        _load_v97("adeu_arc_reasoning_run_record_v97_reference_p002.json"),
        _load_v97("adeu_arc_reasoning_run_record_v97_reference_p003.json"),
    ]
    accepted_harness = _load_v97("adeu_arc_three_puzzle_harness_record_v97_reference.json")
    validated = AdeuArcThreePuzzleHarnessRecord.model_validate(accepted_harness)

    assert validated.schema == ADEU_ARC_THREE_PUZZLE_HARNESS_RECORD_SCHEMA
    assert validated.expected_puzzle_count == 3
    assert validated.selected_puzzle_ids == puzzle_input_bundle["selected_puzzle_ids"]
    assert len(validated.puzzle_run_entries) == 3

    run_records_by_puzzle_id = {run_record["puzzle_id"]: run_record for run_record in run_records}
    derived = derive_v42g3_arc_three_puzzle_harness_record(
        puzzle_input_bundle=puzzle_input_bundle,
        harness_run_id=accepted_harness["harness_run_id"],
        harness_execution_status=accepted_harness["harness_execution_status"],
        harness_sequence_register=accepted_harness["harness_sequence_register"],
        config_consistency_posture=accepted_harness["config_consistency_posture"],
        puzzle_run_inputs=_puzzle_run_inputs_from_reference(
            accepted_harness=accepted_harness,
            run_records_by_puzzle_id=run_records_by_puzzle_id,
        ),
        run_summary=accepted_harness["run_summary"],
        evidence_refs=accepted_harness["evidence_refs"],
        aggregated_local_eval_ref=accepted_harness["aggregated_local_eval_ref"],
        aggregated_scorecard_posture_ref=accepted_harness["aggregated_scorecard_posture_ref"],
        aggregated_submission_posture_ref=accepted_harness[
            "aggregated_submission_posture_ref"
        ],
    )
    assert derived == accepted_harness


def test_v97_solver_helper_replays_reference_fixture() -> None:
    puzzle_input_bundle = _load_v95("adeu_arc_puzzle_input_bundle_v95_reference.json")
    run_records = [
        _load_v97("adeu_arc_reasoning_run_record_v97_reference_p001.json"),
        _load_v97("adeu_arc_reasoning_run_record_v97_reference_p002.json"),
        _load_v97("adeu_arc_reasoning_run_record_v97_reference_p003.json"),
    ]
    accepted_harness = _load_v97("adeu_arc_three_puzzle_harness_record_v97_reference.json")
    run_records_by_puzzle_id = {run_record["puzzle_id"]: run_record for run_record in run_records}

    derived = derive_v42g3_three_puzzle_harness_record(
        puzzle_input_bundle=puzzle_input_bundle,
        harness_run_id=accepted_harness["harness_run_id"],
        harness_execution_status=accepted_harness["harness_execution_status"],
        harness_sequence_register=accepted_harness["harness_sequence_register"],
        config_consistency_posture=accepted_harness["config_consistency_posture"],
        puzzle_run_inputs=_puzzle_run_inputs_from_reference(
            accepted_harness=accepted_harness,
            run_records_by_puzzle_id=run_records_by_puzzle_id,
        ),
        run_summary=accepted_harness["run_summary"],
        evidence_refs=accepted_harness["evidence_refs"],
        aggregated_local_eval_ref=accepted_harness["aggregated_local_eval_ref"],
        aggregated_scorecard_posture_ref=accepted_harness["aggregated_scorecard_posture_ref"],
        aggregated_submission_posture_ref=accepted_harness[
            "aggregated_submission_posture_ref"
        ],
    )
    assert derived == accepted_harness


def test_v97_id_is_deterministic() -> None:
    payload = _load_v97("adeu_arc_three_puzzle_harness_record_v97_reference.json")
    without_id = deepcopy(payload)
    without_id.pop("three_puzzle_harness_record_id")
    assert (
        compute_adeu_arc_three_puzzle_harness_record_id(without_id)
        == payload["three_puzzle_harness_record_id"]
    )


def test_v97_exported_schema_accepts_reference_fixture() -> None:
    _harness_schema_validator().validate(
        _load_v97("adeu_arc_three_puzzle_harness_record_v97_reference.json")
    )


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "adeu_arc_three_puzzle_harness_record_v97_reject_retroactive_selection_swap.json",
            "selected_puzzle_ids must be sorted lexicographically",
        ),
        (
            "adeu_arc_three_puzzle_harness_record_v97_reject_canonical_order_violation.json",
            "puzzle_run_entries must be in canonical puzzle_index order",
        ),
        (
            "adeu_arc_three_puzzle_harness_record_v97_reject_duplicate_puzzle_identity.json",
            "puzzle_run_entries puzzle_id order must follow canonical_puzzle_order",
        ),
        (
            "adeu_arc_three_puzzle_harness_record_v97_reject_omitted_third_entry_laundering.json",
            "at least 3 items",
        ),
        (
            "adeu_arc_three_puzzle_harness_record_v97_reject_identity_chain_mismatch.json",
            "duplicate puzzle_input_id",
        ),
        (
            "adeu_arc_three_puzzle_harness_record_v97_reject_untyped_config_drift.json",
            "uniform config_consistency_posture",
        ),
        (
            "adeu_arc_three_puzzle_harness_record_v97_reject_missing_monotonic_sequence_evidence.json",
            "sequence_step values must be exactly \\[1,2,3\\]",
        ),
        (
            "adeu_arc_three_puzzle_harness_record_v97_reject_aggregated_ref_contradiction.json",
            "aggregated_local_eval_ref must match canonical aggregate",
        ),
    ],
)
def test_v97_rejects_invalid_harness_fixtures(fixture_name: str, match: str) -> None:
    payload = _load_v97(fixture_name)
    with pytest.raises(ValidationError, match=match):
        AdeuArcThreePuzzleHarnessRecord.model_validate(payload)
