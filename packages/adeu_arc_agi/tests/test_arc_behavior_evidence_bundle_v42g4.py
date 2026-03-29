from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_arc_agi import (
    ADEU_ARC_BEHAVIOR_EVIDENCE_BUNDLE_SCHEMA,
    AdeuArcBehaviorEvidenceBundle,
    compute_adeu_arc_behavior_evidence_bundle_id,
    derive_v42g4_arc_behavior_evidence_bundle,
)
from adeu_arc_solver import derive_v42g4_behavior_evidence_bundle
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v97_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus97"


def _v98_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus98"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v97(name: str) -> dict[str, Any]:
    return _load_json(_v97_root() / name)


def _load_v98(name: str) -> dict[str, Any]:
    return _load_json(_v98_root() / name)


def _behavior_schema_validator() -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_arc_agi"
            / "schema"
            / "adeu_arc_behavior_evidence_bundle.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _per_puzzle_behavior_inputs_from_reference(
    *, accepted_bundle: dict[str, Any]
) -> list[dict[str, Any]]:
    return [
        {
            "puzzle_id": entry["puzzle_id"],
            "reasoning_run_record_ref": entry["reasoning_run_record_ref"],
            "local_eval_ref": entry["local_eval_ref"],
            "scorecard_manifest_ref": entry["scorecard_manifest_ref"],
            "submission_execution_record_ref": entry["submission_execution_record_ref"],
            "behavior_signal_refs": entry["behavior_signal_refs"],
            "mapped_failure_mode_ids": entry["mapped_failure_mode_ids"],
            "claim_posture": entry["claim_posture"],
        }
        for entry in accepted_bundle["per_puzzle_behavior_entries"]
    ]


def test_v98_reference_fixture_replays_and_validates() -> None:
    accepted_bundle = _load_v98("adeu_arc_behavior_evidence_bundle_v98_reference.json")
    harness = _load_v97("adeu_arc_three_puzzle_harness_record_v97_reference.json")
    validated = AdeuArcBehaviorEvidenceBundle.model_validate(accepted_bundle)

    assert validated.schema == ADEU_ARC_BEHAVIOR_EVIDENCE_BUNDLE_SCHEMA
    assert validated.harness_record_id == harness["three_puzzle_harness_record_id"]
    assert len(validated.per_puzzle_behavior_entries) == 3

    derived = derive_v42g4_arc_behavior_evidence_bundle(
        three_puzzle_harness_record=harness,
        per_puzzle_behavior_inputs=_per_puzzle_behavior_inputs_from_reference(
            accepted_bundle=accepted_bundle
        ),
        cross_puzzle_pattern_entries=accepted_bundle["cross_puzzle_pattern_entries"],
        failure_mode_catalog=accepted_bundle["failure_mode_catalog"],
        claim_posture_register=accepted_bundle["claim_posture_register"],
        authority_boundary_register=accepted_bundle["authority_boundary_register"],
        deterministic_replay_scope_note=accepted_bundle["deterministic_replay_scope_note"],
        behavior_summary=accepted_bundle["behavior_summary"],
        evidence_refs=accepted_bundle["evidence_refs"],
    )
    assert derived == accepted_bundle


def test_v98_solver_helper_replays_reference_fixture() -> None:
    accepted_bundle = _load_v98("adeu_arc_behavior_evidence_bundle_v98_reference.json")
    harness = _load_v97("adeu_arc_three_puzzle_harness_record_v97_reference.json")

    derived = derive_v42g4_behavior_evidence_bundle(
        three_puzzle_harness_record=harness,
        per_puzzle_behavior_inputs=_per_puzzle_behavior_inputs_from_reference(
            accepted_bundle=accepted_bundle
        ),
        cross_puzzle_pattern_entries=accepted_bundle["cross_puzzle_pattern_entries"],
        failure_mode_catalog=accepted_bundle["failure_mode_catalog"],
        claim_posture_register=accepted_bundle["claim_posture_register"],
        authority_boundary_register=accepted_bundle["authority_boundary_register"],
        deterministic_replay_scope_note=accepted_bundle["deterministic_replay_scope_note"],
        behavior_summary=accepted_bundle["behavior_summary"],
        evidence_refs=accepted_bundle["evidence_refs"],
    )
    assert derived == accepted_bundle


def test_v98_id_is_deterministic() -> None:
    payload = _load_v98("adeu_arc_behavior_evidence_bundle_v98_reference.json")
    without_id = deepcopy(payload)
    without_id.pop("behavior_evidence_bundle_id")
    assert (
        compute_adeu_arc_behavior_evidence_bundle_id(without_id)
        == payload["behavior_evidence_bundle_id"]
    )


def test_v98_exported_schema_accepts_reference_fixture() -> None:
    _behavior_schema_validator().validate(
        _load_v98("adeu_arc_behavior_evidence_bundle_v98_reference.json")
    )


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "adeu_arc_behavior_evidence_bundle_v98_reject_harness_binding_mismatch.json",
            "authoritative_surface_refs must include harness_record binding",
        ),
        (
            "adeu_arc_behavior_evidence_bundle_v98_reject_canonical_order_drift.json",
            "puzzle_id order must follow canonical_puzzle_order",
        ),
        (
            "adeu_arc_behavior_evidence_bundle_v98_reject_cross_pattern_unsupported_by_per_puzzle_entries.json",
            "support_behavior_entry_refs must match support_puzzle_ids",
        ),
        (
            "adeu_arc_behavior_evidence_bundle_v98_reject_missing_failure_mode_evidence_anchors.json",
            "at least 1 item",
        ),
        (
            "adeu_arc_behavior_evidence_bundle_v98_reject_unsupported_readiness_claim_laundering.json",
            "forbidden term 'leaderboard_ready'",
        ),
        (
            "adeu_arc_behavior_evidence_bundle_v98_reject_authority_boundary_contradiction.json",
            "boundary_violation_flags must be empty",
        ),
        (
            "adeu_arc_behavior_evidence_bundle_v98_reject_missing_per_puzzle_upstream_refs.json",
            "must not be empty",
        ),
    ],
)
def test_v98_rejects_invalid_behavior_bundle_fixtures(
    fixture_name: str, match: str
) -> None:
    payload = _load_v98(fixture_name)
    with pytest.raises(ValidationError, match=match):
        AdeuArcBehaviorEvidenceBundle.model_validate(payload)
