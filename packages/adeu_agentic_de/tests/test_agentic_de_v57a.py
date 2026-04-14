from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import (
    AgenticDeLocalEffectObservationRecord,
    run_agentic_de_local_effect_v57a,
)
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v57a"


def _load_json(name: str) -> object:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v57a_input_tree(tmp_path: Path) -> Path:
    repo_root_path = _repo_root_path()
    relative_paths = [
        "packages/adeu_agentic_de/tests/fixtures/v56a/reference_agentic_de_domain_packet.json",
        "packages/adeu_agentic_de/tests/fixtures/v56a/reference_agentic_de_morph_ir.json",
        "packages/adeu_agentic_de/tests/fixtures/v56a/reference_agentic_de_interaction_contract.json",
        "packages/adeu_agentic_de/tests/fixtures/v56a/reference_agentic_de_action_proposal.json",
        "packages/adeu_agentic_de/tests/fixtures/v56a/reference_agentic_de_membrane_checkpoint.json",
        "packages/adeu_agentic_de/tests/fixtures/v56a/reference_agentic_de_morph_diagnostics.json",
        "packages/adeu_agentic_de/tests/fixtures/v56a/reference_agentic_de_conformance_report.json",
        "packages/adeu_agentic_de/tests/fixtures/v56b/reference_agentic_de_lane_drift_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v56b/reference_agentic_de_action_class_taxonomy.json",
        "packages/adeu_agentic_de/tests/fixtures/v56b/reference_agentic_de_runtime_state.json",
        "packages/adeu_agentic_de/tests/fixtures/v56b/reference_agentic_de_action_ticket.json",
        "packages/adeu_agentic_de/tests/fixtures/v56b/reference_agentic_de_morph_diagnostics.json",
        "packages/adeu_agentic_de/tests/fixtures/v56b/reference_agentic_de_conformance_report.json",
        "packages/adeu_agentic_de/tests/fixtures/v56c/reference_agentic_de_lane_drift_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v56c/reference_agentic_de_runtime_harvest_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v56c/reference_agentic_de_governance_calibration_register.json",
        "packages/adeu_agentic_de/tests/fixtures/v56c/reference_agentic_de_migration_decision_register.json",
        "packages/adeu_agentic_de/tests/fixtures/v57a/reference_agentic_de_lane_drift_record.json",
        "artifacts/agent_harness/v152/evidence_inputs/v56a_agentic_de_interaction_governance_starter_evidence_v152.json",
        "artifacts/agent_harness/v153/evidence_inputs/v56b_bounded_live_gate_starter_evidence_v153.json",
        "artifacts/agent_harness/v154/evidence_inputs/v56c_harvest_calibration_migration_evidence_v154.json",
        "artifacts/agentic_de/v57/local_effect/.gitignore",
    ]
    for relative_path in relative_paths:
        source = repo_root_path / relative_path
        target = tmp_path / relative_path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    return tmp_path


def test_reference_outputs_match_live_v57a_runner(tmp_path: Path) -> None:
    temp_root = _copy_v57a_input_tree(tmp_path)

    observation, conformance = run_agentic_de_local_effect_v57a(repo_root_path=temp_root)

    assert observation.model_dump(mode="json") == _load_json(
        "reference_agentic_de_local_effect_observation_record.json"
    )
    assert conformance.model_dump(mode="json") == _load_json(
        "reference_agentic_de_local_effect_conformance_report.json"
    )


def test_v57a_outputs_remain_evidence_only_and_ticket_visible(tmp_path: Path) -> None:
    temp_root = _copy_v57a_input_tree(tmp_path)

    observation, conformance = run_agentic_de_local_effect_v57a(repo_root_path=temp_root)

    assert observation.target_arc == "vNext+155"
    assert observation.target_path == "V57-A"
    assert observation.evidence_only is True
    assert observation.changes_live_behavior_by_default is False
    assert observation.selected_live_action_class == "local_write"
    assert observation.selected_local_write_kind == "create_new"
    assert observation.boundedness_verdict == "bounded"
    assert observation.observation_outcome == "bounded_effect_observed"

    assert conformance.evidence_only is True
    assert conformance.changes_live_behavior_by_default is False
    assert conformance.conformance_status == "effect_aligned"
    assert conformance.ticket_visibility_summary.startswith("ticket_ref=")


def test_parent_traversal_outside_designated_sandbox_fails_closed(tmp_path: Path) -> None:
    temp_root = _copy_v57a_input_tree(tmp_path)

    with pytest.raises(ValueError, match="dot, or parent traversal parts"):
        run_agentic_de_local_effect_v57a(
            repo_root_path=temp_root,
            target_relative_path="../escape.txt",
        )


def test_symlink_escape_inside_designated_sandbox_fails_closed(tmp_path: Path) -> None:
    temp_root = _copy_v57a_input_tree(tmp_path)
    sandbox_root = temp_root / "artifacts" / "agentic_de" / "v57" / "local_effect"
    outside_root = temp_root / "outside"
    outside_root.mkdir(parents=True)
    (sandbox_root / "via_symlink").symlink_to(outside_root, target_is_directory=True)

    with pytest.raises(ValueError, match="forbids symlink components"):
        run_agentic_de_local_effect_v57a(
            repo_root_path=temp_root,
            target_relative_path="via_symlink/escape.txt",
        )


def test_append_only_empty_payload_emits_no_effect_observed(tmp_path: Path) -> None:
    temp_root = _copy_v57a_input_tree(tmp_path)
    target = (
        temp_root
        / "artifacts"
        / "agentic_de"
        / "v57"
        / "local_effect"
        / "seed"
        / "append_target.log"
    )
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text("seed\n", encoding="utf-8")

    observation, conformance = run_agentic_de_local_effect_v57a(
        repo_root_path=temp_root,
        write_kind="append_only",
        target_relative_path="seed/append_target.log",
        payload_text="",
        expected_content_contains=None,
    )

    assert observation.observation_outcome == "no_effect_observed"
    assert observation.observed_write_set == []
    assert conformance.conformance_status == "effect_divergent"
    assert conformance.live_effect_present is False


def test_destructive_or_overwrite_write_kinds_remain_out_of_scope(tmp_path: Path) -> None:
    temp_root = _copy_v57a_input_tree(tmp_path)

    with pytest.raises(ValueError, match="unsupported local-write kind"):
        run_agentic_de_local_effect_v57a(
            repo_root_path=temp_root,
            write_kind="overwrite",
        )


def test_v56b_local_write_semantics_must_remain_frozen(tmp_path: Path) -> None:
    temp_root = _copy_v57a_input_tree(tmp_path)
    taxonomy_path = (
        temp_root
        / "packages"
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v56b"
        / "reference_agentic_de_action_class_taxonomy.json"
    )
    payload = json.loads(taxonomy_path.read_text(encoding="utf-8"))
    payload["entries"][0]["write_surface_category"] = "lock_doc"
    payload["taxonomy_id"] = None
    taxonomy_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="bounded_local_artifact"):
        run_agentic_de_local_effect_v57a(
            repo_root_path=temp_root,
            v56b_action_class_taxonomy_path=taxonomy_path,
        )


def test_missing_required_v57a_lane_drift_assumption_fails_closed(tmp_path: Path) -> None:
    temp_root = _copy_v57a_input_tree(tmp_path)
    lane_drift_path = (
        temp_root
        / "packages"
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v57a"
        / "reference_agentic_de_lane_drift_record.json"
    )
    payload = json.loads(lane_drift_path.read_text(encoding="utf-8"))
    payload["entries"] = payload["entries"][:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    lane_drift_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="required handoff posture"):
        run_agentic_de_local_effect_v57a(repo_root_path=temp_root)


def test_negative_observation_outcomes_remain_explicit_vocab(tmp_path: Path) -> None:
    payload = _load_json("reference_agentic_de_local_effect_observation_record.json")
    assert isinstance(payload, dict)
    base_entry = payload["observed_write_set"][0]
    assert isinstance(base_entry, dict)

    cases = [
        ("mismatched_effect_observed", "bounded", [base_entry]),
        ("out_of_scope_write_observed", "failed", [base_entry]),
        ("boundedness_verdict_failed", "failed", [base_entry]),
    ]
    for outcome, verdict, observed_write_set in cases:
        candidate = {
            **payload,
            "observation_id": None,
            "observation_outcome": outcome,
            "boundedness_verdict": verdict,
            "observed_write_set": observed_write_set,
        }
        record = AgenticDeLocalEffectObservationRecord.model_validate(candidate)
        assert record.observation_outcome == outcome
