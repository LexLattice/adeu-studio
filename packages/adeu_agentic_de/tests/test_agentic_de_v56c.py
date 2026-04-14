from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import run_agentic_de_interaction_v56c
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v56c"


def _load_json(name: str) -> object:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def test_reference_outputs_match_live_evaluator() -> None:
    harvest, governance, migration = run_agentic_de_interaction_v56c(
        repo_root_path=_repo_root_path()
    )

    assert harvest.model_dump(mode="json") == _load_json(
        "reference_agentic_de_runtime_harvest_record.json"
    )
    assert governance.model_dump(mode="json") == _load_json(
        "reference_agentic_de_governance_calibration_register.json"
    )
    assert migration.model_dump(mode="json") == _load_json(
        "reference_agentic_de_migration_decision_register.json"
    )


def test_v56c_outputs_remain_advisory_only_and_freeze_v56b_live_semantics() -> None:
    harvest, governance, migration = run_agentic_de_interaction_v56c(
        repo_root_path=_repo_root_path()
    )

    assert harvest.target_arc == "vNext+154"
    assert harvest.target_path == "V56-C"
    assert harvest.observation_only is True
    assert harvest.governance_classification_deferred is True
    assert harvest.selected_live_action_classes == [
        "local_reversible_execute",
        "local_write",
    ]
    assert harvest.selected_live_action_class_interpretation_frozen is True
    assert harvest.ticket_issued is True
    assert harvest.executed_or_observed_effect == "no_live_effect"
    assert harvest.live_effect_present is False

    assert governance.target_arc == "vNext+154"
    assert governance.target_path == "V56-C"
    assert governance.advisory_only is True
    assert governance.changes_live_behavior_by_default is False
    assert {entry.subject_kind for entry in governance.entries} == {"action_class", "surface"}
    assert {entry.recommended_outcome for entry in governance.entries} == {
        "keep_warning_only",
        "needs_more_evidence",
        "not_selected_for_escalation",
    }

    assert migration.target_arc == "vNext+154"
    assert migration.target_path == "V56-C"
    assert migration.advisory_only is True
    assert migration.candidate_only is True
    assert migration.changes_live_behavior_by_default is False
    assert {entry.recommended_outcome for entry in migration.entries} == {
        "keep_warning_only",
        "candidate_for_later_local_hardening",
        "not_selected_for_escalation",
    }


def test_missing_required_v56c_lane_drift_assumption_fails_closed(tmp_path: Path) -> None:
    payload = _load_json("reference_agentic_de_lane_drift_record.json")
    assert isinstance(payload, dict)
    entries = payload["entries"]
    assert isinstance(entries, list)
    filtered_entries = [
        entry
        for entry in entries
        if entry["assumption_ref"] != "runtime_harvest_observation_only"
    ]
    payload["entries"] = filtered_entries
    payload["entry_count"] = len(filtered_entries)
    payload["record_id"] = None
    bad_path = tmp_path / "bad_lane_drift.json"
    bad_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="required handoff posture"):
        run_agentic_de_interaction_v56c(
            repo_root_path=_repo_root_path(),
            lane_drift_path=bad_path,
        )


def test_reinterpreted_v56b_live_class_definitions_fail_closed(tmp_path: Path) -> None:
    repo_root_path = _repo_root_path()
    evidence_path = (
        repo_root_path
        / "artifacts"
        / "agent_harness"
        / "v153"
        / "evidence_inputs"
        / "v56b_bounded_live_gate_starter_evidence_v153.json"
    )
    payload = json.loads(evidence_path.read_text(encoding="utf-8"))
    payload["selected_live_gate_class_definitions_for_v56b"]["local_scope"] = (
        "broader_system_effects_allowed"
    )
    bad_path = tmp_path / "bad_v56b_evidence.json"
    bad_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="shipped live-class interpretation"):
        run_agentic_de_interaction_v56c(
            repo_root_path=repo_root_path,
            v56b_evidence_path=bad_path,
        )


def test_external_v56b_evidence_override_path_is_preserved_in_output_refs(tmp_path: Path) -> None:
    repo_root_path = _repo_root_path()
    source = (
        repo_root_path
        / "artifacts"
        / "agent_harness"
        / "v153"
        / "evidence_inputs"
        / "v56b_bounded_live_gate_starter_evidence_v153.json"
    )
    override = tmp_path / "external_v56b_evidence.json"
    shutil.copyfile(source, override)

    harvest, governance, migration = run_agentic_de_interaction_v56c(
        repo_root_path=repo_root_path,
        v56b_evidence_path=override,
    )

    assert str(override) in harvest.evidence_refs
    assert any(str(override) in entry.evidence_refs for entry in governance.entries)
    assert any(str(override) in entry.evidence_refs for entry in migration.entries)
