from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import run_agentic_de_live_harness_v58a
from adeu_ir.repo import repo_root
from urm_runtime import CopilotTurnSnapshot

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v58a"
V57A_FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v57a"


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v58a_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        "packages/adeu_agentic_de/tests/fixtures/v57a/reference_agentic_de_local_effect_observation_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v57a/reference_agentic_de_local_effect_conformance_report.json",
        "packages/adeu_agentic_de/tests/fixtures/v57b/reference_agentic_de_lane_drift_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v57b/reference_agentic_de_local_effect_restoration_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v57c/reference_agentic_de_lane_drift_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v57c/reference_agentic_de_local_effect_hardening_register.json",
        "packages/adeu_agentic_de/tests/fixtures/v58a/reference_agentic_de_lane_drift_record.json",
        "packages/adeu_agentic_de/tests/fixtures/v58a/reference_copilot_turn_snapshot.json",
        "artifacts/agent_harness/v152/evidence_inputs/v56a_agentic_de_interaction_governance_starter_evidence_v152.json",
        "artifacts/agent_harness/v153/evidence_inputs/v56b_bounded_live_gate_starter_evidence_v153.json",
        "artifacts/agent_harness/v154/evidence_inputs/v56c_harvest_calibration_migration_evidence_v154.json",
        "artifacts/agent_harness/v155/evidence_inputs/v57a_local_effect_observation_evidence_v155.json",
        "artifacts/agent_harness/v156/evidence_inputs/v57b_local_effect_restoration_evidence_v156.json",
        "artifacts/agent_harness/v157/evidence_inputs/v57c_local_effect_hardening_evidence_v157.json",
        "artifacts/agentic_de/v57/local_effect/.gitignore",
    ]
    for relative_path in relative_paths:
        source = repo_root_path / relative_path
        target = tmp_path / relative_path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    return (
        tmp_path,
        tmp_path
        / "packages"
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v58a",
    )


def _load_snapshot(root: Path) -> CopilotTurnSnapshot:
    return CopilotTurnSnapshot.model_validate(
        _load_json(root, "reference_copilot_turn_snapshot.json")
    )


def test_reference_outputs_match_live_v58a_runner(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v58a_input_tree(tmp_path)

    admission, handoff, observation, conformance, reintegration = run_agentic_de_live_harness_v58a(
        repo_root_path=temp_root,
        live_turn_snapshot=_load_snapshot(fixture_root),
    )

    assert admission.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT, "reference_agentic_de_live_turn_admission_record.json"
    )
    assert handoff.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT, "reference_agentic_de_live_turn_handoff_record.json"
    )
    assert observation.model_dump(mode="json") == _load_json(
        V57A_FIXTURE_ROOT,
        "reference_agentic_de_local_effect_observation_record.json",
    )
    assert conformance.model_dump(mode="json") == _load_json(
        V57A_FIXTURE_ROOT,
        "reference_agentic_de_local_effect_conformance_report.json",
    )
    assert reintegration.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT, "reference_agentic_de_live_turn_reintegration_report.json"
    )


def test_v58a_outputs_remain_evidence_only_and_ticket_bound(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v58a_input_tree(tmp_path)

    admission, handoff, observation, conformance, reintegration = run_agentic_de_live_harness_v58a(
        repo_root_path=temp_root,
        live_turn_snapshot=_load_snapshot(fixture_root),
    )

    assert admission.target_arc == "vNext+158"
    assert admission.target_path == "V58-A"
    assert admission.evidence_only is True
    assert admission.changes_live_behavior_by_default is False
    assert admission.admission_verdict == "admitted"
    assert "writes_allowed_present_but_not_ticket_equivalent" in admission.admission_reason_codes
    assert "approval_posture_observed_but_not_ticket_equivalent" in admission.admission_reason_codes

    assert handoff.target_arc == "vNext+158"
    assert handoff.target_path == "V58-A"
    assert handoff.evidence_only is True
    assert handoff.changes_live_behavior_by_default is False
    assert handoff.field_origin_tags["turn_admission_ref"] == "current_turn_native"
    assert handoff.field_origin_tags["action_ticket_ref"] == "prior_artifact"

    assert observation.ticket_ref == handoff.action_ticket_ref
    assert conformance.ticket_ref == handoff.action_ticket_ref

    assert reintegration.target_arc == "vNext+158"
    assert reintegration.target_path == "V58-A"
    assert reintegration.evidence_only is True
    assert reintegration.changes_live_behavior_by_default is False
    assert reintegration.reintegration_status == "reintegrated"
    assert reintegration.reintegration_certificate_ref_or_equivalent is not None
    assert (
        "observability refs remain non-independent support"
        in reintegration.root_origin_dedup_summary
    )


def test_non_admitted_live_turn_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v58a_input_tree(tmp_path)
    payload = _load_json(fixture_root, "reference_copilot_turn_snapshot.json")
    assert isinstance(payload, dict)
    payload["writes_allowed"] = False

    with pytest.raises(ValueError, match="must resolve to admitted"):
        run_agentic_de_live_harness_v58a(
            repo_root_path=temp_root,
            live_turn_snapshot=CopilotTurnSnapshot.model_validate(payload),
        )


def test_missing_required_v58a_lane_drift_assumption_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v58a_input_tree(tmp_path)
    lane_drift_path = fixture_root / "reference_agentic_de_lane_drift_record.json"
    payload = _load_json(fixture_root, "reference_agentic_de_lane_drift_record.json")
    assert isinstance(payload, dict)
    entries = payload["entries"]
    assert isinstance(entries, list)
    payload["entries"] = entries[:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    lane_drift_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="required handoff posture"):
        run_agentic_de_live_harness_v58a(
            repo_root_path=temp_root,
            live_turn_snapshot=_load_snapshot(fixture_root),
        )


def test_snapshot_cwd_must_match_repo_root(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v58a_input_tree(tmp_path)
    payload = _load_json(fixture_root, "reference_copilot_turn_snapshot.json")
    assert isinstance(payload, dict)
    payload["cwd"] = "/tmp/not-the-repo"

    with pytest.raises(ValueError, match="must resolve to admitted"):
        run_agentic_de_live_harness_v58a(
            repo_root_path=temp_root,
            live_turn_snapshot=CopilotTurnSnapshot.model_validate(payload),
        )
