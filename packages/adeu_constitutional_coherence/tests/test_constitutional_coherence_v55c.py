from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_constitutional_coherence import (
    ConstitutionalCoherenceLaneDriftRecord,
    load_lane_drift_record,
    run_constitutional_coherence_v55c,
)
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v55c"
ADMISSIONS_FIXTURE = FIXTURE_ROOT / "constitutional_support_admission_records_v55c.json"
LANE_DRIFT_FIXTURE = FIXTURE_ROOT / "reference_constitutional_coherence_lane_drift_record.json"
GOVERNANCE_FIXTURE = FIXTURE_ROOT / "reference_constitutional_governance_calibration_register.json"
MIGRATION_FIXTURE = FIXTURE_ROOT / "reference_constitutional_migration_decision_register.json"


def _load_json(name: str) -> object:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def test_reference_outputs_match_live_checker() -> None:
    governance, migration = run_constitutional_coherence_v55c(
        repo_root_path=_repo_root_path(),
        admissions_path=ADMISSIONS_FIXTURE,
        lane_drift_path=LANE_DRIFT_FIXTURE,
    )

    assert governance.model_dump(mode="json") == json.loads(
        GOVERNANCE_FIXTURE.read_text(encoding="utf-8")
    )
    assert migration.model_dump(mode="json") == json.loads(
        MIGRATION_FIXTURE.read_text(encoding="utf-8")
    )


def test_advisory_registers_are_bounded_and_non_live() -> None:
    governance, migration = run_constitutional_coherence_v55c(
        repo_root_path=_repo_root_path(),
        admissions_path=ADMISSIONS_FIXTURE,
        lane_drift_path=LANE_DRIFT_FIXTURE,
    )

    assert governance.target_arc == "vNext+151"
    assert governance.target_path == "V55-C"
    assert governance.advisory_only is True
    assert governance.changes_live_checker_behavior is False
    assert governance.entry_count == 3
    assert {entry.recommended_outcome for entry in governance.entries} == {
        "candidate_for_later_local_hardening",
        "not_selected_for_escalation",
    }
    assert any(
        entry.surface_ref == "docs/support/crypto data spec2.md"
        and entry.predicate_id == "authority_layer_declared"
        for entry in governance.entries
    )

    assert migration.target_arc == "vNext+151"
    assert migration.target_path == "V55-C"
    assert migration.advisory_only is True
    assert migration.changes_live_checker_behavior is False
    assert migration.entry_count == 6
    assert {entry.recommended_outcome for entry in migration.entries} == {
        "keep_warning_only",
        "needs_more_evidence",
        "not_selected_for_escalation",
    }
    assert any(
        entry.surface_id == "report_semantics"
        and entry.recommended_outcome == "needs_more_evidence"
        for entry in migration.entries
    )


def test_reference_lane_drift_fixture_validates() -> None:
    payload = _load_json("reference_constitutional_coherence_lane_drift_record.json")

    record = ConstitutionalCoherenceLaneDriftRecord.model_validate(payload)
    loaded = load_lane_drift_record(path=LANE_DRIFT_FIXTURE)

    assert loaded == record
    assert record.entry_count == len(record.entries)
    assert record.target_arc == "vNext+151"
    assert record.target_path == "V55-C"
    assert record.prior_lane_ref == "docs/LOCKED_CONTINUATION_vNEXT_PLUS150.md"


def test_missing_required_v55c_lane_drift_assumption_fails_closed(tmp_path: Path) -> None:
    payload = _load_json("reference_constitutional_coherence_lane_drift_record.json")
    assert isinstance(payload, dict)
    entries = payload["entries"]
    assert isinstance(entries, list)
    filtered_entries = [
        entry
        for entry in entries
        if entry["assumption_ref"] != "governance_migration_decision_surfaces"
    ]
    payload["entries"] = filtered_entries
    payload["entry_count"] = len(filtered_entries)
    bad_path = tmp_path / "bad_lane_drift.json"
    bad_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="required handoff posture"):
        run_constitutional_coherence_v55c(
            repo_root_path=_repo_root_path(),
            admissions_path=ADMISSIONS_FIXTURE,
            lane_drift_path=bad_path,
        )


def test_missing_required_v55b_evidence_fails_closed(tmp_path: Path) -> None:
    bad_evidence_path = tmp_path / "bad_v55b_evidence.json"
    bad_evidence_path.write_text(
        json.dumps(
            {
                "schema": "v55b_descendant_trial_hardening_evidence@1",
                "warning_only_checker_preserved": True,
                "support_surface_descendant_trial_only": False,
                "reference_warning_count": 3,
                "reference_unresolved_entry_count": 8,
                "reference_lane_drift_entry_count": 5,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )

    with pytest.raises(ValueError, match="support-surface-only descendant posture"):
        run_constitutional_coherence_v55c(
            repo_root_path=_repo_root_path(),
            admissions_path=ADMISSIONS_FIXTURE,
            lane_drift_path=LANE_DRIFT_FIXTURE,
            v55b_evidence_path=bad_evidence_path,
        )
