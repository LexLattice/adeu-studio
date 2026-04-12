from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_constitutional_coherence import (
    ConstitutionalCoherenceLaneDriftRecord,
    load_lane_drift_record,
    run_constitutional_coherence_v55b,
)
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v55b"
ADMISSIONS_FIXTURE = FIXTURE_ROOT / "constitutional_support_admission_records_v55b.json"
LANE_DRIFT_FIXTURE = FIXTURE_ROOT / "reference_constitutional_coherence_lane_drift_record.json"


def _load_json(name: str) -> object:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def test_reference_outputs_match_live_checker() -> None:
    report, unresolved = run_constitutional_coherence_v55b(
        repo_root_path=_repo_root_path(),
        admissions_path=ADMISSIONS_FIXTURE,
        lane_drift_path=LANE_DRIFT_FIXTURE,
    )

    assert report.model_dump(mode="json") == _load_json(
        "reference_constitutional_coherence_report.json"
    )
    assert unresolved.model_dump(mode="json") == _load_json(
        "reference_constitutional_unresolved_seam_register.json"
    )


def test_warning_only_posture_and_unresolved_split_are_explicit() -> None:
    report, unresolved = run_constitutional_coherence_v55b(
        repo_root_path=_repo_root_path(),
        admissions_path=ADMISSIONS_FIXTURE,
        lane_drift_path=LANE_DRIFT_FIXTURE,
    )

    assert report.target_arc == "vNext+150"
    assert report.target_path == "V55-B"
    assert report.checker_version == "v55b_constitutional_coherence_checker@1"
    assert report.warning_count == len(report.warnings)
    assert report.warning_count == 3
    assert {warning.code for warning in report.warnings} == {
        "DESCENDANT_STRUCTURED_AUTHORITY_LAYER_MISSING",
        "NO_STRUCTURED_DOC_CLAIMS_VISIBLE",
    }

    descendant_warning = next(
        warning
        for warning in report.warnings
        if warning.code == "DESCENDANT_STRUCTURED_AUTHORITY_LAYER_MISSING"
    )
    assert descendant_warning.artifact_ref == "docs/support/crypto data spec2.md"
    assert "support-surface only" in descendant_warning.message

    assert unresolved.entry_count == 8
    assert {entry.reason_kind for entry in unresolved.entries} == {
        "family_law_gap",
        "descendant_law_gap",
        "admission_surface_gap",
    }

    descendant_gap = next(
        entry
        for entry in unresolved.entries
        if entry.artifact_ref == "docs/support/crypto data spec2.md"
        and entry.predicate_id == "authority_layer_declared"
    )
    assert descendant_gap.reason_kind == "descendant_law_gap"


def test_reference_lane_drift_fixture_validates() -> None:
    payload = _load_json("reference_constitutional_coherence_lane_drift_record.json")

    record = ConstitutionalCoherenceLaneDriftRecord.model_validate(payload)
    loaded = load_lane_drift_record(path=LANE_DRIFT_FIXTURE)

    assert loaded == record
    assert record.entry_count == len(record.entries)
    assert record.target_arc == "vNext+150"
    assert record.target_path == "V55-B"
    assert record.prior_lane_ref == "docs/LOCKED_CONTINUATION_vNEXT_PLUS149.md"


def test_missing_required_lane_drift_assumption_fails_closed(tmp_path: Path) -> None:
    payload = _load_json("reference_constitutional_coherence_lane_drift_record.json")
    assert isinstance(payload, dict)
    entries = payload["entries"]
    assert isinstance(entries, list)
    filtered_entries = [
        entry for entry in entries if entry["assumption_ref"] != "warning_only_checker"
    ]
    payload["entries"] = filtered_entries
    payload["entry_count"] = len(filtered_entries)
    bad_path = tmp_path / "bad_lane_drift.json"
    bad_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="required handoff posture"):
        run_constitutional_coherence_v55b(
            repo_root_path=_repo_root_path(),
            admissions_path=ADMISSIONS_FIXTURE,
            lane_drift_path=bad_path,
        )


def test_duplicate_lane_drift_assumption_fails_closed(tmp_path: Path) -> None:
    payload = _load_json("reference_constitutional_coherence_lane_drift_record.json")
    assert isinstance(payload, dict)
    entries = payload["entries"]
    assert isinstance(entries, list)
    payload["entries"] = [*entries, dict(entries[0])]
    payload["entry_count"] = len(payload["entries"])
    bad_path = tmp_path / "duplicate_lane_drift.json"
    bad_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="must not repeat assumption refs"):
        run_constitutional_coherence_v55b(
            repo_root_path=_repo_root_path(),
            admissions_path=ADMISSIONS_FIXTURE,
            lane_drift_path=bad_path,
        )


def test_descendant_must_remain_support_surface_only(tmp_path: Path) -> None:
    payload = _load_json("constitutional_support_admission_records_v55b.json")
    assert isinstance(payload, list)
    descendant_entry = next(
        entry for entry in payload if entry["artifact_ref"] == "docs/support/crypto data spec2.md"
    )
    descendant_entry["authority_layer"] = "lock"
    bad_path = tmp_path / "bad_admissions.json"
    bad_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="support-surface admission"):
        run_constitutional_coherence_v55b(
            repo_root_path=_repo_root_path(),
            admissions_path=bad_path,
            lane_drift_path=LANE_DRIFT_FIXTURE,
        )
