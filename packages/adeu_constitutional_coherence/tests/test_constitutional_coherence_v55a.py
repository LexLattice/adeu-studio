from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_constitutional_coherence import (
    ConstitutionalCoherenceLaneDriftRecord,
    ConstitutionalSupportAdmissionRecord,
    compute_constitutional_support_admission_record_id,
    load_support_admission_records,
    run_constitutional_coherence_v55a,
)
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v55a"
ADMISSIONS_FIXTURE = FIXTURE_ROOT / "constitutional_support_admission_records_v55a.json"


def _load_json(name: str) -> object:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _record_with_artifact(
    record: ConstitutionalSupportAdmissionRecord,
    artifact_ref: str,
) -> dict[str, object]:
    payload = record.model_dump(mode="json")
    payload["artifact_ref"] = artifact_ref
    payload["admission_id"] = compute_constitutional_support_admission_record_id(
        artifact_ref=artifact_ref
    )
    return payload


def _write_records(path: Path, payload: list[dict[str, object]]) -> Path:
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return path


def test_committed_admissions_fixture_matches_artifact_ids() -> None:
    records = load_support_admission_records(path=ADMISSIONS_FIXTURE)

    assert len(records) == 6
    assert [record.artifact_ref for record in records] == [
        "docs/LOCKED_RECURSIVE_COORDINATE_ADOPTION_v0.md",
        "docs/DRAFT_RECURSIVE_COORDINATE_MIGRATION_LINT_POSTURE_v0.md",
        "docs/support/ADEU_SCHEMA_META_GRAMMAR.md",
        "docs/support/VERTICAL_ALIGNMENT_ARCHITECTURE_HARDENED.md",
        "docs/support/ODEU_MEMBRANE_ARCHITECTURE.md",
        "docs/support/crypto data spec2.md",
    ]
    for record in records:
        assert record.admission_id == compute_constitutional_support_admission_record_id(
            artifact_ref=record.artifact_ref
        )


def test_reference_outputs_match_live_checker() -> None:
    report, unresolved = run_constitutional_coherence_v55a(
        repo_root_path=_repo_root_path(),
        admissions_path=ADMISSIONS_FIXTURE,
    )

    assert report.model_dump(mode="json") == _load_json(
        "reference_constitutional_coherence_report.json"
    )
    assert unresolved.model_dump(mode="json") == _load_json(
        "reference_constitutional_unresolved_seam_register.json"
    )


def test_warning_only_and_not_evaluable_posture_is_explicit() -> None:
    report, unresolved = run_constitutional_coherence_v55a(
        repo_root_path=_repo_root_path(),
        admissions_path=ADMISSIONS_FIXTURE,
    )

    assert report.warning_count == 2
    assert {
        warning.artifact_ref for warning in report.warnings
    } == {
        "docs/support/ADEU_SCHEMA_META_GRAMMAR.md",
        "docs/support/ODEU_MEMBRANE_ARCHITECTURE.md",
    }
    assert unresolved.entry_count == 7
    assert all(entry.reason_kind == "not_evaluable_yet" for entry in unresolved.entries)

    descendant_eval = next(
        evaluation
        for evaluation in report.evaluations
        if evaluation.artifact_ref == "docs/support/crypto data spec2.md"
        and evaluation.predicate_id == "descendant_claim_within_parent_entitlement"
    )
    assert descendant_eval.status == "pass"


def test_reference_lane_drift_fixture_validates() -> None:
    payload = _load_json("reference_constitutional_coherence_lane_drift_record.json")

    record = ConstitutionalCoherenceLaneDriftRecord.model_validate(payload)

    assert record.entry_count == len(record.entries)
    assert record.target_arc == "vNext+149"
    assert record.target_path == "V55-A"


def test_malformed_designated_support_block_fails_closed(tmp_path: Path) -> None:
    records = load_support_admission_records(path=ADMISSIONS_FIXTURE)
    designated_doc = tmp_path / "designated_seed.md"
    designated_doc.write_text(
        (
            "Status: temporary seed\n"
            "Authority layer: support\n\n"
            "```json\n"
            '{\n  "schema": "constitutional_support_admission_record@1",\n'
            '  "artifact_ref": "docs/placeholder.md",\n'
            "```"
        ),
        encoding="utf-8",
    )
    admissions_path = _write_records(
        tmp_path / "admissions.json",
        [_record_with_artifact(records[2], str(designated_doc))],
    )

    with pytest.raises(ValueError, match="invalid designated structured block"):
        run_constitutional_coherence_v55a(
            repo_root_path=_repo_root_path(),
            admissions_path=admissions_path,
        )


def test_malformed_non_designated_block_is_ignored(tmp_path: Path) -> None:
    records = load_support_admission_records(path=ADMISSIONS_FIXTURE)
    plain_doc = tmp_path / "plain_seed.md"
    plain_doc.write_text(
        (
            "Status: temporary seed\n"
            "Authority layer: support\n\n"
            "```json\n"
            '{\n  "schema": "unrelated_support_shape@1",\n'
            '  "note": "broken"\n'
            "```"
        ),
        encoding="utf-8",
    )
    admissions_path = _write_records(
        tmp_path / "admissions.json",
        [_record_with_artifact(records[2], str(plain_doc))],
    )

    report, unresolved = run_constitutional_coherence_v55a(
        repo_root_path=_repo_root_path(),
        admissions_path=admissions_path,
    )

    assert report.checked_artifact_refs == [str(plain_doc)]
    assert report.warning_count == 0
    assert unresolved.entry_count == 1
    assert unresolved.entries[0].predicate_id == "descendant_claim_within_parent_entitlement"
