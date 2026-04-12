from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_constitutional_coherence import (
    ConstitutionalCoherenceLaneDriftRecord,
    compute_constitutional_support_admission_record_id,
    load_support_admission_records,
    run_constitutional_coherence_v55a,
)
from adeu_constitutional_coherence.checker import (
    EXPECTED_ADMITTED_SEED_ARTIFACTS,
    MAX_STRUCTURED_DOC_BYTES,
    _extract_structured_doc_surface,
)
from adeu_ir.repo import repo_root

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v55a"
ADMISSIONS_FIXTURE = FIXTURE_ROOT / "constitutional_support_admission_records_v55a.json"


def _load_json(name: str) -> object:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _load_admissions_payload() -> list[dict[str, object]]:
    payload = _load_json("constitutional_support_admission_records_v55a.json")
    assert isinstance(payload, list)
    return payload


def _write_records(path: Path, payload: list[dict[str, object]]) -> Path:
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return path


def _bootstrap_seed_docs(root: Path, *, overrides: dict[str, str] | None = None) -> None:
    contents = {
        artifact_ref: "Status: temporary seed\nAuthority layer: support\n"
        for artifact_ref in EXPECTED_ADMITTED_SEED_ARTIFACTS
    }
    contents.update(overrides or {})
    for artifact_ref, body in contents.items():
        path = root / artifact_ref
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body, encoding="utf-8")


def test_committed_admissions_fixture_matches_artifact_ids() -> None:
    records = load_support_admission_records(path=ADMISSIONS_FIXTURE)

    assert len(records) == len(EXPECTED_ADMITTED_SEED_ARTIFACTS)
    assert [record.artifact_ref for record in records] == list(EXPECTED_ADMITTED_SEED_ARTIFACTS)
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


def test_checker_rejects_admission_payloads_outside_exact_seed_set(tmp_path: Path) -> None:
    payload = _load_admissions_payload()

    missing_path = _write_records(tmp_path / "missing.json", payload[:-1])
    with pytest.raises(ValueError, match="exact admitted seed set"):
        run_constitutional_coherence_v55a(
            repo_root_path=_repo_root_path(),
            admissions_path=missing_path,
        )

    extra_record = dict(payload[0])
    extra_record["artifact_ref"] = "docs/EXTRA_SUPPORT_SURFACE.md"
    extra_record["admission_id"] = compute_constitutional_support_admission_record_id(
        artifact_ref=extra_record["artifact_ref"]
    )
    extra_path = _write_records(tmp_path / "extra.json", [*payload, extra_record])
    with pytest.raises(ValueError, match="exact admitted seed set"):
        run_constitutional_coherence_v55a(
            repo_root_path=_repo_root_path(),
            admissions_path=extra_path,
        )


def test_checker_canonicalizes_admission_order_before_report_generation(tmp_path: Path) -> None:
    payload = list(reversed(_load_admissions_payload()))
    admissions_path = _write_records(tmp_path / "reordered.json", payload)

    report, unresolved = run_constitutional_coherence_v55a(
        repo_root_path=_repo_root_path(),
        admissions_path=admissions_path,
    )

    assert report.model_dump(mode="json") == _load_json(
        "reference_constitutional_coherence_report.json"
    )
    assert unresolved.model_dump(mode="json") == _load_json(
        "reference_constitutional_unresolved_seam_register.json"
    )


def test_malformed_designated_support_block_fails_closed(tmp_path: Path) -> None:
    _bootstrap_seed_docs(
        tmp_path,
        overrides={
            "docs/support/ADEU_SCHEMA_META_GRAMMAR.md": (
                "Status: temporary seed\n"
                "Authority layer: support\n\n"
                "```json\n"
                '{\n  "schema": "constitutional_support_admission_record@1",\n'
                '  "artifact_ref": "docs/placeholder.md",\n'
                "```"
            )
        },
    )

    with pytest.raises(ValueError, match="invalid designated structured block"):
        run_constitutional_coherence_v55a(
            repo_root_path=tmp_path,
            admissions_path=ADMISSIONS_FIXTURE,
        )


def test_malformed_non_designated_block_is_ignored(tmp_path: Path) -> None:
    _bootstrap_seed_docs(
        tmp_path,
        overrides={
            "docs/support/ADEU_SCHEMA_META_GRAMMAR.md": (
                "Status: temporary seed\n"
                "Authority layer: support\n\n"
                "```json\n"
                '{\n  "schema": "unrelated_support_shape@1",\n'
                '  "note": "broken"\n'
                "```"
            )
        },
    )

    report, unresolved = run_constitutional_coherence_v55a(
        repo_root_path=tmp_path,
        admissions_path=ADMISSIONS_FIXTURE,
    )

    assert report.checked_artifact_refs == list(EXPECTED_ADMITTED_SEED_ARTIFACTS)
    assert report.warning_count == 0
    assert unresolved.entry_count == 7


def test_structured_doc_surface_rejects_symlink_parent_traversal(tmp_path: Path) -> None:
    outside = tmp_path / "outside"
    outside.mkdir()
    (outside / "escape.md").write_text(
        "Status: escaped\nAuthority layer: support\n",
        encoding="utf-8",
    )
    (tmp_path / "docs").symlink_to(outside, target_is_directory=True)

    with pytest.raises(ValueError, match="symlink component forbidden"):
        _extract_structured_doc_surface(
            repo_root_path=tmp_path,
            artifact_ref="docs/escape.md",
        )


def test_structured_doc_surface_rejects_oversized_seed_artifact(tmp_path: Path) -> None:
    large_doc = tmp_path / "docs" / "large.md"
    large_doc.parent.mkdir(parents=True, exist_ok=True)
    large_doc.write_text("x" * (MAX_STRUCTURED_DOC_BYTES + 1), encoding="utf-8")

    with pytest.raises(ValueError, match="exceeds"):
        _extract_structured_doc_surface(
            repo_root_path=tmp_path,
            artifact_ref="docs/large.md",
        )
