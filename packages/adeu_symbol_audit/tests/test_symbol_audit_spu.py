from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_symbol_audit import (
    SymbolAuditCoverageReport,
    SymbolCensus,
    SymbolSemanticAudit,
    build_manifest_to_census_coverage_report,
    build_reference_architecture_ir_scope_manifest,
    build_symbol_census,
    build_symbol_semantic_audit,
)
from pydantic import ValidationError


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def _fixture_path(version: str, name: str) -> Path:
    return Path(__file__).parent / "fixtures" / version / name


def _read_json(version: str, name: str) -> dict[str, object]:
    return json.loads(_fixture_path(version, name).read_text(encoding="utf-8"))


def test_reference_symbol_semantic_audit_replays_deterministically() -> None:
    payload = _read_json("v50b", "reference_symbol_semantic_audit.json")

    model = SymbolSemanticAudit.model_validate(payload)

    assert model.model_dump(mode="json", by_alias=True, exclude_none=True) == payload


def test_reference_symbol_semantic_audit_matches_fixture() -> None:
    manifest = build_reference_architecture_ir_scope_manifest(repo_root=_repo_root())
    census = build_symbol_census(repo_root=_repo_root(), scope_manifest=manifest)
    coverage = build_manifest_to_census_coverage_report(scope_manifest=manifest, census=census)

    audit = build_symbol_semantic_audit(
        repo_root=_repo_root(),
        census=census,
        coverage_report=coverage,
    )

    assert audit.model_dump(mode="json", by_alias=True, exclude_none=True) == _read_json(
        "v50b",
        "reference_symbol_semantic_audit.json",
    )


def test_reference_symbol_semantic_audit_has_exactly_one_entry_per_census_symbol() -> None:
    census = SymbolCensus.model_validate(_read_json("v50a", "reference_symbol_census.json"))
    audit = SymbolSemanticAudit.model_validate(
        _read_json("v50b", "reference_symbol_semantic_audit.json")
    )

    assert len(audit.audit_entries) == census.symbol_count
    assert [entry.symbol_id for entry in audit.audit_entries] == [
        entry.symbol_id for entry in census.symbols
    ]


def test_reference_symbol_semantic_audit_includes_low_confidence_and_unresolved_rows() -> None:
    audit = SymbolSemanticAudit.model_validate(
        _read_json("v50b", "reference_symbol_semantic_audit.json")
    )

    statuses = {entry.audit_status for entry in audit.audit_entries}

    assert "audited_low_confidence" in statuses
    assert "unresolved" in statuses


def test_semantic_audit_rejects_missing_source_span_evidence() -> None:
    payload = _read_json("v50b", "reference_symbol_semantic_audit.json")
    payload["audit_entries"][0]["evidence_refs"] = [
        ref
        for ref in payload["audit_entries"][0]["evidence_refs"]
        if ref["evidence_kind"] != "source_span"
    ]

    with pytest.raises(ValidationError):
        SymbolSemanticAudit.model_validate(payload)


def test_semantic_audit_rejects_missing_evidence_refs() -> None:
    payload = _read_json("v50b", "reference_symbol_semantic_audit.json")
    payload["audit_entries"][0]["evidence_refs"] = []

    with pytest.raises(ValidationError):
        SymbolSemanticAudit.model_validate(payload)


def test_semantic_audit_rejects_duplicate_symbol_ids() -> None:
    payload = _read_json("v50b", "reference_symbol_semantic_audit.json")
    payload["audit_entries"][1]["symbol_id"] = payload["audit_entries"][0]["symbol_id"]

    with pytest.raises(ValidationError):
        SymbolSemanticAudit.model_validate(payload)


def test_build_symbol_semantic_audit_rejects_non_closed_clean_coverage() -> None:
    census = SymbolCensus.model_validate(_read_json("v50a", "reference_symbol_census.json"))
    coverage = SymbolAuditCoverageReport.model_validate(
        _read_json(
            "v50a",
            "reference_symbol_audit_coverage_report_fail_closed_missing_source_file.json",
        )
    )

    with pytest.raises(ValueError, match="coverage_report.coverage_status = closed_clean"):
        build_symbol_semantic_audit(
            repo_root=_repo_root(),
            census=census,
            coverage_report=coverage,
        )


def test_build_symbol_semantic_audit_rejects_census_hash_mismatch() -> None:
    census = SymbolCensus.model_validate(_read_json("v50a", "reference_symbol_census.json"))
    coverage_payload = _read_json("v50a", "reference_symbol_audit_coverage_report.json")
    coverage_payload["census_hash"] = "0" * 64
    coverage = SymbolAuditCoverageReport.model_validate(coverage_payload)

    with pytest.raises(ValueError, match="matching census_hash"):
        build_symbol_semantic_audit(
            repo_root=_repo_root(),
            census=census,
            coverage_report=coverage,
        )


def test_build_symbol_semantic_audit_rejects_source_file_hash_drift(tmp_path: Path) -> None:
    repo_root = _repo_root()
    census = SymbolCensus.model_validate(_read_json("v50a", "reference_symbol_census.json"))
    coverage = SymbolAuditCoverageReport.model_validate(
        _read_json("v50a", "reference_symbol_audit_coverage_report.json")
    )

    for source_file in census.source_files:
        destination = tmp_path / source_file.file_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(repo_root / source_file.file_path, destination)

    drifted_path = tmp_path / census.source_files[0].file_path
    drifted_path.write_text(
        drifted_path.read_text(encoding="utf-8") + "\n# drifted after census\n",
        encoding="utf-8",
    )

    with pytest.raises(ValueError, match="source file hash match"):
        build_symbol_semantic_audit(
            repo_root=tmp_path,
            census=census,
            coverage_report=coverage,
        )
