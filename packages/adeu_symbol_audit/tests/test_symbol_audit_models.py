from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_repo_description.models import compute_symbol_id
from adeu_symbol_audit import (
    ADEU_SYMBOL_AUDIT_COVERAGE_REPORT_SCHEMA,
    ADEU_SYMBOL_AUDIT_SCOPE_MANIFEST_SCHEMA,
    ADEU_SYMBOL_CENSUS_SCHEMA,
    SymbolAuditCoverageReport,
    SymbolAuditScopeManifest,
    SymbolCensus,
    compute_symbol_audit_symbol_id,
)
from pydantic import ValidationError


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v50a" / name


def _read_json(name: str) -> dict[str, object]:
    return json.loads(_fixture_path(name).read_text(encoding="utf-8"))


def test_reference_scope_manifest_replays_deterministically() -> None:
    payload = _read_json("reference_symbol_audit_scope_manifest.json")

    model = SymbolAuditScopeManifest.model_validate(payload)

    assert model.schema == ADEU_SYMBOL_AUDIT_SCOPE_MANIFEST_SCHEMA
    assert model.model_dump(mode="json", by_alias=True, exclude_none=True) == payload


def test_reference_symbol_census_replays_deterministically() -> None:
    payload = _read_json("reference_symbol_census.json")

    model = SymbolCensus.model_validate(payload)

    assert model.schema == ADEU_SYMBOL_CENSUS_SCHEMA
    assert model.model_dump(mode="json", by_alias=True, exclude_none=True) == payload


@pytest.mark.parametrize(
    "fixture_name",
    [
        "reference_symbol_audit_coverage_report.json",
        "reference_symbol_audit_coverage_report_fail_closed_missing_source_file.json",
    ],
)
def test_reference_coverage_reports_replay_deterministically(fixture_name: str) -> None:
    payload = _read_json(fixture_name)

    model = SymbolAuditCoverageReport.model_validate(payload)

    assert model.schema == ADEU_SYMBOL_AUDIT_COVERAGE_REPORT_SCHEMA
    assert model.model_dump(mode="json", by_alias=True, exclude_none=True) == payload


def test_scope_manifest_requires_explicit_file_hashes() -> None:
    payload = _read_json("reference_symbol_audit_scope_manifest.json")
    payload["source_files"][0].pop("sha256")

    with pytest.raises(ValidationError):
        SymbolAuditScopeManifest.model_validate(payload)


def test_coverage_report_rejects_clean_status_with_missing_source_file() -> None:
    payload = _read_json("reference_symbol_audit_coverage_report.json")
    payload["missing_source_files"] = [payload["expected_source_files"][0]]

    with pytest.raises(ValidationError):
        SymbolAuditCoverageReport.model_validate(payload)


def test_shared_symbol_kinds_reuse_released_textual_symbol_id_law() -> None:
    module_path = "packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py"
    qualname = "_validation_context"
    for symbol_kind in ("class", "function", "method"):
        assert compute_symbol_audit_symbol_id(
            module_path=module_path,
            qualname=qualname,
            symbol_kind=symbol_kind,
        ) == compute_symbol_id(
            module_path=module_path,
            qualname=qualname,
            symbol_kind=symbol_kind,
        )


def test_census_entry_requires_explicit_extractor_confidence_posture() -> None:
    payload = _read_json("reference_symbol_census.json")
    payload["symbols"][0].pop("extractor_confidence_posture")

    with pytest.raises(ValidationError):
        SymbolCensus.model_validate(payload)


def test_scope_manifest_rejects_unsorted_source_files() -> None:
    payload = _read_json("reference_symbol_audit_scope_manifest.json")
    payload["source_files"] = list(reversed(payload["source_files"]))

    with pytest.raises(ValidationError):
        SymbolAuditScopeManifest.model_validate(payload)


def test_coverage_report_fail_closed_fixture_is_typed_missing_file_case() -> None:
    payload = _read_json(
        "reference_symbol_audit_coverage_report_fail_closed_missing_source_file.json"
    )

    model = SymbolAuditCoverageReport.model_validate(payload)

    assert model.coverage_status == "fail_closed_mismatch"
    assert model.missing_source_files
    assert model.unexpected_source_files == []
