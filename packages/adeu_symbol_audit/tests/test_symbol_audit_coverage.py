from __future__ import annotations

import json
from pathlib import Path

from adeu_symbol_audit import (
    SymbolCensus,
    build_manifest_to_census_coverage_report,
    build_reference_architecture_ir_scope_manifest,
    build_symbol_census,
)


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v50a" / name


def _read_json(name: str) -> dict[str, object]:
    return json.loads(_fixture_path(name).read_text(encoding="utf-8"))


def test_reference_coverage_report_matches_fixture() -> None:
    manifest = build_reference_architecture_ir_scope_manifest(repo_root=_repo_root())
    census = build_symbol_census(repo_root=_repo_root(), scope_manifest=manifest)

    report = build_manifest_to_census_coverage_report(scope_manifest=manifest, census=census)

    assert report.model_dump(mode="json", by_alias=True, exclude_none=True) == _read_json(
        "reference_symbol_audit_coverage_report.json"
    )


def test_missing_manifest_source_file_fails_closed_with_typed_carrier() -> None:
    manifest = build_reference_architecture_ir_scope_manifest(repo_root=_repo_root())
    reference_census = SymbolCensus.model_validate(_read_json("reference_symbol_census.json"))
    census = reference_census.model_copy(
        update={"source_files": reference_census.source_files[:-1]}, deep=True
    )

    report = build_manifest_to_census_coverage_report(scope_manifest=manifest, census=census)

    assert report.model_dump(mode="json", by_alias=True, exclude_none=True) == _read_json(
        "reference_symbol_audit_coverage_report_fail_closed_missing_source_file.json"
    )


def test_disallowed_symbol_kind_fails_closed() -> None:
    manifest = build_reference_architecture_ir_scope_manifest(repo_root=_repo_root())
    reference_census = SymbolCensus.model_validate(_read_json("reference_symbol_census.json"))
    mutated_entry = reference_census.symbols[0].model_copy(
        update={
            "symbol_id": reference_census.symbols[0].symbol_id.replace(":function", ":attribute"),
            "symbol_kind": "attribute",
        },
        deep=True,
    )
    census = reference_census.model_copy(
        update={
            "symbols": [mutated_entry],
            "symbol_count": 1,
            "source_files": reference_census.source_files[:1],
        },
        deep=True,
    )

    report = build_manifest_to_census_coverage_report(scope_manifest=manifest, census=census)

    assert report.coverage_status == "fail_closed_mismatch"
    assert report.disallowed_symbol_kinds == ["attribute"]


def test_duplicate_symbol_id_fails_closed() -> None:
    manifest = build_reference_architecture_ir_scope_manifest(repo_root=_repo_root())
    reference_census = SymbolCensus.model_validate(_read_json("reference_symbol_census.json"))
    duplicate_entry = reference_census.symbols[0].model_copy(deep=True)
    census = reference_census.model_copy(
        update={
            "symbols": [reference_census.symbols[0], duplicate_entry],
            "symbol_count": 2,
            "source_files": reference_census.source_files[:1],
        },
        deep=True,
    )

    report = build_manifest_to_census_coverage_report(scope_manifest=manifest, census=census)

    assert report.coverage_status == "fail_closed_mismatch"
    assert report.duplicate_symbol_ids == [duplicate_entry.symbol_id]


def test_scope_manifest_ref_mismatch_fails_closed() -> None:
    manifest = build_reference_architecture_ir_scope_manifest(repo_root=_repo_root())
    reference_census = SymbolCensus.model_validate(_read_json("reference_symbol_census.json"))
    mismatched_census = reference_census.model_copy(
        update={"scope_manifest_ref": "scope_manifest:0000000000000000"},
        deep=True,
    )

    report = build_manifest_to_census_coverage_report(
        scope_manifest=manifest, census=mismatched_census
    )

    assert report.coverage_status == "fail_closed_mismatch"
    assert report.census_scope_manifest_ref == "scope_manifest:0000000000000000"
