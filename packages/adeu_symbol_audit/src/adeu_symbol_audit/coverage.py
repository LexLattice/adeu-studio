from __future__ import annotations

from collections import Counter

from .models import SymbolAuditCoverageReport, SymbolAuditScopeManifest, SymbolCensus


def build_manifest_to_census_coverage_report(
    *,
    scope_manifest: SymbolAuditScopeManifest,
    census: SymbolCensus,
) -> SymbolAuditCoverageReport:
    expected_source_files = [item.file_path for item in scope_manifest.source_files]
    observed_source_files = [item.file_path for item in census.source_files]
    missing_source_files = sorted(set(expected_source_files) - set(observed_source_files))
    unexpected_source_files = sorted(set(observed_source_files) - set(expected_source_files))

    admitted_symbol_kinds = set(scope_manifest.symbol_kinds_included)
    disallowed_symbol_kinds = sorted(
        {
            entry.symbol_kind
            for entry in census.symbols
            if entry.symbol_kind not in admitted_symbol_kinds
        }
    )
    duplicate_symbol_ids = sorted(
        symbol_id
        for symbol_id, count in Counter(entry.symbol_id for entry in census.symbols).items()
        if count > 1
    )

    if (
        missing_source_files
        or unexpected_source_files
        or disallowed_symbol_kinds
        or duplicate_symbol_ids
    ):
        coverage_status = "fail_closed_mismatch"
        coverage_gate_reason = (
            "fail_closed: manifest and census must reconcile over exact source files, "
            "admitted kinds, and unique symbol identities"
        )
    else:
        coverage_status = "closed_clean"
        coverage_gate_reason = (
            "manifest source set and census closure reconciled cleanly over the admitted pilot "
            "scope"
        )

    return SymbolAuditCoverageReport.model_validate(
        {
            "schema": "adeu_symbol_audit_coverage_report@1",
            "scope_manifest_ref": scope_manifest.scope_manifest_id,
            "census_hash": census.census_hash,
            "expected_source_files": expected_source_files,
            "observed_source_files": observed_source_files,
            "missing_source_files": missing_source_files,
            "unexpected_source_files": unexpected_source_files,
            "disallowed_symbol_kinds": disallowed_symbol_kinds,
            "duplicate_symbol_ids": duplicate_symbol_ids,
            "coverage_status": coverage_status,
            "coverage_gate_reason": coverage_gate_reason,
        }
    )


__all__ = ["build_manifest_to_census_coverage_report"]
