from __future__ import annotations

from collections import Counter

from .models import SymbolAuditCoverageReport, SymbolCensus, SymbolSemanticAudit

def build_coverage_report(*, census: SymbolCensus, audit: SymbolSemanticAudit) -> SymbolAuditCoverageReport:
    census_ids = [entry.symbol_id for entry in census.symbols]
    audit_ids = [entry.symbol_id for entry in audit.audit_entries]

    duplicate_audit_symbol_ids = sorted(
        symbol_id for symbol_id, count in Counter(audit_ids).items() if count > 1
    )
    missing_symbol_ids = sorted(set(census_ids) - set(audit_ids))
    unexpected_symbol_ids = sorted(set(audit_ids) - set(census_ids))
    unresolved_count = sum(entry.audit_status == "unresolved" for entry in audit.audit_entries)
    low_confidence_count = sum(entry.confidence_band == "low" for entry in audit.audit_entries)
    schema_valid_count = len(audit.audit_entries)

    if (
        missing_symbol_ids
        or unexpected_symbol_ids
        or duplicate_audit_symbol_ids
        or schema_valid_count != len(census_ids)
        or audit.audit_entry_count != len(census_ids)
    ):
        completion_status = "incomplete"
        completion_gate_reason = (
            "fail_closed: expected one schema-valid audit entry per census symbol and no extras or duplicates"
        )
    elif unresolved_count:
        completion_status = "closed_with_unresolved"
        completion_gate_reason = "100% coverage reached, but unresolved audit entries remain"
    elif low_confidence_count:
        completion_status = "closed_with_low_confidence"
        completion_gate_reason = "100% coverage reached; low-confidence hypotheses still require review"
    else:
        completion_status = "closed_clean"
        completion_gate_reason = "100% coverage reached with no unresolved or low-confidence entries"

    return SymbolAuditCoverageReport(
        schema="adeu_symbol_audit_coverage_report@1",
        scope_id=census.scope_id,
        census_hash=census.census_hash,
        audit_hash=audit.audit_hash,
        expected_symbol_count=len(census_ids),
        audited_symbol_count=len(audit_ids),
        missing_symbol_ids=missing_symbol_ids,
        unexpected_symbol_ids=unexpected_symbol_ids,
        duplicate_audit_symbol_ids=duplicate_audit_symbol_ids,
        schema_valid_count=schema_valid_count,
        unresolved_count=unresolved_count,
        low_confidence_count=low_confidence_count,
        completion_status=completion_status,
        completion_gate_reason=completion_gate_reason,
    )
