from __future__ import annotations

from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

SYMBOL_CENSUS_SCHEMA = "adeu_symbol_census@1"
SYMBOL_SEMANTIC_AUDIT_SCHEMA = "adeu_symbol_semantic_audit@1"
SYMBOL_AUDIT_COVERAGE_REPORT_SCHEMA = "adeu_symbol_audit_coverage_report@1"

SymbolKind = Literal["class", "function", "method", "local_function"]
AuditStatus = Literal["audited_hypothesis", "audited_low_confidence", "unresolved"]
ConfidenceBand = Literal["low", "medium", "high"]
CompletionStatus = Literal[
    "incomplete",
    "closed_with_unresolved",
    "closed_with_low_confidence",
    "closed_clean",
]

class SourceFileSnapshot(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)
    file_path: str
    sha256: str

class SymbolCensusEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)
    symbol_id: str
    fq_name: str
    symbol_name: str
    symbol_kind: SymbolKind
    language: Literal["python"]
    file_path: str
    start_line: int
    end_line: int
    parent_symbol_id: str | None = None
    signature_text: str
    decorators_or_modifiers: list[str] = Field(default_factory=list)
    class_bases: list[str] = Field(default_factory=list)
    docstring_excerpt: str | None = None
    census_index: int
    parser_version: str
    parser_confidence: str
    parse_status: Literal["parsed"]

    @model_validator(mode="after")
    def _validate_lines(self) -> "SymbolCensusEntry":
        if self.start_line <= 0 or self.end_line < self.start_line:
            raise ValueError("invalid source line interval")
        return self

class SymbolCensus(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)
    schema: Literal[SYMBOL_CENSUS_SCHEMA]
    scope_id: str
    language: Literal["python"]
    source_files: list[SourceFileSnapshot]
    symbol_kinds_included: list[SymbolKind]
    symbol_count: int
    census_hash: str
    symbols: list[SymbolCensusEntry]

    @model_validator(mode="after")
    def _validate_count(self) -> "SymbolCensus":
        if self.symbol_count != len(self.symbols):
            raise ValueError("symbol_count must match symbols length")
        return self

class AuditEvidenceRef(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)
    evidence_kind: Literal["source_span", "decorator", "baseclass", "call_summary", "docstring"]
    detail: str

class SymbolSemanticAuditEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)
    symbol_id: str
    audit_status: AuditStatus
    role_summary: str
    architectural_purpose: str
    local_behavior_summary: str
    inputs_outputs_summary: str
    side_effect_profile: list[str] = Field(default_factory=list)
    dependency_position: str
    likely_canonical_family: str | None = None
    overlap_candidate_symbol_ids: list[str] = Field(default_factory=list)
    abstraction_candidate_notes: str | None = None
    evidence_refs: list[AuditEvidenceRef] = Field(default_factory=list)
    uncertainty_notes: list[str] = Field(default_factory=list)
    confidence_band: ConfidenceBand

class SymbolSemanticAudit(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)
    schema: Literal[SYMBOL_SEMANTIC_AUDIT_SCHEMA]
    scope_id: str
    census_hash: str
    spu_name: str
    spu_version: str
    audit_entry_count: int
    audit_hash: str
    audit_entries: list[SymbolSemanticAuditEntry]

    @model_validator(mode="after")
    def _validate_count(self) -> "SymbolSemanticAudit":
        if self.audit_entry_count != len(self.audit_entries):
            raise ValueError("audit_entry_count must match audit_entries length")
        return self

class SymbolAuditCoverageReport(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)
    schema: Literal[SYMBOL_AUDIT_COVERAGE_REPORT_SCHEMA]
    scope_id: str
    census_hash: str
    audit_hash: str
    expected_symbol_count: int
    audited_symbol_count: int
    missing_symbol_ids: list[str] = Field(default_factory=list)
    unexpected_symbol_ids: list[str] = Field(default_factory=list)
    duplicate_audit_symbol_ids: list[str] = Field(default_factory=list)
    schema_valid_count: int
    unresolved_count: int
    low_confidence_count: int
    completion_status: CompletionStatus
    completion_gate_reason: str
