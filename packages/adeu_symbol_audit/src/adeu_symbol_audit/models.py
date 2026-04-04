from __future__ import annotations

import hashlib
import json
import re
from pathlib import PurePosixPath
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

ADEU_SYMBOL_AUDIT_SCOPE_MANIFEST_SCHEMA = "adeu_symbol_audit_scope_manifest@1"
ADEU_SYMBOL_CENSUS_ENTRY_SCHEMA = "adeu_symbol_census_entry@1"
ADEU_SYMBOL_CENSUS_SCHEMA = "adeu_symbol_census@1"
ADEU_SYMBOL_AUDIT_COVERAGE_REPORT_SCHEMA = "adeu_symbol_audit_coverage_report@1"

MODEL_CONFIG = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

LanguageKind = Literal["python"]
SymbolKind = Literal["class", "function", "method", "local_function"]
ParseStatus = Literal["parsed"]
ExtractorConfidencePosture = Literal["authoritative_for_explicit_parseable_defs"]
CoverageStatus = Literal["closed_clean", "fail_closed_mismatch"]

_SYMBOL_KIND_ORDER: dict[SymbolKind, int] = {
    "class": 0,
    "function": 1,
    "method": 2,
    "local_function": 3,
}
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
DEFAULT_SYMBOL_KINDS: tuple[SymbolKind, ...] = ("class", "function", "method", "local_function")


def _assert_non_empty_text(value: str, *, field_name: str) -> str:
    normalized = value.strip()
    if not normalized:
        raise ValueError(f"{field_name} must be non-empty")
    return normalized


def _assert_repo_rel_path(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    if normalized.startswith("/"):
        raise ValueError(f"{field_name} must be repo-relative")
    if "\\" in normalized:
        raise ValueError(f"{field_name} must use forward slashes")
    path = PurePosixPath(normalized)
    if path.is_absolute():
        raise ValueError(f"{field_name} must be repo-relative")
    if any(part in {"", ".", ".."} for part in path.parts):
        raise ValueError(f"{field_name} must not contain empty, '.' or '..' segments")
    if path.name == "":
        raise ValueError(f"{field_name} must point to a file path")
    return path.as_posix()


def _assert_sha256_hex(value: str, *, field_name: str) -> str:
    normalized = _assert_non_empty_text(value, field_name=field_name)
    if not _SHA256_RE.fullmatch(normalized):
        raise ValueError(f"{field_name} must be a lowercase 64-character sha256 hex digest")
    return normalized


def _dump_canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def _sha256_canonical_payload(value: Any) -> str:
    return hashlib.sha256(_dump_canonical_json(value).encode("utf-8")).hexdigest()


def _assert_sorted_unique_strings(
    values: list[str], *, field_name: str, path_normalized: bool = False
) -> list[str]:
    normalized = [
        _assert_repo_rel_path(value, field_name=field_name)
        if path_normalized
        else _assert_non_empty_text(value, field_name=field_name)
        for value in values
    ]
    if normalized != sorted(normalized):
        raise ValueError(f"{field_name} must be sorted")
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must be unique")
    return normalized


def _assert_symbol_kinds(values: list[SymbolKind], *, field_name: str) -> list[SymbolKind]:
    if list(values) != list(DEFAULT_SYMBOL_KINDS):
        raise ValueError(f"{field_name} must equal the frozen V50-A symbol-kind vocabulary")
    return list(values)


def compute_symbol_audit_symbol_id(
    *, module_path: str, qualname: str, symbol_kind: SymbolKind
) -> str:
    normalized_module_path = _assert_repo_rel_path(module_path, field_name="module_path")
    normalized_qualname = _assert_non_empty_text(qualname, field_name="qualname")
    return f"symbol:{normalized_module_path}:{normalized_qualname}:{symbol_kind}"


def compute_scope_manifest_id(payload_without_id: dict[str, Any]) -> str:
    digest = _sha256_canonical_payload(payload_without_id)
    return f"scope_manifest:{digest[:16]}"


class ScopeManifestSourceFile(BaseModel):
    model_config = MODEL_CONFIG

    file_path: str
    sha256: str

    @model_validator(mode="after")
    def _validate(self) -> "ScopeManifestSourceFile":
        object.__setattr__(
            self, "file_path", _assert_repo_rel_path(self.file_path, field_name="file_path")
        )
        object.__setattr__(self, "sha256", _assert_sha256_hex(self.sha256, field_name="sha256"))
        return self


class SymbolAuditScopeManifest(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_SYMBOL_AUDIT_SCOPE_MANIFEST_SCHEMA] = Field(
        default=ADEU_SYMBOL_AUDIT_SCOPE_MANIFEST_SCHEMA,
        alias="schema",
    )
    scope_manifest_id: str
    language: LanguageKind = "python"
    source_files: list[ScopeManifestSourceFile] = Field(min_length=1)
    symbol_kinds_included: list[SymbolKind] = Field(
        default_factory=lambda: list(DEFAULT_SYMBOL_KINDS)
    )
    scope_hash: str

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "SymbolAuditScopeManifest":
        object.__setattr__(
            self,
            "scope_manifest_id",
            _assert_non_empty_text(self.scope_manifest_id, field_name="scope_manifest_id"),
        )
        sorted_source_files = sorted(self.source_files, key=lambda item: item.file_path)
        if list(self.source_files) != sorted_source_files:
            raise ValueError("source_files must be sorted by file_path")
        file_paths = [item.file_path for item in self.source_files]
        if len(file_paths) != len(set(file_paths)):
            raise ValueError("source_files must be unique by file_path")
        object.__setattr__(
            self,
            "symbol_kinds_included",
            _assert_symbol_kinds(self.symbol_kinds_included, field_name="symbol_kinds_included"),
        )
        expected_scope_hash = _sha256_canonical_payload(
            {
                "schema": self.schema,
                "language": self.language,
                "source_files": [item.model_dump(mode="json") for item in self.source_files],
                "symbol_kinds_included": self.symbol_kinds_included,
            }
        )
        if self.scope_hash != expected_scope_hash:
            raise ValueError("scope_hash must match canonical manifest payload")
        expected_scope_manifest_id = compute_scope_manifest_id(
            {
                "schema": self.schema,
                "language": self.language,
                "source_files": [item.model_dump(mode="json") for item in self.source_files],
                "symbol_kinds_included": self.symbol_kinds_included,
                "scope_hash": self.scope_hash,
            }
        )
        if self.scope_manifest_id != expected_scope_manifest_id:
            raise ValueError("scope_manifest_id must match canonical manifest identity")
        return self


class SymbolCensusEntry(BaseModel):
    model_config = MODEL_CONFIG

    symbol_id: str
    module_path: str
    qualname: str
    symbol_name: str
    symbol_kind: SymbolKind
    start_line: int
    end_line: int
    parent_symbol_id: str | None = None
    signature_text: str
    decorators_or_modifiers: list[str] = Field(default_factory=list)
    class_bases: list[str] = Field(default_factory=list)
    docstring_excerpt: str | None = None
    census_index: int
    extractor_confidence_posture: ExtractorConfidencePosture
    parse_status: ParseStatus = "parsed"

    @model_validator(mode="after")
    def _validate(self) -> "SymbolCensusEntry":
        object.__setattr__(
            self, "module_path", _assert_repo_rel_path(self.module_path, field_name="module_path")
        )
        object.__setattr__(
            self, "qualname", _assert_non_empty_text(self.qualname, field_name="qualname")
        )
        object.__setattr__(
            self, "symbol_name", _assert_non_empty_text(self.symbol_name, field_name="symbol_name")
        )
        object.__setattr__(
            self,
            "signature_text",
            _assert_non_empty_text(self.signature_text, field_name="signature_text"),
        )
        if self.parent_symbol_id is not None:
            object.__setattr__(
                self,
                "parent_symbol_id",
                _assert_non_empty_text(self.parent_symbol_id, field_name="parent_symbol_id"),
            )
        object.__setattr__(
            self,
            "decorators_or_modifiers",
            _assert_sorted_unique_strings(
                self.decorators_or_modifiers, field_name="decorators_or_modifiers"
            ),
        )
        object.__setattr__(
            self,
            "class_bases",
            _assert_sorted_unique_strings(self.class_bases, field_name="class_bases"),
        )
        if self.docstring_excerpt is not None:
            object.__setattr__(
                self,
                "docstring_excerpt",
                _assert_non_empty_text(self.docstring_excerpt, field_name="docstring_excerpt"),
            )
        if self.start_line <= 0 or self.end_line < self.start_line:
            raise ValueError("start_line/end_line must describe a valid source interval")
        if self.census_index <= 0:
            raise ValueError("census_index must be positive")
        expected_symbol_id = compute_symbol_audit_symbol_id(
            module_path=self.module_path,
            qualname=self.qualname,
            symbol_kind=self.symbol_kind,
        )
        if self.symbol_id != expected_symbol_id:
            raise ValueError("symbol_id must match canonical module_path + qualname + symbol_kind")
        return self


class SymbolCensus(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_SYMBOL_CENSUS_SCHEMA] = Field(
        default=ADEU_SYMBOL_CENSUS_SCHEMA,
        alias="schema",
    )
    scope_manifest_ref: str
    language: LanguageKind = "python"
    source_files: list[ScopeManifestSourceFile] = Field(min_length=1)
    symbol_kinds_included: list[SymbolKind] = Field(
        default_factory=lambda: list(DEFAULT_SYMBOL_KINDS)
    )
    symbol_count: int
    census_hash: str
    symbols: list[SymbolCensusEntry] = Field(min_length=1)

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "SymbolCensus":
        object.__setattr__(
            self,
            "scope_manifest_ref",
            _assert_non_empty_text(self.scope_manifest_ref, field_name="scope_manifest_ref"),
        )
        sorted_source_files = sorted(self.source_files, key=lambda item: item.file_path)
        if list(self.source_files) != sorted_source_files:
            raise ValueError("source_files must be sorted by file_path")
        file_paths = [item.file_path for item in self.source_files]
        if len(file_paths) != len(set(file_paths)):
            raise ValueError("source_files must be unique by file_path")
        object.__setattr__(
            self,
            "symbol_kinds_included",
            _assert_symbol_kinds(self.symbol_kinds_included, field_name="symbol_kinds_included"),
        )
        if self.symbol_count != len(self.symbols):
            raise ValueError("symbol_count must match the number of symbols")
        symbol_ids = [entry.symbol_id for entry in self.symbols]
        if len(symbol_ids) != len(set(symbol_ids)):
            raise ValueError("symbols must be unique by symbol_id")
        expected_indices = list(range(1, len(self.symbols) + 1))
        observed_indices = [entry.census_index for entry in self.symbols]
        if observed_indices != expected_indices:
            raise ValueError("symbols must carry contiguous census_index values starting at 1")
        admitted_paths = set(file_paths)
        admitted_kinds = set(self.symbol_kinds_included)
        for entry in self.symbols:
            if entry.module_path not in admitted_paths:
                raise ValueError("symbol module_path must belong to source_files")
            if entry.symbol_kind not in admitted_kinds:
                raise ValueError("symbol_kind must belong to symbol_kinds_included")
        expected_census_hash = _sha256_canonical_payload(
            {
                "schema": self.schema,
                "scope_manifest_ref": self.scope_manifest_ref,
                "language": self.language,
                "source_files": [item.model_dump(mode="json") for item in self.source_files],
                "symbol_kinds_included": self.symbol_kinds_included,
                "symbol_count": self.symbol_count,
                "symbols": [
                    item.model_dump(mode="json", exclude_none=True) for item in self.symbols
                ],
            }
        )
        if self.census_hash != expected_census_hash:
            raise ValueError("census_hash must match canonical census payload")
        return self


class SymbolAuditCoverageReport(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_SYMBOL_AUDIT_COVERAGE_REPORT_SCHEMA] = Field(
        default=ADEU_SYMBOL_AUDIT_COVERAGE_REPORT_SCHEMA,
        alias="schema",
    )
    scope_manifest_ref: str
    census_scope_manifest_ref: str
    census_hash: str
    expected_source_files: list[str] = Field(default_factory=list)
    observed_source_files: list[str] = Field(default_factory=list)
    missing_source_files: list[str] = Field(default_factory=list)
    unexpected_source_files: list[str] = Field(default_factory=list)
    disallowed_symbol_kinds: list[str] = Field(default_factory=list)
    duplicate_symbol_ids: list[str] = Field(default_factory=list)
    coverage_status: CoverageStatus
    coverage_gate_reason: str

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "SymbolAuditCoverageReport":
        object.__setattr__(
            self,
            "scope_manifest_ref",
            _assert_non_empty_text(self.scope_manifest_ref, field_name="scope_manifest_ref"),
        )
        object.__setattr__(
            self,
            "census_scope_manifest_ref",
            _assert_non_empty_text(
                self.census_scope_manifest_ref, field_name="census_scope_manifest_ref"
            ),
        )
        object.__setattr__(
            self, "census_hash", _assert_sha256_hex(self.census_hash, field_name="census_hash")
        )
        for field_name in (
            "expected_source_files",
            "observed_source_files",
            "missing_source_files",
            "unexpected_source_files",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique_strings(
                    getattr(self, field_name), field_name=field_name, path_normalized=True
                ),
            )
        object.__setattr__(
            self,
            "disallowed_symbol_kinds",
            _assert_sorted_unique_strings(
                self.disallowed_symbol_kinds, field_name="disallowed_symbol_kinds"
            ),
        )
        object.__setattr__(
            self,
            "duplicate_symbol_ids",
            _assert_sorted_unique_strings(
                self.duplicate_symbol_ids, field_name="duplicate_symbol_ids"
            ),
        )
        object.__setattr__(
            self,
            "coverage_gate_reason",
            _assert_non_empty_text(self.coverage_gate_reason, field_name="coverage_gate_reason"),
        )
        has_mismatch = any(
            (
                self.scope_manifest_ref != self.census_scope_manifest_ref,
                self.missing_source_files,
                self.unexpected_source_files,
                self.disallowed_symbol_kinds,
                self.duplicate_symbol_ids,
            )
        )
        expected_status: CoverageStatus = "fail_closed_mismatch" if has_mismatch else "closed_clean"
        if self.coverage_status != expected_status:
            raise ValueError("coverage_status must match the typed coverage mismatch posture")
        return self


__all__ = [
    "ADEU_SYMBOL_AUDIT_COVERAGE_REPORT_SCHEMA",
    "ADEU_SYMBOL_AUDIT_SCOPE_MANIFEST_SCHEMA",
    "ADEU_SYMBOL_CENSUS_ENTRY_SCHEMA",
    "ADEU_SYMBOL_CENSUS_SCHEMA",
    "DEFAULT_SYMBOL_KINDS",
    "ExtractorConfidencePosture",
    "LanguageKind",
    "ParseStatus",
    "ScopeManifestSourceFile",
    "SymbolAuditCoverageReport",
    "SymbolAuditScopeManifest",
    "SymbolCensus",
    "SymbolCensusEntry",
    "SymbolKind",
    "compute_scope_manifest_id",
    "compute_symbol_audit_symbol_id",
]
