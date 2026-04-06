from __future__ import annotations

import json
from functools import lru_cache
from pathlib import Path

import pytest
from adeu_edge_ledger import (
    build_starter_edge_class_catalog,
    build_starter_edge_probe_template_catalog,
)
from adeu_ir.repo import repo_root
from adeu_symbol_audit import (
    SymbolAuditCoverageReport,
    SymbolAuditScopeManifest,
    SymbolCensus,
    SymbolSemanticAudit,
)


def _fixture_path(*parts: str) -> Path:
    root = repo_root(anchor=Path(__file__))
    return root.joinpath(*parts)


def _load_json(*parts: str) -> dict[str, object]:
    return json.loads(_fixture_path(*parts).read_text(encoding="utf-8"))


@lru_cache(maxsize=1)
def _released_stack() -> tuple[
    Path,
    SymbolAuditScopeManifest,
    SymbolCensus,
    SymbolAuditCoverageReport,
    SymbolSemanticAudit,
]:
    root = repo_root(anchor=Path(__file__))
    manifest = SymbolAuditScopeManifest.model_validate(
        _load_json(
            "packages",
            "adeu_symbol_audit",
            "tests",
            "fixtures",
            "v50a",
            "reference_symbol_audit_scope_manifest.json",
        )
    )
    census = SymbolCensus.model_validate(
        _load_json(
            "packages",
            "adeu_symbol_audit",
            "tests",
            "fixtures",
            "v50a",
            "reference_symbol_census.json",
        )
    )
    coverage = SymbolAuditCoverageReport.model_validate(
        _load_json(
            "packages",
            "adeu_symbol_audit",
            "tests",
            "fixtures",
            "v50a",
            "reference_symbol_audit_coverage_report.json",
        )
    )
    audit = SymbolSemanticAudit.model_validate(
        _load_json(
            "packages",
            "adeu_symbol_audit",
            "tests",
            "fixtures",
            "v50b",
            "reference_symbol_semantic_audit.json",
        )
    )
    return root, manifest, census, coverage, audit


@lru_cache(maxsize=1)
def _starter_catalogs():
    catalog = build_starter_edge_class_catalog()
    probes = build_starter_edge_probe_template_catalog(edge_class_catalog=catalog)
    return catalog, probes


@pytest.fixture(scope="session")
def released_stack() -> tuple[
    Path,
    SymbolAuditScopeManifest,
    SymbolCensus,
    SymbolAuditCoverageReport,
    SymbolSemanticAudit,
]:
    return _released_stack()


@pytest.fixture(scope="session")
def starter_catalogs():
    return _starter_catalogs()
