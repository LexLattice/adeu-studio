from __future__ import annotations

import warnings
from functools import lru_cache
from pathlib import Path

import pytest
from adeu_edge_ledger import (
    build_starter_edge_class_catalog,
    build_starter_edge_probe_template_catalog,
)
from adeu_symbol_audit import (
    SymbolAuditCoverageReport,
    SymbolAuditScopeManifest,
    SymbolCensus,
    SymbolSemanticAudit,
    build_manifest_to_census_coverage_report,
    build_reference_architecture_ir_scope_manifest,
    build_symbol_census,
    build_symbol_semantic_audit,
)

warnings.filterwarnings(
    "ignore",
    message=r'Field name "schema" .* shadows an attribute in parent "BaseModel"',
    category=UserWarning,
)

ANALYSIS_REQUEST_CLASS_SYMBOL_ID = (
    "symbol:packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py:"
    "AdeuArchitectureAnalysisRequest:class"
)
CAPTURE_SOURCE_SET_SYMBOL_ID = (
    "symbol:packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py:"
    "capture_adeu_architecture_analysis_source_set_payload:function"
)
RUN_GIT_SYMBOL_ID = (
    "symbol:packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py:"
    "_run_git:function"
)
MATERIALIZE_SETTLEMENT_SYMBOL_ID = (
    "symbol:packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_settlement.py:"
    "materialize_adeu_architecture_analysis_settlement_frame_payload:function"
)


@lru_cache(maxsize=1)
def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


@lru_cache(maxsize=1)
def _released_stack() -> tuple[
    Path,
    SymbolAuditScopeManifest,
    SymbolCensus,
    SymbolAuditCoverageReport,
    SymbolSemanticAudit,
]:
    repo_root = _repo_root()
    manifest = build_reference_architecture_ir_scope_manifest(repo_root=repo_root)
    census = build_symbol_census(repo_root=repo_root, scope_manifest=manifest)
    coverage = build_manifest_to_census_coverage_report(scope_manifest=manifest, census=census)
    audit = build_symbol_semantic_audit(
        repo_root=repo_root,
        census=census,
        coverage_report=coverage,
    )
    return repo_root, manifest, census, coverage, audit


@lru_cache(maxsize=1)
def _starter_catalogs():
    catalog = build_starter_edge_class_catalog()
    probes = build_starter_edge_probe_template_catalog(edge_class_catalog=catalog)
    return catalog, probes


@pytest.fixture(scope="session")
def repo_root() -> Path:
    return _repo_root()


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
