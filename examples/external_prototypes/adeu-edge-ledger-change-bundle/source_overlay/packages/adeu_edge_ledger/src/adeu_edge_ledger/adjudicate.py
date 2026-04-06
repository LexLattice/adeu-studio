from __future__ import annotations

import ast
import hashlib
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

from adeu_repo_description.models import compute_repo_test_ref
from adeu_symbol_audit import (
    SymbolAuditCoverageReport,
    SymbolCensus,
    SymbolCensusEntry,
    SymbolSemanticAudit,
)
from urm_runtime.hashing import sha256_canonical_json

from .applicability import FRAME_POSTURE, derive_symbol_edge_applicability_frame
from .models import (
    EdgeClassCatalog,
    EdgeProbeTemplateCatalog,
    SymbolEdgeAdjudicationLedger,
    SymbolEdgeAdjudicationRow,
    SymbolEdgeApplicabilityFrame,
    compute_symbol_edge_adjudication_ledger_id,
)
from .taxonomy import (
    build_starter_edge_class_catalog,
    build_starter_edge_probe_template_catalog,
    catalog_nodes_by_ref,
)

LEDGER_POSTURE = f"{FRAME_POSTURE}+bounded_repo_test_scan"
_WORD_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_TEST_FILE_GLOBS = ("test_*.py", "*_test.py")


@dataclass(frozen=True)
class _TestDescriptor:
    source_path: str
    qualname: str
    test_ref: str
    tokens: frozenset[str]


class _TestCollector(ast.NodeVisitor):
    def __init__(self, *, source_path: str, source_text: str) -> None:
        self._source_path = source_path
        self._source_text = source_text
        self._class_stack: list[str] = []
        self.descriptors: list[_TestDescriptor] = []

    def _qualname(self, function_name: str) -> str:
        if not self._class_stack:
            return function_name
        return ".".join([*self._class_stack, function_name])

    def _tokens_for_node(self, node: ast.AST) -> frozenset[str]:
        source = ast.get_source_segment(self._source_text, node)
        if source is None:
            source = ast.unparse(node)
        tokens = {token.lower() for token in _WORD_RE.findall(source)}
        tokens.update(token.lower() for token in _WORD_RE.findall(self._source_path))
        return frozenset(tokens)

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self._class_stack.append(node.name)
        self.generic_visit(node)
        self._class_stack.pop()

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        if node.name.startswith("test_"):
            qualname = self._qualname(node.name)
            self.descriptors.append(
                _TestDescriptor(
                    source_path=self._source_path,
                    qualname=qualname,
                    test_ref=compute_repo_test_ref(
                        source_path=self._source_path,
                        qualname=qualname,
                    ),
                    tokens=self._tokens_for_node(node),
                )
            )
        self.generic_visit(node)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self.visit_FunctionDef(node)


def _read_verified_source_file(*, repo_root: Path, file_path: str, sha256: str) -> str:
    file_bytes = (repo_root / file_path).read_bytes()
    if hashlib.sha256(file_bytes).hexdigest() != sha256:
        raise ValueError(f"edge adjudication requires source file hash match for {file_path}")
    return file_bytes.decode("utf-8")


def _validate_v50_stack(
    *,
    census: SymbolCensus,
    coverage_report: SymbolAuditCoverageReport,
    semantic_audit: SymbolSemanticAudit,
) -> None:
    if coverage_report.coverage_status != "closed_clean":
        raise ValueError("edge adjudication requires coverage_report.coverage_status = closed_clean")
    if coverage_report.scope_manifest_ref != census.scope_manifest_ref:
        raise ValueError("edge adjudication requires coverage_report.scope_manifest_ref to match census")
    if coverage_report.census_scope_manifest_ref != census.scope_manifest_ref:
        raise ValueError(
            "edge adjudication requires coverage_report.census_scope_manifest_ref to match census"
        )
    if coverage_report.census_hash != census.census_hash:
        raise ValueError("edge adjudication requires matching census_hash between coverage and census")
    if semantic_audit.scope_manifest_ref != census.scope_manifest_ref:
        raise ValueError("edge adjudication requires matching scope_manifest_ref between audit and census")
    if semantic_audit.census_hash != census.census_hash:
        raise ValueError("edge adjudication requires matching census_hash between audit and census")


def _package_tests_root(module_path: str) -> Path | None:
    parts = Path(module_path).parts
    if len(parts) >= 4 and parts[0] == "packages" and parts[2] == "src":
        return Path("packages") / parts[1] / "tests"
    if len(parts) >= 3 and parts[0] == "apps":
        return Path("apps") / parts[1] / "tests"
    return None


def _iter_test_files(*, repo_root: Path, module_path: str) -> list[Path]:
    tests_root = _package_tests_root(module_path)
    if tests_root is None:
        return []
    absolute_root = repo_root / tests_root
    if not absolute_root.is_dir():
        return []
    collected: set[Path] = set()
    for pattern in _TEST_FILE_GLOBS:
        collected.update(path for path in absolute_root.rglob(pattern) if path.is_file())
    return sorted(collected)


def _collect_test_descriptors(*, repo_root: Path, module_path: str) -> list[_TestDescriptor]:
    descriptors: list[_TestDescriptor] = []
    for test_path in _iter_test_files(repo_root=repo_root, module_path=module_path):
        relative_path = test_path.relative_to(repo_root).as_posix()
        source_text = test_path.read_text(encoding="utf-8")
        tree = ast.parse(source_text, filename=relative_path)
        collector = _TestCollector(source_path=relative_path, source_text=source_text)
        collector.visit(tree)
        descriptors.extend(collector.descriptors)
    descriptors.sort(key=lambda item: item.test_ref)
    return descriptors


def _symbol_identity_tokens(symbol: SymbolCensusEntry) -> set[str]:
    tokens = {symbol.symbol_name.lower(), symbol.qualname.lower()}
    tokens.update(token.lower() for token in _WORD_RE.findall(symbol.symbol_name))
    tokens.update(token.lower() for token in _WORD_RE.findall(symbol.qualname))
    tokens.update(token.lower() for token in _WORD_RE.findall(Path(symbol.module_path).stem))
    return {token for token in tokens if token}


_GENERIC_SYMBOL_TOKENS = {
    "analysis",
    "artifact",
    "architecture",
    "build",
    "class",
    "compute",
    "function",
    "helper",
    "model",
    "module",
    "normalize",
    "request",
    "scope",
    "schema",
    "source",
    "symbol",
    "test",
    "validate",
}


def _symbol_specific_identity_tokens(symbol: SymbolCensusEntry) -> set[str]:
    raw = _symbol_identity_tokens(symbol)
    exact = {symbol.symbol_name.lower(), symbol.qualname.lower()}
    informative = {
        token
        for token in raw
        if token in exact
        or (len(token) > 3 and token not in _GENERIC_SYMBOL_TOKENS)
    }
    return informative or exact


def _test_mentions_symbol(*, symbol: SymbolCensusEntry, descriptor: _TestDescriptor) -> bool:
    specific_tokens = _symbol_specific_identity_tokens(symbol)
    return bool(specific_tokens & descriptor.tokens)


def _relevant_tests_for_symbol(
    *,
    symbol: SymbolCensusEntry,
    test_descriptors: list[_TestDescriptor],
) -> list[_TestDescriptor]:
    return [descriptor for descriptor in test_descriptors if _test_mentions_symbol(symbol=symbol, descriptor=descriptor)]


def _edge_test_refs(
    *,
    symbol: SymbolCensusEntry,
    edge_test_tokens: Iterable[str],
    relevant_tests: list[_TestDescriptor],
) -> list[str]:
    normalized_tokens = {token.lower() for token in edge_test_tokens}
    matched: list[str] = []
    for descriptor in relevant_tests:
        if normalized_tokens & descriptor.tokens:
            matched.append(descriptor.test_ref)
    return sorted(set(matched))


_DEFERRING_AUDIT_STATUSES = {"audited_low_confidence", "unresolved"}


def _structure_support_refs(
    *,
    matched_cue_tags: list[str],
    structural_safety_cue_tags: list[str],
    audit_status: str,
    likely_canonical_family: str,
) -> list[str]:
    matched = sorted(set(matched_cue_tags) & set(structural_safety_cue_tags))
    refs = [f"cue:{tag}" for tag in matched]
    refs.append(f"audit_status:{audit_status}")
    refs.append(f"semantic_family:{likely_canonical_family}")
    return sorted(set(refs))


def derive_symbol_edge_adjudication_ledger(
    *,
    repo_root: Path,
    census: SymbolCensus,
    coverage_report: SymbolAuditCoverageReport,
    semantic_audit: SymbolSemanticAudit,
    symbol_id: str,
    applicability_frame: SymbolEdgeApplicabilityFrame | None = None,
    edge_class_catalog: EdgeClassCatalog | None = None,
    probe_template_catalog: EdgeProbeTemplateCatalog | None = None,
    witness_summaries: dict[str, str] | None = None,
    checked_no_witness_edge_class_refs: set[str] | None = None,
) -> SymbolEdgeAdjudicationLedger:
    _validate_v50_stack(census=census, coverage_report=coverage_report, semantic_audit=semantic_audit)
    catalog = edge_class_catalog or build_starter_edge_class_catalog()
    probes = probe_template_catalog or build_starter_edge_probe_template_catalog(
        edge_class_catalog=catalog
    )
    frame = applicability_frame or derive_symbol_edge_applicability_frame(
        repo_root=repo_root,
        census=census,
        coverage_report=coverage_report,
        semantic_audit=semantic_audit,
        symbol_id=symbol_id,
        edge_class_catalog=catalog,
        probe_template_catalog=probes,
    )
    if frame.symbol_id != symbol_id:
        raise ValueError("applicability_frame.symbol_id must match symbol_id")
    if frame.scope_manifest_ref != census.scope_manifest_ref:
        raise ValueError("applicability_frame.scope_manifest_ref must match census")
    if frame.census_hash != census.census_hash:
        raise ValueError("applicability_frame.census_hash must match census")
    if frame.audit_hash != semantic_audit.audit_hash:
        raise ValueError("applicability_frame.audit_hash must match semantic_audit")
    if frame.bound_edge_class_catalog_ref != catalog.catalog_id:
        raise ValueError("applicability_frame must bind the supplied edge_class_catalog")
    if frame.bound_probe_template_catalog_ref != probes.catalog_id:
        raise ValueError("applicability_frame must bind the supplied probe_template_catalog")

    witness_map = witness_summaries or {}
    checked_no_witness = checked_no_witness_edge_class_refs or set()
    census_by_id = {entry.symbol_id: entry for entry in census.symbols}
    audit_by_id = {entry.symbol_id: entry for entry in semantic_audit.audit_entries}
    if symbol_id not in census_by_id:
        raise ValueError(f"symbol_id not found in census: {symbol_id}")
    if symbol_id not in audit_by_id:
        raise ValueError(f"symbol_id not found in semantic_audit: {symbol_id}")
    symbol = census_by_id[symbol_id]
    audit_entry = audit_by_id[symbol_id]
    test_descriptors = _collect_test_descriptors(repo_root=repo_root, module_path=symbol.module_path)
    relevant_tests = _relevant_tests_for_symbol(symbol=symbol, test_descriptors=test_descriptors)
    nodes_by_ref = catalog_nodes_by_ref(catalog)

    adjudication_rows: list[SymbolEdgeAdjudicationRow] = []
    for row in frame.applicability_rows:
        node = nodes_by_ref[row.edge_class_ref]
        evidence_refs: list[str] = []
        supporting_test_refs: list[str] = []
        witness_summary = witness_map.get(row.edge_class_ref)
        if row.edge_class_ref in witness_map:
            status = "witness_found"
            posture = "adjudicated"
            rationale = "witness supplied explicitly for this applicable or candidate edge class"
        elif row.edge_class_ref in checked_no_witness:
            status = "checked_no_witness_found"
            posture = "adjudicated"
            rationale = "probe execution was supplied explicitly and produced no witness within the checked slice"
        elif row.applicability_status == "not_applicable":
            status = "not_applicable"
            posture = row.epistemic_posture
            rationale = row.rationale
        elif row.applicability_status == "underdetermined":
            status = "underdetermined"
            posture = row.epistemic_posture
            evidence_refs = sorted(f"cue:{tag}" for tag in row.matched_cue_tags)
            rationale = (
                "applicability cues were only partial, so adjudication remains underdetermined even if adjacent tests exist"
            )
        else:
            supporting_test_refs = _edge_test_refs(
                symbol=symbol,
                edge_test_tokens=node.test_token_tags,
                relevant_tests=relevant_tests,
            )
            if supporting_test_refs:
                status = "covered_by_existing_tests"
                posture = "observed"
                rationale = (
                    "existing package-local tests mention the symbol and exercise at least one catalog test token for this edge class"
                )
            else:
                structure_refs = _structure_support_refs(
                    matched_cue_tags=row.matched_cue_tags,
                    structural_safety_cue_tags=node.structural_safety_cue_tags,
                    audit_status=audit_entry.audit_status,
                    likely_canonical_family=audit_entry.likely_canonical_family,
                )
                matched_structural = [
                    ref
                    for ref in structure_refs
                    if ref.startswith("cue:")
                ]
                if matched_structural and audit_entry.audit_status not in _DEFERRING_AUDIT_STATUSES:
                    status = "bounded_safe_by_structure"
                    posture = "adjudicated"
                    evidence_refs = structure_refs
                    rationale = (
                        "no direct test witness was found, but structural safety cues match the catalog and the upstream semantic audit does not mark the symbol low-confidence"
                    )
                elif audit_entry.audit_status in _DEFERRING_AUDIT_STATUSES or any(
                    effect in {"filesystem_read", "filesystem_write", "subprocess_read"}
                    for effect in audit_entry.side_effect_profile
                ):
                    status = "deferred"
                    posture = "inferred_heuristically"
                    evidence_refs = structure_refs
                    rationale = (
                        "the edge class appears applicable, but this symbol remains low-confidence or crosses a side-effect boundary without a located covering test"
                    )
                else:
                    status = "applicable_unchecked"
                    posture = "derived_deterministically"
                    evidence_refs = structure_refs
                    rationale = (
                        "the edge class is applicable under the starter taxonomy, but no covering test or explicit witness was located"
                    )

        adjudication_rows.append(
            SymbolEdgeAdjudicationRow.model_validate(
                {
                    "edge_class_ref": row.edge_class_ref,
                    "source_applicability_status": row.applicability_status,
                    "adjudication_status": status,
                    "status_posture": posture,
                    "matched_cue_tags": row.matched_cue_tags,
                    "supporting_test_refs": supporting_test_refs,
                    "supporting_evidence_refs": evidence_refs,
                    "suggested_probe_template_refs": row.suggested_probe_template_refs,
                    "witness_summary": witness_summary,
                    "rationale": rationale,
                }
            )
        )

    adjudication_rows.sort(key=lambda item: item.edge_class_ref)
    payload = {
        "schema": "adeu_symbol_edge_adjudication_ledger@1",
        "bound_edge_class_catalog_ref": catalog.catalog_id,
        "bound_probe_template_catalog_ref": probes.catalog_id,
        "scope_manifest_ref": census.scope_manifest_ref,
        "census_hash": census.census_hash,
        "audit_hash": semantic_audit.audit_hash,
        "symbol_id": symbol.symbol_id,
        "module_path": symbol.module_path,
        "qualname": symbol.qualname,
        "symbol_kind": symbol.symbol_kind,
        "bound_applicability_frame_ref": frame.frame_id,
        "ledger_posture": LEDGER_POSTURE,
        "adjudication_rows": [
            item.model_dump(mode="json", exclude_none=True) for item in adjudication_rows
        ],
    }
    payload["ledger_hash"] = sha256_canonical_json(payload)
    payload["ledger_id"] = compute_symbol_edge_adjudication_ledger_id(payload)
    return SymbolEdgeAdjudicationLedger.model_validate(payload)


def derive_scope_symbol_edge_adjudication_ledgers(
    *,
    repo_root: Path,
    census: SymbolCensus,
    coverage_report: SymbolAuditCoverageReport,
    semantic_audit: SymbolSemanticAudit,
    applicability_frames: list[SymbolEdgeApplicabilityFrame] | None = None,
    edge_class_catalog: EdgeClassCatalog | None = None,
    probe_template_catalog: EdgeProbeTemplateCatalog | None = None,
) -> list[SymbolEdgeAdjudicationLedger]:
    catalog = edge_class_catalog or build_starter_edge_class_catalog()
    probes = probe_template_catalog or build_starter_edge_probe_template_catalog(
        edge_class_catalog=catalog
    )
    frames_by_symbol_id = {
        frame.symbol_id: frame
        for frame in (applicability_frames or [])
    }
    return [
        derive_symbol_edge_adjudication_ledger(
            repo_root=repo_root,
            census=census,
            coverage_report=coverage_report,
            semantic_audit=semantic_audit,
            symbol_id=symbol.symbol_id,
            applicability_frame=frames_by_symbol_id.get(symbol.symbol_id),
            edge_class_catalog=catalog,
            probe_template_catalog=probes,
        )
        for symbol in census.symbols
    ]


__all__ = [
    "LEDGER_POSTURE",
    "derive_scope_symbol_edge_adjudication_ledgers",
    "derive_symbol_edge_adjudication_ledger",
]
