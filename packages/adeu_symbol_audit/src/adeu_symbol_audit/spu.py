from __future__ import annotations

import ast
import hashlib
from pathlib import Path

from .models import (
    SymbolAuditCoverageReport,
    SymbolCensus,
    SymbolCensusEntry,
    SymbolKind,
    SymbolSemanticAudit,
    SymbolSemanticAuditEntry,
    SymbolSemanticEvidenceRef,
    _sha256_canonical_payload,
    compute_symbol_audit_symbol_id,
)

SPU_NAME = "adeu_symbol_audit.v50b_independent_spu"
SPU_VERSION = "1.0.0"
SEMANTIC_VOCABULARY_POSTURE = "explicit_independence_from_v49"


def _dotted_name(node: ast.AST) -> str | None:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        prefix = _dotted_name(node.value)
        return f"{prefix}.{node.attr}" if prefix else node.attr
    if isinstance(node, ast.Call):
        return _dotted_name(node.func)
    return None


def _call_names(node: ast.AST) -> list[str]:
    names: set[str] = set()

    class Visitor(ast.NodeVisitor):
        def visit_Call(self, inner: ast.Call) -> None:
            dotted = _dotted_name(inner.func)
            if dotted:
                names.add(dotted)
            self.generic_visit(inner)

    Visitor().visit(node)
    return sorted(names)


def _read_verified_census_source_file(*, repo_root: Path, file_path: str, sha256: str) -> str:
    file_bytes = (repo_root / file_path).read_bytes()
    if hashlib.sha256(file_bytes).hexdigest() != sha256:
        raise ValueError(f"semantic audit requires source file hash match for {file_path}")
    return file_bytes.decode("utf-8")


class _NodeCollector(ast.NodeVisitor):
    def __init__(self, *, module_path: str) -> None:
        self._module_path = module_path
        self._stack: list[tuple[str, SymbolKind]] = []
        self.nodes: dict[str, ast.AST] = {}

    def _push_symbol(self, node: ast.AST, *, symbol_name: str, symbol_kind: SymbolKind) -> None:
        qualname = ".".join([frame[0] for frame in self._stack] + [symbol_name])
        symbol_id = compute_symbol_audit_symbol_id(
            module_path=self._module_path,
            qualname=qualname,
            symbol_kind=symbol_kind,
        )
        self.nodes[symbol_id] = node
        self._stack.append((symbol_name, symbol_kind))
        self.generic_visit(node)
        self._stack.pop()

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self._push_symbol(node, symbol_name=node.name, symbol_kind="class")

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        parent_kind = self._stack[-1][1] if self._stack else None
        if parent_kind == "class":
            symbol_kind: SymbolKind = "method"
        elif parent_kind in {"function", "method", "local_function"}:
            symbol_kind = "local_function"
        else:
            symbol_kind = "function"
        self._push_symbol(node, symbol_name=node.name, symbol_kind=symbol_kind)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self.visit_FunctionDef(node)


def _collect_symbol_nodes(*, repo_root: Path, census: SymbolCensus) -> dict[str, ast.AST]:
    nodes: dict[str, ast.AST] = {}
    for source_file in census.source_files:
        file_text = _read_verified_census_source_file(
            repo_root=repo_root,
            file_path=source_file.file_path,
            sha256=source_file.sha256,
        )
        tree = ast.parse(file_text, filename=source_file.file_path)
        collector = _NodeCollector(module_path=source_file.file_path)
        collector.visit(tree)
        nodes.update(collector.nodes)
    missing_symbol_ids = sorted(
        entry.symbol_id for entry in census.symbols if entry.symbol_id not in nodes
    )
    if missing_symbol_ids:
        raise ValueError(
            "semantic audit requires AST nodes for every census symbol; "
            f"missing {missing_symbol_ids[0]}"
        )
    return nodes


def _side_effect_profile(call_names: list[str]) -> list[str]:
    effects: set[str] = set()
    if any(name.startswith("subprocess.run") for name in call_names):
        effects.add("subprocess_read")
    if any(name.endswith("read_text") or name.endswith("read_bytes") for name in call_names):
        effects.add("filesystem_read")
    if any(
        name.endswith("write_text") or name.endswith("write_bytes") or name.endswith("mkdir")
        for name in call_names
    ):
        effects.add("filesystem_write")
    if any("model_validate" in name or "model_dump" in name for name in call_names):
        effects.add("schema_validation")
    if not effects:
        effects.add("in_process_only")
    return sorted(effects)


def _family_role_and_behavior(
    *, symbol: SymbolCensusEntry, side_effect_profile: list[str]
) -> tuple[str, str, str, str]:
    if symbol.symbol_kind == "class" and "BaseModel" in symbol.class_bases:
        return (
            "pydantic_contract_model",
            "Typed contract carrier with schema validation semantics",
            (
                "Declares a typed contract surface whose field constraints are "
                "enforced by attached validators."
            ),
            "contract_surface",
        )
    if any("model_validator" in item for item in symbol.decorators_or_modifiers):
        return (
            "pydantic_post_validation",
            "Post-parse contract validator",
            "Rewrites or validates fields after model parse and enforces cross-field invariants.",
            "validation_or_boundary_bridge",
        )
    if symbol.symbol_name.startswith("canonicalize_"):
        return (
            "canonicalization",
            "Canonical payload normalizer and validator",
            (
                "Validates a payload against the surrounding contract model and "
                "re-emits canonical JSON-safe form."
            ),
            "validation_or_boundary_bridge",
        )
    if symbol.symbol_name.startswith("materialize_"):
        return (
            "materialization",
            "Payload completion helper",
            (
                "Fills carried fields into a partial payload and materializes the "
                "deterministic contract surface."
            ),
            "validation_or_boundary_bridge",
        )
    if symbol.symbol_name.startswith("compute_"):
        return (
            "hash_or_id_computation",
            "Deterministic hash or identity computation",
            "Computes a stable digest or identity from a canonical payload basis.",
            "local_helper",
        )
    if symbol.symbol_name.startswith("_normalize_"):
        return (
            "normalization_helper",
            "String, ref, or path normalization helper",
            "Normalizes input text into a repo-safe canonical form and rejects illegal shapes.",
            "local_helper",
        )
    if symbol.symbol_name.startswith("_assert_"):
        return (
            "validation_helper",
            "Assertion or invariant helper",
            "Checks a local invariant and raises on mismatch.",
            "local_helper",
        )
    if symbol.symbol_name.startswith("_write_"):
        return (
            "io_emit_helper",
            "Filesystem emission helper",
            "Writes structured artifact content to disk after ensuring directory existence.",
            "artifact_emitter",
        )
    if symbol.symbol_name == "main":
        return (
            "schema_export_orchestrator",
            "Schema export orchestrator",
            "Coordinates schema export for the bounded package surface.",
            "orchestration_entrypoint",
        )
    if symbol.symbol_kind == "local_function":
        return (
            "nested_validation_helper",
            "Nested helper scoped to an outer validator or helper",
            "Checks local constraints inside the enclosing function or method body.",
            "local_helper",
        )
    if "filesystem_write" in side_effect_profile:
        return (
            "artifact_emitter",
            "Artifact emission helper",
            "Coordinates deterministic artifact emission over the bounded package surface.",
            "artifact_emitter",
        )
    return (
        "general_helper",
        "General deterministic helper",
        "Provides local deterministic helper logic for the enclosing contract workflow.",
        "local_helper",
    )


def _architectural_purpose(module_path: str) -> str:
    if module_path.endswith("analysis_request.py"):
        return (
            "Supports the analysis-request contract: scope declaration, snapshot identity "
            "binding, source-set capture, and canonicalization."
        )
    if module_path.endswith("analysis_settlement.py"):
        return (
            "Supports the settlement-frame contract: interpretation registers, "
            "entitlement gating, and request-bound reference checks."
        )
    return "Supports schema export and authoritative schema publication for architecture IR."


def _audit_status_and_confidence(symbol: SymbolCensusEntry) -> tuple[str, str]:
    if symbol.symbol_name == "main":
        return ("unresolved", "low")
    if any("model_validator" in item for item in symbol.decorators_or_modifiers):
        return ("audited_hypothesis", "medium")
    if symbol.symbol_kind == "class" and "BaseModel" in symbol.class_bases:
        return ("audited_hypothesis", "medium")
    if symbol.symbol_name.startswith(("canonicalize_", "materialize_", "compute_")):
        return ("audited_hypothesis", "medium")
    if symbol.symbol_kind == "local_function" or symbol.symbol_name.startswith("_"):
        return ("audited_low_confidence", "low")
    return ("audited_hypothesis", "medium")


def _overlap_candidate_symbol_ids(symbol: SymbolCensusEntry, census: SymbolCensus) -> list[str]:
    overlap_ids = [
        candidate.symbol_id
        for candidate in census.symbols
        if candidate.symbol_id != symbol.symbol_id and candidate.symbol_name == symbol.symbol_name
    ]
    if symbol.parent_symbol_id is not None and symbol.parent_symbol_id not in overlap_ids:
        overlap_ids.append(symbol.parent_symbol_id)
    return sorted(set(overlap_ids))


def _uncertainty_notes(symbol: SymbolCensusEntry) -> list[str]:
    notes: list[str] = []
    if symbol.docstring_excerpt is None:
        notes.append("No docstring present in symbol body.")
    if symbol.symbol_kind == "local_function":
        notes.append(
            "Nested helper role inferred mainly from the enclosing method or function context."
        )
    if symbol.symbol_name == "main":
        notes.append("Entrypoint semantics remain broad relative to the bounded starter ledger.")
    return sorted(set(notes))


def _build_evidence_refs(
    *, symbol: SymbolCensusEntry, call_names: list[str]
) -> list[SymbolSemanticEvidenceRef]:
    evidence_refs: list[SymbolSemanticEvidenceRef] = [
        SymbolSemanticEvidenceRef(
            evidence_kind="source_span",
            detail=f"{symbol.module_path}#L{symbol.start_line}-L{symbol.end_line}",
        )
    ]
    if call_names:
        evidence_refs.append(
            SymbolSemanticEvidenceRef(
                evidence_kind="call_summary",
                detail=" | ".join(call_names[:8]),
            )
        )
    for decorator in symbol.decorators_or_modifiers:
        evidence_refs.append(
            SymbolSemanticEvidenceRef(evidence_kind="decorator", detail=decorator)
        )
    for baseclass in symbol.class_bases:
        evidence_refs.append(
            SymbolSemanticEvidenceRef(evidence_kind="baseclass", detail=baseclass)
        )
    return evidence_refs


def build_symbol_semantic_audit(
    *,
    repo_root: Path,
    census: SymbolCensus,
    coverage_report: SymbolAuditCoverageReport,
) -> SymbolSemanticAudit:
    if coverage_report.coverage_status != "closed_clean":
        raise ValueError("semantic audit requires coverage_report.coverage_status = closed_clean")
    if coverage_report.scope_manifest_ref != census.scope_manifest_ref:
        raise ValueError(
            "semantic audit requires matching scope_manifest_ref "
            "between census and coverage_report"
        )
    if coverage_report.census_scope_manifest_ref != census.scope_manifest_ref:
        raise ValueError(
            "semantic audit requires matching census_scope_manifest_ref "
            "and census scope_manifest_ref"
        )
    if coverage_report.census_hash != census.census_hash:
        raise ValueError(
            "semantic audit requires matching census_hash "
            "between census and coverage_report"
        )

    nodes = _collect_symbol_nodes(repo_root=repo_root, census=census)
    audit_entries: list[SymbolSemanticAuditEntry] = []
    for symbol in census.symbols:
        node = nodes[symbol.symbol_id]
        call_names = _call_names(node)
        side_effect_profile = _side_effect_profile(call_names)
        (
            likely_canonical_family,
            role_summary,
            local_behavior_summary,
            dependency_position,
        ) = _family_role_and_behavior(symbol=symbol, side_effect_profile=side_effect_profile)
        audit_status, confidence_band = _audit_status_and_confidence(symbol)
        audit_entries.append(
            SymbolSemanticAuditEntry.model_validate(
                {
                    "symbol_id": symbol.symbol_id,
                    "audit_status": audit_status,
                    "confidence_band": confidence_band,
                    "role_summary": role_summary,
                    "architectural_purpose": _architectural_purpose(symbol.module_path),
                    "local_behavior_summary": local_behavior_summary,
                    "inputs_outputs_summary": symbol.signature_text,
                    "side_effect_profile": side_effect_profile,
                    "dependency_position": dependency_position,
                    "likely_canonical_family": likely_canonical_family,
                    "overlap_candidate_symbol_ids": _overlap_candidate_symbol_ids(symbol, census),
                    "abstraction_candidate_notes": None,
                    "evidence_refs": [
                        evidence.model_dump(mode="json")
                        for evidence in _build_evidence_refs(symbol=symbol, call_names=call_names)
                    ],
                    "uncertainty_notes": _uncertainty_notes(symbol),
                }
            )
        )

    audit_payload = {
        "schema": "adeu_symbol_semantic_audit@1",
        "scope_manifest_ref": census.scope_manifest_ref,
        "census_hash": census.census_hash,
        "semantic_vocabulary_posture": SEMANTIC_VOCABULARY_POSTURE,
        "spu_name": SPU_NAME,
        "spu_version": SPU_VERSION,
        "audit_entries": [
            entry.model_dump(mode="json", exclude_none=True) for entry in audit_entries
        ],
    }
    audit_payload["audit_hash"] = _sha256_canonical_payload(audit_payload)
    return SymbolSemanticAudit.model_validate(audit_payload)


__all__ = [
    "SEMANTIC_VOCABULARY_POSTURE",
    "SPU_NAME",
    "SPU_VERSION",
    "build_symbol_semantic_audit",
]
