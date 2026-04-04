from __future__ import annotations

import ast
import hashlib
from pathlib import Path

from .models import (
    DEFAULT_SYMBOL_KINDS,
    ScopeManifestSourceFile,
    SymbolAuditScopeManifest,
    SymbolCensus,
    SymbolCensusEntry,
    SymbolKind,
    _sha256_canonical_payload,
    compute_scope_manifest_id,
    compute_symbol_audit_symbol_id,
)

REFERENCE_ARCHITECTURE_IR_PILOT_SCOPE_SOURCE_FILES: tuple[str, ...] = (
    "packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py",
    "packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_settlement.py",
    "packages/adeu_architecture_ir/src/adeu_architecture_ir/export_schema.py",
)


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _read_repo_file(repo_root: Path, repo_rel_path: str) -> bytes:
    return (repo_root / repo_rel_path).read_bytes()


def _signature_text(node: ast.AST) -> str:
    if isinstance(node, ast.ClassDef):
        pieces = [ast.unparse(base) for base in node.bases]
        pieces.extend(
            f"{kw.arg}={ast.unparse(kw.value)}" if kw.arg else ast.unparse(kw.value)
            for kw in node.keywords
        )
        joined = ", ".join(pieces)
        return f"class {node.name}" + (f"({joined})" if joined else "")
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        prefix = "async def " if isinstance(node, ast.AsyncFunctionDef) else "def "
        returns = f" -> {ast.unparse(node.returns)}" if node.returns is not None else ""
        return f"{prefix}{node.name}({ast.unparse(node.args)}){returns}"
    raise TypeError(type(node))


def _docstring_excerpt(node: ast.AST) -> str | None:
    docstring = ast.get_docstring(node)
    if not docstring:
        return None
    normalized = " ".join(docstring.strip().split())
    return normalized[:160] if normalized else None


class _Collector(ast.NodeVisitor):
    def __init__(self, *, module_path: str) -> None:
        self._module_path = module_path
        self._stack: list[dict[str, str]] = []
        self.entries: list[dict[str, object]] = []

    def _push_symbol(self, node: ast.AST, *, symbol_name: str, symbol_kind: SymbolKind) -> None:
        qualname = ".".join([frame["symbol_name"] for frame in self._stack] + [symbol_name])
        symbol_id = compute_symbol_audit_symbol_id(
            module_path=self._module_path, qualname=qualname, symbol_kind=symbol_kind
        )
        entry = {
            "symbol_id": symbol_id,
            "module_path": self._module_path,
            "qualname": qualname,
            "symbol_name": symbol_name,
            "symbol_kind": symbol_kind,
            "start_line": node.lineno,
            "end_line": getattr(node, "end_lineno", node.lineno),
            "parent_symbol_id": self._stack[-1]["symbol_id"] if self._stack else None,
            "signature_text": _signature_text(node),
            "decorators_or_modifiers": sorted(
                {ast.unparse(item) for item in getattr(node, "decorator_list", [])}
            ),
            "class_bases": (
                sorted(
                    {ast.unparse(base) for base in node.bases}
                    | {
                        f"{kw.arg}={ast.unparse(kw.value)}" if kw.arg else ast.unparse(kw.value)
                        for kw in node.keywords
                    }
                )
                if isinstance(node, ast.ClassDef)
                else []
            ),
            "docstring_excerpt": _docstring_excerpt(node),
            "census_index": 0,
            "extractor_confidence_posture": "authoritative_for_explicit_parseable_defs",
            "parse_status": "parsed",
        }
        self.entries.append(entry)
        self._stack.append(
            {"symbol_id": symbol_id, "symbol_name": symbol_name, "symbol_kind": symbol_kind}
        )
        self.generic_visit(node)
        self._stack.pop()

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self._push_symbol(node, symbol_name=node.name, symbol_kind="class")

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        parent_kind = self._stack[-1]["symbol_kind"] if self._stack else None
        if parent_kind == "class":
            symbol_kind: SymbolKind = "method"
        elif parent_kind in {"function", "method", "local_function"}:
            symbol_kind = "local_function"
        else:
            symbol_kind = "function"
        self._push_symbol(node, symbol_name=node.name, symbol_kind=symbol_kind)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self.visit_FunctionDef(node)


def build_reference_architecture_ir_scope_manifest(*, repo_root: Path) -> SymbolAuditScopeManifest:
    source_files = [
        ScopeManifestSourceFile(
            file_path=repo_rel_path,
            sha256=_sha256_bytes(_read_repo_file(repo_root, repo_rel_path)),
        )
        for repo_rel_path in REFERENCE_ARCHITECTURE_IR_PILOT_SCOPE_SOURCE_FILES
    ]
    scope_hash = _sha256_canonical_payload(
        {
            "schema": "adeu_symbol_audit_scope_manifest@1",
            "language": "python",
            "source_files": [item.model_dump(mode="json") for item in source_files],
            "symbol_kinds_included": list(DEFAULT_SYMBOL_KINDS),
        }
    )
    scope_manifest_id = compute_scope_manifest_id(
        {
            "schema": "adeu_symbol_audit_scope_manifest@1",
            "language": "python",
            "source_files": [item.model_dump(mode="json") for item in source_files],
            "symbol_kinds_included": list(DEFAULT_SYMBOL_KINDS),
            "scope_hash": scope_hash,
        }
    )
    return SymbolAuditScopeManifest.model_validate(
        {
            "schema": "adeu_symbol_audit_scope_manifest@1",
            "scope_manifest_id": scope_manifest_id,
            "language": "python",
            "source_files": [item.model_dump(mode="json") for item in source_files],
            "symbol_kinds_included": list(DEFAULT_SYMBOL_KINDS),
            "scope_hash": scope_hash,
        }
    )


def build_symbol_census(
    *, repo_root: Path, scope_manifest: SymbolAuditScopeManifest
) -> SymbolCensus:
    source_files = [item.model_copy(deep=True) for item in scope_manifest.source_files]
    collected_entries: list[dict[str, object]] = []
    for source_file in source_files:
        tree = ast.parse((repo_root / source_file.file_path).read_text(encoding="utf-8"))
        collector = _Collector(module_path=source_file.file_path)
        collector.visit(tree)
        collected_entries.extend(collector.entries)

    collected_entries.sort(
        key=lambda entry: (
            entry["module_path"],
            entry["start_line"],
            entry["end_line"],
            entry["symbol_kind"],
            entry["qualname"],
        )
    )
    for index, entry in enumerate(collected_entries, start=1):
        entry["census_index"] = index

    validated_entries = [SymbolCensusEntry.model_validate(entry) for entry in collected_entries]
    census_payload = {
        "schema": "adeu_symbol_census@1",
        "scope_manifest_ref": scope_manifest.scope_manifest_id,
        "language": scope_manifest.language,
        "source_files": [item.model_dump(mode="json") for item in source_files],
        "symbol_kinds_included": list(scope_manifest.symbol_kinds_included),
        "symbol_count": len(validated_entries),
        "symbols": [
            entry.model_dump(mode="json", exclude_none=True) for entry in validated_entries
        ],
    }
    census_hash = _sha256_canonical_payload(census_payload)
    census_payload["census_hash"] = census_hash
    return SymbolCensus.model_validate(census_payload)


__all__ = [
    "REFERENCE_ARCHITECTURE_IR_PILOT_SCOPE_SOURCE_FILES",
    "build_reference_architecture_ir_scope_manifest",
    "build_symbol_census",
]
