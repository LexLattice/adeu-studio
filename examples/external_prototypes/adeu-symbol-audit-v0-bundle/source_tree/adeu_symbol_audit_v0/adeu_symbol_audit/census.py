from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path

from .models import SourceFileSnapshot, SymbolCensus, SymbolCensusEntry

def _canonical_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)

def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()

def _symbol_id(*, file_path: str, fq_name: str, symbol_kind: str) -> str:
    return f"symbol:{file_path}:{fq_name}:{symbol_kind}"

def _signature_text(node: ast.AST) -> str:
    if isinstance(node, ast.ClassDef):
        pieces = [ast.unparse(base) for base in node.bases]
        pieces += [
            f"{kw.arg}={ast.unparse(kw.value)}" if kw.arg else ast.unparse(kw.value)
            for kw in node.keywords
        ]
        joined = ", ".join(pieces)
        return f"class {node.name}" + (f"({joined})" if joined else "")
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        prefix = "async def " if isinstance(node, ast.AsyncFunctionDef) else "def "
        returns = f" -> {ast.unparse(node.returns)}" if node.returns is not None else ""
        return f"{prefix}{node.name}({ast.unparse(node.args)}){returns}"
    raise TypeError(type(node))

class _Collector(ast.NodeVisitor):
    def __init__(self, *, file_path: str) -> None:
        self.file_path = file_path
        self.symbols: list[dict[str, object]] = []
        self._stack: list[dict[str, str]] = []

    def _add_symbol(self, node: ast.AST, *, name: str, symbol_kind: str) -> None:
        fq_name = ".".join([entry["symbol_name"] for entry in self._stack] + [name])
        symbol = {
            "symbol_id": _symbol_id(file_path=self.file_path, fq_name=fq_name, symbol_kind=symbol_kind),
            "fq_name": fq_name,
            "symbol_name": name,
            "symbol_kind": symbol_kind,
            "language": "python",
            "file_path": self.file_path,
            "start_line": node.lineno,
            "end_line": getattr(node, "end_lineno", node.lineno),
            "parent_symbol_id": self._stack[-1]["symbol_id"] if self._stack else None,
            "signature_text": _signature_text(node),
            "decorators_or_modifiers": [ast.unparse(item) for item in getattr(node, "decorator_list", [])],
            "class_bases": (
                [ast.unparse(base) for base in node.bases]
                + [
                    f"{kw.arg}={ast.unparse(kw.value)}" if kw.arg else ast.unparse(kw.value)
                    for kw in node.keywords
                ]
                if isinstance(node, ast.ClassDef)
                else []
            ),
            "docstring_excerpt": (
                " ".join((ast.get_docstring(node) or "").strip().split())[:160]
                if ast.get_docstring(node)
                else None
            ),
            "census_index": 0,
            "parser_version": "python.ast@3.11",
            "parser_confidence": "authoritative_for_explicit_parseable_defs",
            "parse_status": "parsed",
        }
        self.symbols.append(symbol)
        self._stack.append({"symbol_id": symbol["symbol_id"], "symbol_name": name, "symbol_kind": symbol_kind})
        self.generic_visit(node)
        self._stack.pop()

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self._add_symbol(node, name=node.name, symbol_kind="class")

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        parent_kind = self._stack[-1]["symbol_kind"] if self._stack else None
        if parent_kind == "class":
            symbol_kind = "method"
        elif parent_kind in {"function", "method", "local_function"}:
            symbol_kind = "local_function"
        else:
            symbol_kind = "function"
        self._add_symbol(node, name=node.name, symbol_kind=symbol_kind)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self.visit_FunctionDef(node)

def build_symbol_census(
    *,
    repo_root: Path,
    scope_id: str,
    source_paths: list[str],
) -> SymbolCensus:
    source_files = [
        SourceFileSnapshot(
            file_path=path,
            sha256=_sha256_bytes((repo_root / path).read_bytes()),
        )
        for path in sorted(source_paths)
    ]
    entries: list[dict[str, object]] = []
    for path in sorted(source_paths):
        tree = ast.parse((repo_root / path).read_text(encoding="utf-8"))
        collector = _Collector(file_path=path)
        collector.visit(tree)
        entries.extend(collector.symbols)

    entries = sorted(
        entries,
        key=lambda item: (
            item["file_path"],
            item["start_line"],
            item["end_line"],
            item["symbol_kind"],
            item["fq_name"],
        ),
    )
    for index, entry in enumerate(entries, start=1):
        entry["census_index"] = index

    canonical_basis = {
        "source_files": [item.model_dump(mode="json") for item in source_files],
        "symbols": entries,
    }
    census_hash = "sha256:" + _sha256_bytes(_canonical_json(canonical_basis).encode("utf-8"))

    return SymbolCensus(
        schema="adeu_symbol_census@1",
        scope_id=scope_id,
        language="python",
        source_files=source_files,
        symbol_kinds_included=["class", "function", "method", "local_function"],
        symbol_count=len(entries),
        census_hash=census_hash,
        symbols=[SymbolCensusEntry.model_validate(entry) for entry in entries],
    )
