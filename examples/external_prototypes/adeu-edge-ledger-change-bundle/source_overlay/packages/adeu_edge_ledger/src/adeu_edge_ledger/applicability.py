from __future__ import annotations

import ast
import hashlib
import re
from collections import defaultdict
from pathlib import Path
from typing import DefaultDict

from adeu_symbol_audit import SymbolAuditCoverageReport, SymbolCensus, SymbolCensusEntry, SymbolSemanticAudit
from urm_runtime.hashing import sha256_canonical_json

from .models import (
    EdgeClassCatalog,
    EdgeProbeTemplateCatalog,
    SymbolEdgeApplicabilityFrame,
    SymbolEdgeApplicabilityRow,
    SymbolKind,
    compute_symbol_edge_applicability_frame_id,
)
from .taxonomy import build_starter_edge_class_catalog, build_starter_edge_probe_template_catalog

FRAME_POSTURE = "starter_taxonomy_over_released_v50_stack"
_WORD_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def _validate_v50_stack(
    *,
    census: SymbolCensus,
    coverage_report: SymbolAuditCoverageReport,
    semantic_audit: SymbolSemanticAudit,
) -> None:
    if coverage_report.coverage_status != "closed_clean":
        raise ValueError("edge applicability requires coverage_report.coverage_status = closed_clean")
    if coverage_report.scope_manifest_ref != census.scope_manifest_ref:
        raise ValueError("edge applicability requires coverage_report.scope_manifest_ref to match census")
    if coverage_report.census_scope_manifest_ref != census.scope_manifest_ref:
        raise ValueError(
            "edge applicability requires coverage_report.census_scope_manifest_ref to match census"
        )
    if coverage_report.census_hash != census.census_hash:
        raise ValueError("edge applicability requires matching census_hash between coverage and census")
    if semantic_audit.scope_manifest_ref != census.scope_manifest_ref:
        raise ValueError("edge applicability requires matching scope_manifest_ref between audit and census")
    if semantic_audit.census_hash != census.census_hash:
        raise ValueError("edge applicability requires matching census_hash between audit and census")


def _read_verified_source_file(*, repo_root: Path, file_path: str, sha256: str) -> str:
    file_bytes = (repo_root / file_path).read_bytes()
    if hashlib.sha256(file_bytes).hexdigest() != sha256:
        raise ValueError(f"edge applicability requires source file hash match for {file_path}")
    return file_bytes.decode("utf-8")


def _dotted_name(node: ast.AST) -> str | None:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        prefix = _dotted_name(node.value)
        return f"{prefix}.{node.attr}" if prefix else node.attr
    if isinstance(node, ast.Call):
        return _dotted_name(node.func)
    return None


class _NodeCollector(ast.NodeVisitor):
    def __init__(self, *, module_path: str) -> None:
        self._module_path = module_path
        self._stack: list[tuple[str, SymbolKind]] = []
        self.nodes: dict[str, ast.AST] = {}

    def _symbol_id(self, *, symbol_name: str, symbol_kind: SymbolKind) -> str:
        qualname = ".".join([frame[0] for frame in self._stack] + [symbol_name])
        return f"symbol:{self._module_path}:{qualname}:{symbol_kind}"

    def _push_symbol(self, node: ast.AST, *, symbol_name: str, symbol_kind: SymbolKind) -> None:
        self.nodes[self._symbol_id(symbol_name=symbol_name, symbol_kind=symbol_kind)] = node
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
        source_text = _read_verified_source_file(
            repo_root=repo_root,
            file_path=source_file.file_path,
            sha256=source_file.sha256,
        )
        tree = ast.parse(source_text, filename=source_file.file_path)
        collector = _NodeCollector(module_path=source_file.file_path)
        collector.visit(tree)
        nodes.update(collector.nodes)
    missing_symbol_ids = [symbol.symbol_id for symbol in census.symbols if symbol.symbol_id not in nodes]
    if missing_symbol_ids:
        raise ValueError(
            "edge applicability requires AST nodes for every census symbol; "
            f"missing {missing_symbol_ids[0]}"
        )
    return nodes


def _annotation_feature_tags(
    text: str,
    *,
    evidence_ref: str,
    feature_evidence: DefaultDict[str, set[str]],
) -> None:
    lowered = text.lower()
    if "optional" in lowered or "none" in lowered or "| none" in lowered:
        feature_evidence["feature:optional_annotation"].add(evidence_ref)
    if any(token in lowered for token in ("list", "dict", "set", "tuple", "sequence")):
        feature_evidence["feature:collection_like"].add(evidence_ref)
    if any(token in lowered for token in ("path", "pureposixpath", "pathlib")):
        feature_evidence["feature:path_like"].add(evidence_ref)
    if any(token in lowered for token in ("int", "float", "index", "count", "line")):
        feature_evidence["feature:numeric_annotation"].add(evidence_ref)
    if "literal" in lowered:
        feature_evidence["feature:literal_like"].add(evidence_ref)


class _FeatureCollector(ast.NodeVisitor):
    def __init__(self) -> None:
        self.feature_evidence: DefaultDict[str, set[str]] = defaultdict(set)

    def _add(self, tag: str, ref: str) -> None:
        self.feature_evidence[tag].add(ref)

    def visit_Call(self, node: ast.Call) -> None:
        dotted = _dotted_name(node.func)
        if dotted:
            self._add(f"call:{dotted}", f"call:{dotted}")
            lowered = dotted.lower()
            if lowered.endswith("sorted") or lowered == "sorted":
                self._add("feature:sorted_call", f"call:{dotted}")
            if lowered.endswith("set") or lowered == "set":
                self._add("feature:set_call", f"call:{dotted}")
            if lowered.endswith("len") or lowered == "len":
                self._add("feature:len_call", f"call:{dotted}")
            if "deepcopy" in lowered:
                self._add("feature:deepcopy_call", f"call:{dotted}")
            if "model_validate" in lowered:
                self._add("feature:model_validate_call", f"call:{dotted}")
            if "model_dump" in lowered:
                self._add("feature:model_dump_call", f"call:{dotted}")
            if any(token in lowered for token in ("json.loads", "json.dumps", "loads", "dumps")):
                self._add("feature:json_loads_or_dumps", f"call:{dotted}")
            if any(token in lowered for token in ("sha256", "hashlib", "sha256_text", "sha256_canonical_json")):
                self._add("feature:hashlib_or_sha", f"call:{dotted}")
            if "subprocess.run" in lowered:
                self._add("feature:subprocess_boundary", f"call:{dotted}")
                self._add("feature:side_effect_boundary", f"call:{dotted}")
            if any(token in lowered for token in ("read_text", "read_bytes", "open")):
                self._add("feature:file_read_boundary", f"call:{dotted}")
                self._add("feature:side_effect_boundary", f"call:{dotted}")
            if any(token in lowered for token in ("write_text", "write_bytes", "mkdir")):
                self._add("feature:file_write_boundary", f"call:{dotted}")
                self._add("feature:side_effect_boundary", f"call:{dotted}")
            if any(token in lowered for token in ("exists", "is_file", "rglob", "resolve")):
                self._add("feature:exists_or_is_file", f"call:{dotted}")
            if any(token in lowered for token in ("strip", "replace")):
                self._add("feature:strip_or_replace", f"call:{dotted}")
            if any(token in lowered for token in ("lower", "upper")):
                self._add("feature:lower_or_upper", f"call:{dotted}")
            if any(token in lowered for token in ("startswith", "endswith")):
                self._add("feature:startswith_or_endswith", f"call:{dotted}")
        self.generic_visit(node)

    def visit_If(self, node: ast.If) -> None:
        self._add("feature:has_if", f"line:{node.lineno}")
        self.generic_visit(node)

    def visit_Try(self, node: ast.Try) -> None:
        self._add("feature:has_try", f"line:{node.lineno}")
        if node.handlers:
            self._add("feature:except_block", f"line:{node.lineno}")
        self.generic_visit(node)

    def visit_Raise(self, node: ast.Raise) -> None:
        self._add("feature:raise_stmt", f"line:{node.lineno}")
        exc_name = _dotted_name(node.exc) if node.exc is not None else None
        if exc_name and any(token in exc_name for token in ("ValueError", "ValidationError")):
            self._add("feature:raises_value_error", f"line:{node.lineno}")
        self.generic_visit(node)

    def visit_Compare(self, node: ast.Compare) -> None:
        self._add("feature:has_compare", f"line:{node.lineno}")
        self._add("feature:compare_ops", f"line:{node.lineno}")
        if any(isinstance(op, (ast.In, ast.NotIn)) for op in node.ops):
            self._add("feature:membership_check", f"line:{node.lineno}")
        for comparator in node.comparators:
            if isinstance(comparator, ast.Constant):
                if comparator.value is None:
                    self._add("feature:none_compare", f"line:{node.lineno}")
                if comparator.value in {0, 1, -1}:
                    self._add("feature:compare_to_zero", f"line:{node.lineno}")
                if isinstance(comparator.value, str):
                    self._tokens_from_text(comparator.value, ref=f"line:{node.lineno}")
        self.generic_visit(node)

    def visit_Assert(self, node: ast.Assert) -> None:
        self._add("feature:raises_value_error", f"line:{node.lineno}")
        self.generic_visit(node)

    def visit_Assign(self, node: ast.Assign) -> None:
        for target in node.targets:
            if isinstance(target, ast.Attribute):
                self._add("feature:attribute_assignment", f"line:{node.lineno}")
            if isinstance(target, ast.Subscript):
                self._add("feature:subscript_assignment", f"line:{node.lineno}")
        self.generic_visit(node)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        if isinstance(node.target, ast.Attribute):
            self._add("feature:attribute_assignment", f"line:{node.lineno}")
        if isinstance(node.target, ast.Subscript):
            self._add("feature:subscript_assignment", f"line:{node.lineno}")
        self.generic_visit(node)

    def visit_Constant(self, node: ast.Constant) -> None:
        if isinstance(node.value, str):
            self._tokens_from_text(node.value, ref=f"line:{node.lineno}")
        self.generic_visit(node)

    def _tokens_from_text(self, text: str, *, ref: str) -> None:
        tokens = {token.lower() for token in _WORD_RE.findall(text)}
        if not tokens:
            return
        self._add("feature:error_message_string", ref)
        if tokens & {"missing", "none", "null", "required", "absent"}:
            self._add("feature:missing_terms", ref)
        if tokens & {"scope", "boundary", "outside", "inside", "subtree", "root", "prefix"}:
            self._add("feature:scope_terms", ref)
            self._add("feature:boundary_terms", ref)
        if tokens & {"mismatch", "match", "drift", "exact", "same"}:
            self._add("feature:mismatch_terms", ref)
        if tokens & {"ref", "refs", "fragment", "qualname", "module", "path"}:
            self._add("feature:fragment_or_ref_terms", ref)
            self._add("feature:ref_or_path_name", ref)
        if tokens & {"git", "show"}:
            self._add("feature:git_literal", ref)
        if tokens & {"mode", "kind", "status", "class"}:
            self._add("feature:mode_or_kind_name", ref)
        if tokens & {"lineage", "hash", "id", "policy", "request", "source", "settlement"}:
            self._add("feature:cross_field_terms", ref)
        if tokens & {"sorted", "duplicate", "duplicates", "unique", "order"}:
            self._add("feature:sorted_unique_pattern", ref)


def _add_name_features(
    *,
    symbol: SymbolCensusEntry,
    feature_evidence: DefaultDict[str, set[str]],
) -> None:
    name_ref = f"symbol:{symbol.symbol_name}"
    lowered_name = symbol.symbol_name.lower()
    lowered_qualname = symbol.qualname.lower()
    lowered_signature = symbol.signature_text.lower()
    if lowered_name.startswith("canonicalize_"):
        feature_evidence["feature:canonicalization_name"].add(name_ref)
    if lowered_name.startswith("materialize_"):
        feature_evidence["feature:materialization_name"].add(name_ref)
    if lowered_name.startswith("compute_"):
        feature_evidence["feature:compute_name"].add(name_ref)
    if lowered_name.startswith("_normalize_") or lowered_name.startswith("normalize_"):
        feature_evidence["feature:normalize_name"].add(name_ref)
    if lowered_name.startswith("_assert_") or "validate" in lowered_name:
        feature_evidence["feature:validation_name"].add(name_ref)
    if any(token in lowered_name for token in ("path", "ref", "root", "scope", "source", "target")):
        feature_evidence["feature:ref_or_path_name"].add(name_ref)
    if any(token in lowered_name for token in ("scope", "boundary", "prefix", "subtree", "root")):
        feature_evidence["feature:scope_terms"].add(name_ref)
        feature_evidence["feature:boundary_terms"].add(name_ref)
    if any(token in lowered_name for token in ("mode", "kind", "status", "class")):
        feature_evidence["feature:mode_or_kind_name"].add(name_ref)
    if any(token in lowered_name for token in ("mismatch", "match", "hash", "id", "drift")):
        feature_evidence["feature:mismatch_terms"].add(name_ref)
    if any(token in lowered_name for token in ("request", "source", "settlement", "policy", "lineage")):
        feature_evidence["feature:cross_field_terms"].add(name_ref)
    if any(token in lowered_name for token in ("ref", "refs", "fragment", "qualname")):
        feature_evidence["feature:fragment_or_ref_terms"].add(name_ref)
    if "literal[" in lowered_signature:
        feature_evidence["feature:literal_like"].add(name_ref)
    if any(token in lowered_signature for token in ("path", "pureposixpath", "pathlib")):
        feature_evidence["feature:path_like"].add(name_ref)
    if any(token in lowered_signature for token in ("list", "dict", "set", "tuple")):
        feature_evidence["feature:collection_like"].add(name_ref)
    if any(token in lowered_signature for token in ("none", "optional")):
        feature_evidence["feature:optional_annotation"].add(name_ref)
    if any(token in lowered_signature for token in ("int", "float", "line", "count", "index")):
        feature_evidence["feature:numeric_annotation"].add(name_ref)


def _add_symbol_audit_features(
    *,
    symbol: SymbolCensusEntry,
    audit_entry: object,
    feature_evidence: DefaultDict[str, set[str]],
) -> None:
    for decorator in symbol.decorators_or_modifiers:
        lowered = decorator.lower()
        if "model_validator" in lowered:
            feature_evidence["feature:model_validator"].add(f"decorator:{decorator}")
            feature_evidence["feature:validation_name"].add(f"decorator:{decorator}")
    for base in symbol.class_bases:
        if "BaseModel" in base:
            feature_evidence["feature:contract_model_class"].add(f"base:{base}")
    for effect in getattr(audit_entry, "side_effect_profile"):
        if effect in {"filesystem_read", "filesystem_write", "subprocess_read", "schema_validation"}:
            feature_evidence["feature:side_effect_boundary"].add(f"side_effect:{effect}")
        if effect == "filesystem_read":
            feature_evidence["feature:file_read_boundary"].add(f"side_effect:{effect}")
        if effect == "filesystem_write":
            feature_evidence["feature:file_write_boundary"].add(f"side_effect:{effect}")
        if effect == "subprocess_read":
            feature_evidence["feature:subprocess_boundary"].add(f"side_effect:{effect}")
        if effect == "schema_validation":
            feature_evidence["feature:model_validate_call"].add(f"side_effect:{effect}")
            feature_evidence["feature:model_dump_call"].add(f"side_effect:{effect}")
    likely_family = getattr(audit_entry, "likely_canonical_family")
    if likely_family == "pydantic_post_validation":
        feature_evidence["feature:model_validator"].add(f"audit_family:{likely_family}")
    if likely_family == "pydantic_contract_model":
        feature_evidence["feature:contract_model_class"].add(f"audit_family:{likely_family}")


def _add_parameter_and_field_features(
    *,
    node: ast.AST,
    feature_evidence: DefaultDict[str, set[str]],
) -> None:
    def handle_name(name: str, *, ref: str) -> None:
        lowered = name.lower()
        if any(token in lowered for token in ("path", "ref", "root", "scope", "source", "target")):
            feature_evidence["feature:ref_or_path_name"].add(ref)
        if any(token in lowered for token in ("scope", "boundary", "prefix", "root")):
            feature_evidence["feature:scope_terms"].add(ref)
            feature_evidence["feature:boundary_terms"].add(ref)
        if any(token in lowered for token in ("mode", "kind", "status", "class")):
            feature_evidence["feature:mode_or_kind_name"].add(ref)
        if any(token in lowered for token in ("hash", "id", "lineage", "policy", "request", "source")):
            feature_evidence["feature:cross_field_terms"].add(ref)
        if any(token in lowered for token in ("fragment", "qualname", "ref", "refs")):
            feature_evidence["feature:fragment_or_ref_terms"].add(ref)

    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        arguments = list(node.args.posonlyargs) + list(node.args.args) + list(node.args.kwonlyargs)
        if node.args.vararg is not None:
            arguments.append(node.args.vararg)
        if node.args.kwarg is not None:
            arguments.append(node.args.kwarg)
        for arg in arguments:
            ref = f"param:{arg.arg}"
            handle_name(arg.arg, ref=ref)
            if arg.annotation is not None:
                _annotation_feature_tags(ast.unparse(arg.annotation), evidence_ref=ref, feature_evidence=feature_evidence)
        return

    if isinstance(node, ast.ClassDef):
        for child in node.body:
            if isinstance(child, ast.AnnAssign) and isinstance(child.target, ast.Name):
                ref = f"field:{child.target.id}"
                handle_name(child.target.id, ref=ref)
                _annotation_feature_tags(ast.unparse(child.annotation), evidence_ref=ref, feature_evidence=feature_evidence)
            if isinstance(child, ast.Assign):
                for target in child.targets:
                    if isinstance(target, ast.Name):
                        handle_name(target.id, ref=f"field:{target.id}")


def _collect_symbol_features(
    *,
    symbol: SymbolCensusEntry,
    audit_entry: object,
    node: ast.AST,
) -> tuple[list[str], dict[str, list[str]]]:
    feature_evidence: DefaultDict[str, set[str]] = defaultdict(set)
    _add_name_features(symbol=symbol, feature_evidence=feature_evidence)
    _add_symbol_audit_features(symbol=symbol, audit_entry=audit_entry, feature_evidence=feature_evidence)
    _add_parameter_and_field_features(node=node, feature_evidence=feature_evidence)
    collector = _FeatureCollector()
    collector.visit(node)
    for tag, refs in collector.feature_evidence.items():
        feature_evidence[tag].update(refs)
    features = sorted(feature_evidence)
    materialized_evidence = {tag: sorted(refs) for tag, refs in sorted(feature_evidence.items())}
    return features, materialized_evidence


def _build_applicability_row(
    *,
    node: object,
    present_features: set[str],
    feature_evidence: dict[str, list[str]],
) -> SymbolEdgeApplicabilityRow:
    required = set(node.required_cue_tags)
    supporting = set(node.supporting_cue_tags)
    matched_required = sorted(required & present_features)
    matched_supporting = sorted(supporting & present_features)
    matched = sorted(set(matched_required) | set(matched_supporting))
    if required and set(matched_required) == required and (not supporting or matched_supporting):
        applicability_status = "applicable"
        epistemic_posture = "derived_deterministically"
    elif (required and matched_required) or matched_supporting:
        applicability_status = "underdetermined"
        epistemic_posture = "inferred_heuristically"
    else:
        applicability_status = "not_applicable"
        epistemic_posture = "derived_deterministically"
    concrete_bindings = sorted(
        {
            ref
            for tag in matched
            for ref in feature_evidence.get(tag, [])
        }
    )
    if applicability_status == "applicable":
        rationale = (
            "applicable via matched cue tags " + ", ".join(matched)
            if matched
            else "applicable via catalog rule without additional matched cues"
        )
    elif applicability_status == "underdetermined":
        rationale = "partial cue match only; at least one applicability cue fired without full closure"
    else:
        rationale = "no required or supporting applicability cues matched for this symbol"
    return SymbolEdgeApplicabilityRow.model_validate(
        {
            "edge_class_ref": node.edge_class_ref,
            "applicability_status": applicability_status,
            "epistemic_posture": epistemic_posture,
            "matched_cue_tags": matched,
            "concrete_binding_refs": concrete_bindings[:8],
            "suggested_probe_template_refs": node.default_probe_template_refs,
            "rationale": rationale,
        }
    )


def derive_symbol_edge_applicability_frame(
    *,
    repo_root: Path,
    census: SymbolCensus,
    coverage_report: SymbolAuditCoverageReport,
    semantic_audit: SymbolSemanticAudit,
    symbol_id: str,
    edge_class_catalog: EdgeClassCatalog | None = None,
    probe_template_catalog: EdgeProbeTemplateCatalog | None = None,
) -> SymbolEdgeApplicabilityFrame:
    _validate_v50_stack(census=census, coverage_report=coverage_report, semantic_audit=semantic_audit)
    catalog = edge_class_catalog or build_starter_edge_class_catalog()
    probes = probe_template_catalog or build_starter_edge_probe_template_catalog(
        edge_class_catalog=catalog
    )
    nodes = _collect_symbol_nodes(repo_root=repo_root, census=census)
    census_by_id = {entry.symbol_id: entry for entry in census.symbols}
    audit_by_id = {entry.symbol_id: entry for entry in semantic_audit.audit_entries}
    if symbol_id not in census_by_id:
        raise ValueError(f"symbol_id not found in census: {symbol_id}")
    if symbol_id not in audit_by_id:
        raise ValueError(f"symbol_id not found in semantic_audit: {symbol_id}")
    symbol = census_by_id[symbol_id]
    node = nodes[symbol_id]
    audit_entry = audit_by_id[symbol_id]
    features, feature_evidence = _collect_symbol_features(
        symbol=symbol,
        audit_entry=audit_entry,
        node=node,
    )
    present = set(features)
    applicability_rows = [
        _build_applicability_row(
            node=catalog_node,
            present_features=present,
            feature_evidence=feature_evidence,
        )
        for catalog_node in catalog.nodes
        if catalog_node.node_kind == "archetype"
    ]
    applicability_rows.sort(key=lambda row: row.edge_class_ref)
    payload = {
        "schema": "adeu_symbol_edge_applicability_frame@1",
        "bound_edge_class_catalog_ref": catalog.catalog_id,
        "bound_probe_template_catalog_ref": probes.catalog_id,
        "scope_manifest_ref": census.scope_manifest_ref,
        "census_hash": census.census_hash,
        "audit_hash": semantic_audit.audit_hash,
        "symbol_id": symbol.symbol_id,
        "module_path": symbol.module_path,
        "qualname": symbol.qualname,
        "symbol_kind": symbol.symbol_kind,
        "frame_posture": FRAME_POSTURE,
        "applicability_rows": [
            row.model_dump(mode="json", exclude_none=True) for row in applicability_rows
        ],
    }
    payload["frame_hash"] = sha256_canonical_json(payload)
    payload["frame_id"] = compute_symbol_edge_applicability_frame_id(payload)
    return SymbolEdgeApplicabilityFrame.model_validate(payload)


def derive_scope_symbol_edge_applicability_frames(
    *,
    repo_root: Path,
    census: SymbolCensus,
    coverage_report: SymbolAuditCoverageReport,
    semantic_audit: SymbolSemanticAudit,
    edge_class_catalog: EdgeClassCatalog | None = None,
    probe_template_catalog: EdgeProbeTemplateCatalog | None = None,
) -> list[SymbolEdgeApplicabilityFrame]:
    catalog = edge_class_catalog or build_starter_edge_class_catalog()
    probes = probe_template_catalog or build_starter_edge_probe_template_catalog(
        edge_class_catalog=catalog
    )
    return [
        derive_symbol_edge_applicability_frame(
            repo_root=repo_root,
            census=census,
            coverage_report=coverage_report,
            semantic_audit=semantic_audit,
            symbol_id=symbol.symbol_id,
            edge_class_catalog=catalog,
            probe_template_catalog=probes,
        )
        for symbol in census.symbols
    ]


__all__ = [
    "FRAME_POSTURE",
    "derive_scope_symbol_edge_applicability_frames",
    "derive_symbol_edge_applicability_frame",
]
