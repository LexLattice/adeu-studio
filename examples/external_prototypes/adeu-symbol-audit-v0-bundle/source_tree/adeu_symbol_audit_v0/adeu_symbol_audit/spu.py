from __future__ import annotations

import ast
import hashlib
import json
import re
from collections import defaultdict
from pathlib import Path

from .models import AuditEvidenceRef, SymbolCensus, SymbolSemanticAudit, SymbolSemanticAuditEntry

def _canonical_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)

def _sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()

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

def _collect_symbol_nodes(repo_root: Path, census: SymbolCensus) -> dict[str, ast.AST]:
    nodes: dict[str, ast.AST] = {}
    grouped: dict[str, list[tuple[int, str, str]]] = defaultdict(list)
    for symbol in census.symbols:
        grouped[symbol.file_path].append((symbol.start_line, symbol.symbol_id, symbol.fq_name))
    for file_path, rows in grouped.items():
        tree = ast.parse((repo_root / file_path).read_text(encoding="utf-8"))
        by_line = defaultdict(list)
        for start_line, symbol_id, fq_name in rows:
            by_line[start_line].append((symbol_id, fq_name))
        class Visitor(ast.NodeVisitor):
            def visit_ClassDef(self, node: ast.ClassDef) -> None:
                for symbol_id, fq_name in by_line.get(node.lineno, []):
                    if fq_name.split(".")[-1] == node.name:
                        nodes[symbol_id] = node
                self.generic_visit(node)
            def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
                for symbol_id, fq_name in by_line.get(node.lineno, []):
                    if fq_name.split(".")[-1] == node.name:
                        nodes[symbol_id] = node
                self.generic_visit(node)
            visit_AsyncFunctionDef = visit_FunctionDef
        Visitor().visit(tree)
    return nodes

def _tokens(name: str) -> set[str]:
    parts = re.split(r"[._]+", name)
    tokens: list[str] = []
    for part in parts:
        if not part:
            continue
        part = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", part)
        tokens.extend(piece.lower() for piece in part.split())
    return set(tokens)

def _jaccard(a: str, b: str) -> float:
    left = _tokens(a)
    right = _tokens(b)
    return len(left & right) / len(left | right) if left and right else 0.0

def build_semantic_audit(*, repo_root: Path, census: SymbolCensus) -> SymbolSemanticAudit:
    nodes = _collect_symbol_nodes(repo_root, census)
    name_to_ids: dict[str, list[str]] = defaultdict(list)
    for symbol in census.symbols:
        name_to_ids[symbol.symbol_name].append(symbol.symbol_id)

    entries: list[SymbolSemanticAuditEntry] = []
    for symbol in census.symbols:
        node = nodes[symbol.symbol_id]
        calls = _call_names(node)
        side_effect_profile: list[str] = []
        if any(name.startswith("subprocess.run") for name in calls):
            side_effect_profile.append("subprocess_read")
        if any(name.endswith("read_text") or name.endswith("read_bytes") for name in calls):
            side_effect_profile.append("filesystem_read")
        if any(name.endswith("write_text") or name.endswith("mkdir") for name in calls):
            side_effect_profile.append("filesystem_write")
        if any("model_validate" in name for name in calls):
            side_effect_profile.append("schema_validation")
        if not side_effect_profile:
            side_effect_profile.append("in_process_only")

        likely_canonical_family = "general_helper"
        role_summary = "General deterministic helper"
        local_behavior_summary = "Provides local deterministic helper logic for the enclosing contract workflow."
        confidence_band = "low"
        audit_status = "audited_low_confidence"
        abstraction_candidate_notes = None
        uncertainty_notes = []
        overlap_candidate_symbol_ids = [candidate for candidate in name_to_ids[symbol.symbol_name] if candidate != symbol.symbol_id]

        if symbol.symbol_kind == "class" and "BaseModel" in symbol.class_bases:
            likely_canonical_family = "pydantic_contract_model"
            role_summary = "Typed contract carrier with schema validation semantics"
            local_behavior_summary = "Declares a typed contract surface whose field constraints are enforced by attached validators."
            confidence_band = "medium"
        elif any("model_validator" in item for item in symbol.decorators_or_modifiers):
            likely_canonical_family = "pydantic_post_validation"
            role_summary = "Post-parse contract validator"
            local_behavior_summary = "Rewrites/normalizes fields after model parse and enforces cross-field invariants."
            confidence_band = "medium"
        elif symbol.symbol_name.startswith("canonicalize_"):
            likely_canonical_family = "canonicalization"
            role_summary = "Canonical payload normalizer / validator"
            local_behavior_summary = "Validates a payload against the contract model and re-emits canonical JSON-safe form."
            confidence_band = "medium"
        elif symbol.symbol_name.startswith("materialize_"):
            likely_canonical_family = "materialization"
            role_summary = "Payload completion helper that fills carried fields then canonicalizes"
            local_behavior_summary = "Fills carried identity and boundary fields into a partial payload, then canonicalizes."
            confidence_band = "medium"
        elif symbol.symbol_name.startswith("compute_"):
            likely_canonical_family = "hash_or_id_computation"
            role_summary = "Deterministic hash or identity computation"
            local_behavior_summary = "Computes a stable digest from a canonicalized payload basis."
            confidence_band = "medium"
        elif symbol.symbol_name.startswith("_normalize_"):
            likely_canonical_family = "normalization_helper"
            role_summary = "String/ref/path normalization helper"
            local_behavior_summary = "Normalizes input text into a repo-safe canonical form and rejects illegal path or ref shapes."
            confidence_band = "medium"
        elif symbol.symbol_name.startswith("_assert_"):
            likely_canonical_family = "validation_helper"
            role_summary = "Assertion / invariant helper"
            local_behavior_summary = "Checks a local invariant and raises ValueError on mismatch."
            confidence_band = "medium"
        elif symbol.symbol_name.startswith("_write_"):
            likely_canonical_family = "io_emit_helper"
            role_summary = "Filesystem emission helper"
            local_behavior_summary = "Writes structured artifact content to disk after ensuring directory existence."
            confidence_band = "medium"
        elif symbol.symbol_name == "main":
            likely_canonical_family = "orchestration_entrypoint"
            role_summary = "Orchestrates schema export for this package"
            local_behavior_summary = "Builds schema mappings and writes authoritative and mirrored schema files."
            confidence_band = "medium"
        elif symbol.symbol_kind == "local_function":
            likely_canonical_family = "nested_validation_helper"
            role_summary = "Nested helper scoped to outer validator"
            local_behavior_summary = "Checks a specific reference against source-set or captured-input constraints inside the enclosing validator."
            confidence_band = "low"

        if symbol.file_path.endswith("analysis_request.py"):
            architectural_purpose = (
                "Supports the V41-A analysis request contract: scope declaration, snapshot identity binding, "
                "source-set capture, and canonicalization."
            )
        elif symbol.file_path.endswith("analysis_settlement.py"):
            architectural_purpose = (
                "Supports the V41-B settlement frame contract: interpretation registers, entitlement gating, "
                "and request-bound reference checks."
            )
        else:
            architectural_purpose = (
                "Exports package JSON Schemas into authoritative package/schema and mirrored spec/ locations."
            )

        for other in census.symbols:
            if other.symbol_id == symbol.symbol_id:
                continue
            if _jaccard(symbol.fq_name, other.fq_name) >= 0.65 and other.symbol_id not in overlap_candidate_symbol_ids:
                overlap_candidate_symbol_ids.append(other.symbol_id)

        if symbol.symbol_name == "_validation_context":
            abstraction_candidate_notes = (
                "Appears in both analysis_request.py and analysis_settlement.py with the same broad shape; "
                "candidate for shared helper extraction if semantics remain identical."
            )

        if not symbol.docstring_excerpt:
            uncertainty_notes.append("No docstring present in symbol body.")
        if symbol.symbol_kind == "local_function":
            uncertainty_notes.append(
                "Nested helper role inferred mainly from enclosing method and local calls, not from a public contract."
            )

        evidence_refs = [
            AuditEvidenceRef(
                evidence_kind="source_span",
                detail=f"{symbol.file_path}#L{symbol.start_line}-L{symbol.end_line}",
            )
        ]
        for decorator in symbol.decorators_or_modifiers:
            evidence_refs.append(AuditEvidenceRef(evidence_kind="decorator", detail=decorator))
        for baseclass in symbol.class_bases:
            evidence_refs.append(AuditEvidenceRef(evidence_kind="baseclass", detail=baseclass))
        if calls:
            evidence_refs.append(
                AuditEvidenceRef(
                    evidence_kind="call_summary",
                    detail=" | ".join(calls[:8]),
                )
            )

        if confidence_band in {"medium", "high"}:
            audit_status = "audited_hypothesis"

        entries.append(
            SymbolSemanticAuditEntry(
                symbol_id=symbol.symbol_id,
                audit_status=audit_status,
                role_summary=role_summary,
                architectural_purpose=architectural_purpose,
                local_behavior_summary=local_behavior_summary,
                inputs_outputs_summary=symbol.signature_text,
                side_effect_profile=sorted(set(side_effect_profile)),
                dependency_position=(
                    "contract_surface" if likely_canonical_family == "pydantic_contract_model" else
                    "orchestration_entrypoint" if symbol.symbol_name == "main" else
                    "artifact_emitter" if "filesystem_write" in side_effect_profile else
                    "validation_or_boundary_bridge" if "schema_validation" in side_effect_profile else
                    "local_helper"
                ),
                likely_canonical_family=likely_canonical_family,
                overlap_candidate_symbol_ids=sorted(set(overlap_candidate_symbol_ids))[:8],
                abstraction_candidate_notes=abstraction_candidate_notes,
                evidence_refs=evidence_refs,
                uncertainty_notes=uncertainty_notes,
                confidence_band=confidence_band,
            )
        )

    entries = sorted(entries, key=lambda item: item.symbol_id)
    audit_hash = "sha256:" + _sha256_text(
        _canonical_json(
            {"census_hash": census.census_hash, "audit_entries": [entry.model_dump(mode="json") for entry in entries]}
        )
    )
    return SymbolSemanticAudit(
        schema="adeu_symbol_semantic_audit@1",
        scope_id=census.scope_id,
        census_hash=census.census_hash,
        spu_name="adeu_symbol_audit.heuristic_spu",
        spu_version="0.1.0",
        audit_entry_count=len(entries),
        audit_hash=audit_hash,
        audit_entries=entries,
    )
