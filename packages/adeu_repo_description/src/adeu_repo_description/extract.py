from __future__ import annotations

import ast
import json
import re
from copy import deepcopy
from pathlib import Path, PurePosixPath
from typing import Any

from adeu_ir.repo import repo_root
from urm_runtime.hashing import sha256_canonical_json

from .models import (
    REPO_DEPENDENCY_GRAPH_SCHEMA,
    REPO_DESCRIPTIVE_NORMATIVE_BINDING_FRAME_SCHEMA,
    REPO_OPTIMIZATION_REGISTER_SCHEMA,
    REPO_SYMBOL_CATALOG_SCHEMA,
    REPO_TEST_INTENT_MATRIX_SCHEMA,
    SCHEMA_VISIBLE_ENTITY_COVERAGE_MODE,
    V45A_CLASSIFICATION_POLICY_REF,
    V45C_DEPENDENCY_POLICY_REF,
    RepoDescriptionEvidenceRef,
    RepoSchemaFamilyRegistry,
    compute_claimed_invariant_binding_id,
    compute_internal_module_boundary_ref,
    compute_repo_descriptive_normative_binding_entry_id,
    compute_repo_optimization_entry_id,
    compute_repo_test_intent_entry_id,
    compute_repo_test_ref,
    compute_symbol_id,
    compute_v45a_classification_policy_hash,
    compute_v45c_v102_dependency_policy_hash,
    materialize_repo_arc_dependency_register_payload,
    materialize_repo_dependency_graph_payload,
    materialize_repo_descriptive_normative_binding_frame_payload,
    materialize_repo_entity_catalog_payload,
    materialize_repo_optimization_register_payload,
    materialize_repo_schema_family_registry_payload,
    materialize_repo_symbol_catalog_payload,
    materialize_repo_test_intent_matrix_payload,
    representative_schema_keys,
    validate_repo_descriptive_normative_binding_frame_against_v45_baseline,
    validate_repo_optimization_register_against_v45_baseline,
    validate_repo_symbol_catalog_dependency_graph_pair,
    validate_repo_test_intent_matrix_against_v45b,
)

_DEFAULT_SOURCE_PATHS: tuple[str, ...] = (
    "packages/adeu_arc_agi/schema/adeu_arc_task_packet.v1.json",
    "packages/adeu_architecture_ir/schema/adeu_architecture_analysis_request.v1.json",
    "packages/adeu_core_ir/schema/meta_loop_sequence_contract.v1.json",
    "packages/adeu_core_ir/schema/ux_interaction_contract.v1.json",
    "packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json",
    "spec/policy_registry.schema.json",
    "packages/adeu_ir/schema/adeu.validator_result.v0.json",
)
_DEFAULT_V45C_SOURCE_PATHS: tuple[str, ...] = (
    "docs/DRAFT_NEXT_ARC_OPTIONS_v28.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS100.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS102.md",
)
_DEFAULT_V45B_SOURCE_PATHS: tuple[str, ...] = (
    "packages/adeu_repo_description/src/adeu_repo_description/__init__.py",
    "packages/adeu_repo_description/src/adeu_repo_description/export_schema.py",
    "packages/adeu_repo_description/src/adeu_repo_description/extract.py",
    "packages/adeu_repo_description/src/adeu_repo_description/models.py",
)
_DEFAULT_V45D_SOURCE_PATHS: tuple[str, ...] = (
    "packages/adeu_repo_description/tests/test_repo_description_v45b.py",
)
_DEFAULT_V45E_SOURCE_PATHS: tuple[str, ...] = (
    "packages/adeu_repo_description/src/adeu_repo_description/__init__.py",
    "packages/adeu_repo_description/src/adeu_repo_description/export_schema.py",
    "packages/adeu_repo_description/src/adeu_repo_description/extract.py",
    "packages/adeu_repo_description/src/adeu_repo_description/models.py",
    "packages/adeu_repo_description/tests/test_repo_description_v45b.py",
)
_DEFAULT_V45F_SOURCE_PATHS: tuple[str, ...] = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS105.md",
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS105.md",
    "docs/ASSESSMENT_vNEXT_PLUS105_EDGES.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v28.md",
    "docs/DRAFT_V45_REPO_SELF_DESCRIPTION_DECOMPOSITION_v0.md",
)
_V45C_V102_REFERENCE_FIXTURE_PATH = (
    "apps/api/fixtures/repo_description/vnext_plus102/"
    "repo_arc_dependency_register_v102_reference.json"
)


def _assert_repo_rel_path(value: str, *, field_name: str) -> str:
    normalized = value.strip().replace("\\", "/")
    if not normalized:
        raise ValueError(f"{field_name} must not be empty")
    if normalized.startswith("/"):
        raise ValueError(f"{field_name} must be repository-relative")
    if ".." in PurePosixPath(normalized).parts:
        raise ValueError(f"{field_name} must not contain parent traversal")
    return str(PurePosixPath(normalized))


def _schema_discriminator(payload: dict[str, Any], *, fallback_path: str) -> str:
    schema_properties = payload.get("properties")
    if isinstance(schema_properties, dict):
        schema_field = schema_properties.get("schema")
        if isinstance(schema_field, dict):
            schema_const = schema_field.get("const")
            if isinstance(schema_const, str) and schema_const:
                return schema_const
    return f"missing_schema_discriminator:{fallback_path}"


def _schema_key(schema_discriminator: str, *, schema_path: str) -> str:
    if "@" in schema_discriminator:
        return schema_discriminator.split("@", 1)[0]
    filename = Path(schema_path).name
    if filename.endswith(".schema.json"):
        stem = filename[: -len(".schema.json")]
    elif filename.endswith(".json"):
        stem = filename[: -len(".json")]
    else:
        stem = filename
    # Drop trailing version suffixes like ".v1", ".v0_1", ".v10".
    stem = re.sub(r"\.v[0-9][0-9_]*$", "", stem)
    return stem


def _family_cluster(schema_key: str) -> str:
    if schema_key.startswith("adeu_arc_"):
        return "adeu_arc"
    if schema_key.startswith("adeu_architecture_"):
        return "adeu_architecture"
    if schema_key.startswith("meta_"):
        return "meta"
    if schema_key.startswith("ux_"):
        return "ux"
    if schema_key.startswith("policy_"):
        return "policy"
    if schema_key.startswith("adeu_core_ir"):
        return "adeu_core_ir"
    if schema_key.startswith("adeu.validator"):
        return "adeu_validator"
    if schema_key.startswith("adeu_"):
        return "adeu_generic"
    return "residual"


def _lineage_overlay(family_cluster: str) -> str:
    return {
        "adeu_arc": "arc_agi_lineage",
        "adeu_architecture": "architecture_lineage",
        "meta": "meta_control_lineage",
        "ux": "ux_governance_lineage",
        "policy": "policy_lineage",
        "adeu_core_ir": "core_ir_lineage",
        "adeu_validator": "validator_lineage",
        "adeu_generic": "adeu_generic_lineage",
        "residual": "residual_lineage",
    }[family_cluster]


def _primary_carrier_class(schema_key: str) -> str:
    key = schema_key.lower().replace(".", "_")
    if any(token in key for token in ("contract", "policy", "rule", "gate")):
        return "ContractGate"
    if any(token in key for token in ("trace", "checkpoint", "log")):
        return "TraceRecord"
    if any(token in key for token in ("manifest", "registry", "catalog", "table", "snapshot")):
        return "CuratedSet"
    if any(token in key for token in ("report", "diagnostic", "resolution", "evidence", "result")):
        return "Adjudication"
    if any(token in key for token in ("ir", "model", "projection", "delta", "payload")):
        return "StructuralModel"
    return "IntakeFrame"


def _secondary_role_form_tags(schema_key: str) -> list[str]:
    key = schema_key.lower().replace(".", "_")
    tags: list[str] = []
    token_map = (
        ("packet", "packet"),
        ("frame", "frame"),
        ("request", "request"),
        ("candidate", "candidate"),
        ("trace", "trace"),
        ("manifest", "manifest"),
        ("registry", "registry"),
        ("catalog", "catalog"),
        ("report", "report"),
        ("diagnostic", "diagnostics"),
        ("result", "result"),
        ("contract", "contract"),
        ("policy", "policy"),
        ("ir", "ir"),
        ("projection", "projection"),
        ("payload", "payload"),
        ("delta", "delta"),
    )
    for token, tag in token_map:
        if token in key:
            tags.append(tag)
    if not tags:
        tags.append("plan")
    return sorted(set(tags))


def _core_envelope_features(payload: dict[str, Any]) -> list[str]:
    features: list[str] = []
    schema_properties = payload.get("properties")
    has_schema_const = False
    if isinstance(schema_properties, dict):
        schema_field = schema_properties.get("schema")
        if isinstance(schema_field, dict):
            has_schema_const = isinstance(schema_field.get("const"), str)
    if has_schema_const:
        features.append("has_schema_const")
    else:
        features.append("missing_schema_const")
    if payload.get("additionalProperties") is False:
        features.append("closed_root")
    if "$defs" in payload:
        features.append("has_defs")
    return sorted(features)


def _residual_flags(payload: dict[str, Any]) -> list[str]:
    flags: list[str] = []
    schema_properties = payload.get("properties")
    has_schema_const = False
    if isinstance(schema_properties, dict):
        schema_field = schema_properties.get("schema")
        if isinstance(schema_field, dict):
            has_schema_const = isinstance(schema_field.get("const"), str)
    if not has_schema_const:
        flags.append("missing_schema_const")
    additional = payload.get("additionalProperties")
    if additional is True:
        flags.append("open_root_map")
    return sorted(flags)


def _classification_method(payload: dict[str, Any], *, schema_discriminator: str) -> str:
    if schema_discriminator.startswith("missing_schema_discriminator:"):
        return "lexical_naming"
    schema_properties = payload.get("properties")
    if isinstance(schema_properties, dict):
        schema_field = schema_properties.get("schema")
        if isinstance(schema_field, dict) and isinstance(schema_field.get("const"), str):
            return "structural_signature"
    return "lexical_naming"


def _classification_posture(classification_method: str) -> str:
    if classification_method == "lexical_naming":
        return "inferred_heuristically"
    return "derived_deterministically"


def _semantic_role_for_carrier(carrier: str) -> str:
    return {
        "IntakeFrame": "intake_surface",
        "TraceRecord": "trace_surface",
        "CuratedSet": "curated_set_surface",
        "Adjudication": "adjudication_surface",
        "ContractGate": "contract_surface",
        "StructuralModel": "structural_model_surface",
    }[carrier]


def _as_repo_rel(path: Path, *, root: Path) -> str:
    return path.relative_to(root).as_posix()


def _default_source_paths() -> list[str]:
    return list(_DEFAULT_SOURCE_PATHS)


def _default_v45b_source_paths() -> list[str]:
    return list(_DEFAULT_V45B_SOURCE_PATHS)


def _default_v45d_source_paths() -> list[str]:
    return list(_DEFAULT_V45D_SOURCE_PATHS)


def _default_v45e_source_paths() -> list[str]:
    return list(_DEFAULT_V45E_SOURCE_PATHS)


def _default_v45f_source_paths() -> list[str]:
    return list(_DEFAULT_V45F_SOURCE_PATHS)


def _load_historical_v45c_v102_reference(*, root: Path) -> dict[str, Any]:
    # V45-E binds V45-C as released historical baseline context. Loading the
    # committed v102 fixture here preserves that explicit historical seam without
    # re-deriving current planning-sensitive V45-C state inside V45-E extraction.
    fixture_path = root / _V45C_V102_REFERENCE_FIXTURE_PATH
    return json.loads(fixture_path.read_text(encoding="utf-8"))


def _module_import_path_for_source_path(source_path: str) -> str:
    normalized = _assert_repo_rel_path(source_path, field_name="source_path")
    marker = "/src/"
    if marker not in normalized or not normalized.endswith(".py"):
        raise ValueError("v45b source_path must be a Python file under a src/ tree")
    module_suffix = normalized.split(marker, 1)[1]
    if module_suffix.endswith("/__init__.py"):
        module_suffix = module_suffix[: -len("/__init__.py")]
    else:
        module_suffix = module_suffix[: -len(".py")]
    return module_suffix.replace("/", ".")


def _source_path_for_module_import_path(
    *,
    module_import_path: str,
    module_to_source_path: dict[str, str],
) -> str | None:
    return module_to_source_path.get(module_import_path)


def _current_package_for_source_path(source_path: str) -> str:
    module_import_path = _module_import_path_for_source_path(source_path)
    if Path(source_path).name == "__init__.py":
        return module_import_path
    if "." not in module_import_path:
        return module_import_path
    return module_import_path.rsplit(".", 1)[0]


def _resolve_import_from_module(
    *,
    source_path: str,
    module: str | None,
    level: int,
) -> str:
    if level == 0:
        return module or ""
    package = _current_package_for_source_path(source_path)
    package_parts = package.split(".") if package else []
    ascend = max(level - 1, 0)
    if ascend > len(package_parts):
        raise ValueError("relative import level exceeds package depth")
    base_parts = package_parts[: len(package_parts) - ascend]
    if module:
        base_parts.extend(module.split("."))
    return ".".join(base_parts)


def _qualname_join(parent: str | None, name: str) -> str:
    if not parent:
        return name
    return f"{parent}.{name}"


def _assignment_target_names_from_target(target: ast.expr) -> set[str]:
    if isinstance(target, ast.Name):
        return {target.id}
    if isinstance(target, (ast.Tuple, ast.List)):
        names: set[str] = set()
        for element in target.elts:
            names.update(_assignment_target_names_from_target(element))
        return names
    if isinstance(target, ast.Starred):
        return _assignment_target_names_from_target(target.value)
    return set()


def _assignment_target_names(node: ast.Assign | ast.AnnAssign) -> list[str]:
    targets: set[str] = set()
    if isinstance(node, ast.Assign):
        raw_targets = node.targets
    else:
        raw_targets = [node.target]
    for target in raw_targets:
        targets.update(_assignment_target_names_from_target(target))
    return sorted(targets)


def _symbol_role_method_for_node(node: ast.AST) -> str:
    if isinstance(node, ast.ClassDef):
        if node.bases or node.decorator_list:
            return "decorator_or_baseclass_rule"
        return "ast_signature"
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        if node.decorator_list:
            return "decorator_or_baseclass_rule"
        return "ast_signature"
    return "ast_signature"


def _expr_to_dotted_name(node: ast.AST) -> str | None:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        parent = _expr_to_dotted_name(node.value)
        if parent is None:
            return None
        return f"{parent}.{node.attr}"
    return None


def _bound_unique_symbol_index(
    *,
    symbol_catalog: dict[str, Any],
) -> tuple[dict[str, str], dict[tuple[str, str], str], dict[str, str]]:
    qualname_to_symbol_ids: dict[str, set[str]] = {}
    module_qualname_to_symbol: dict[tuple[str, str], str] = {}
    source_path_to_module_import_path: dict[str, str] = {}
    for entry in symbol_catalog["symbol_entries"]:
        qualname_to_symbol_ids.setdefault(entry["qualname"], set()).add(entry["symbol_id"])
        module_import_path = _module_import_path_for_source_path(entry["module_path"])
        source_path_to_module_import_path[entry["module_path"]] = module_import_path
        module_qualname_to_symbol[(module_import_path, entry["qualname"])] = entry["symbol_id"]
    unique_qualname_index = {
        qualname: next(iter(symbol_ids))
        for qualname, symbol_ids in qualname_to_symbol_ids.items()
        if len(symbol_ids) == 1
    }
    return unique_qualname_index, module_qualname_to_symbol, source_path_to_module_import_path


def _resolve_import_binding(
    *,
    imported_module: str,
    imported_name: str | None,
    unique_qualname_index: dict[str, str],
    module_qualname_to_symbol: dict[tuple[str, str], str],
    bound_module_to_source_path: dict[str, str],
) -> tuple[str, str] | None:
    if imported_name is not None:
        symbol_id = module_qualname_to_symbol.get((imported_module, imported_name))
        if symbol_id is None:
            symbol_id = unique_qualname_index.get(imported_name)
        if symbol_id is not None:
            return ("internal_symbol", symbol_id)
        imported_submodule = (
            f"{imported_module}.{imported_name}" if imported_module else imported_name
        )
        submodule_source_path = bound_module_to_source_path.get(imported_submodule)
        if submodule_source_path is not None:
            return (
                "internal_module_boundary",
                compute_internal_module_boundary_ref(module_path=submodule_source_path),
            )
    source_path = bound_module_to_source_path.get(imported_module)
    if source_path is not None:
        return (
            "internal_module_boundary",
            compute_internal_module_boundary_ref(module_path=source_path),
        )
    if imported_module.startswith("adeu_") or imported_module.startswith("urm_"):
        return ("external_boundary", f"out_of_scope:{imported_module}")
    return ("external_boundary", f"external:{imported_module}")


def _extract_test_import_aliases(
    *,
    source_path: str,
    tree: ast.Module,
    unique_qualname_index: dict[str, str],
    module_qualname_to_symbol: dict[tuple[str, str], str],
    bound_module_to_source_path: dict[str, str],
) -> dict[str, tuple[str, str]]:
    alias_map: dict[str, tuple[str, str]] = {}
    for node in tree.body:
        if isinstance(node, ast.Import):
            for alias in node.names:
                local_name = alias.asname or alias.name.split(".", 1)[0]
                resolved = _resolve_import_binding(
                    imported_module=alias.name,
                    imported_name=None,
                    unique_qualname_index=unique_qualname_index,
                    module_qualname_to_symbol=module_qualname_to_symbol,
                    bound_module_to_source_path=bound_module_to_source_path,
                )
                if resolved is not None:
                    alias_map[local_name] = resolved
        elif isinstance(node, ast.ImportFrom):
            imported_module = _resolve_import_from_module(
                source_path=source_path,
                module=node.module,
                level=node.level,
            )
            if node.module is None:
                if not imported_module:
                    continue
            for alias in node.names:
                if alias.name == "*":
                    continue
                local_name = alias.asname or alias.name
                resolved = _resolve_import_binding(
                    imported_module=imported_module,
                    imported_name=alias.name,
                    unique_qualname_index=unique_qualname_index,
                    module_qualname_to_symbol=module_qualname_to_symbol,
                    bound_module_to_source_path=bound_module_to_source_path,
                )
                if resolved is not None:
                    alias_map[local_name] = resolved
    return alias_map


def _ref_from_expr(
    expr: ast.AST,
    *,
    alias_map: dict[str, tuple[str, str]],
    provenance_map: dict[str, tuple[str, str]],
) -> tuple[str, str] | None:
    if isinstance(expr, ast.Name):
        return provenance_map.get(expr.id) or alias_map.get(expr.id)
    if isinstance(expr, ast.Attribute):
        return _ref_from_expr(expr.value, alias_map=alias_map, provenance_map=provenance_map)
    if isinstance(expr, ast.Call):
        return _ref_from_expr(expr.func, alias_map=alias_map, provenance_map=provenance_map)
    if isinstance(expr, ast.Subscript):
        return _ref_from_expr(expr.value, alias_map=alias_map, provenance_map=provenance_map)
    collected: list[tuple[str, str]] = []
    for child in ast.iter_child_nodes(expr):
        child_ref = _ref_from_expr(child, alias_map=alias_map, provenance_map=provenance_map)
        if child_ref is not None:
            collected.append(child_ref)
    unique = sorted(set(collected))
    if len(unique) == 1:
        return unique[0]
    return None


def _assignment_target_identifiers(target: ast.expr) -> list[str]:
    return sorted(_assignment_target_names_from_expr_target(target))


def _assignment_target_names_from_expr_target(target: ast.expr) -> set[str]:
    if isinstance(target, ast.Name):
        return {target.id}
    if isinstance(target, (ast.Tuple, ast.List)):
        names: set[str] = set()
        for element in target.elts:
            names.update(_assignment_target_names_from_expr_target(element))
        return names
    if isinstance(target, ast.Starred):
        return _assignment_target_names_from_expr_target(target.value)
    return set()


def _update_test_provenance_for_assignment(
    node: ast.Assign | ast.AnnAssign,
    *,
    alias_map: dict[str, tuple[str, str]],
    provenance_map: dict[str, tuple[str, str]],
) -> None:
    if isinstance(node, ast.AnnAssign) and node.value is None:
        return
    value_ref = _ref_from_expr(
        node.value,
        alias_map=alias_map,
        provenance_map=provenance_map,
    )
    if value_ref is None:
        return
    targets = node.targets if isinstance(node, ast.Assign) else [node.target]
    for target in targets:
        for name in _assignment_target_identifiers(target):
            provenance_map[name] = value_ref


def _iter_assertion_units(body: list[ast.stmt]) -> list[tuple[ast.AST, ast.AST]]:
    units: list[tuple[ast.AST, ast.AST]] = []
    for node in body:
        if isinstance(node, ast.Assert):
            units.append((node, node.test))
        elif isinstance(node, (ast.With, ast.AsyncWith)):
            for item in node.items:
                context_expr = item.context_expr
                dotted = _expr_to_dotted_name(
                    context_expr.func if isinstance(context_expr, ast.Call) else context_expr
                )
                if dotted == "pytest.raises":
                    units.append((node, context_expr))
        elif isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
            func_name = _expr_to_dotted_name(node.value.func) or ""
            terminal = func_name.rsplit(".", 1)[-1]
            if terminal in {"validate", "model_validate", "check_schema"}:
                units.append((node, node.value))
    return units


def _collect_candidate_refs(
    node: ast.AST,
    *,
    alias_map: dict[str, tuple[str, str]],
    provenance_map: dict[str, tuple[str, str]],
    unique_qualname_index: dict[str, str],
) -> list[tuple[str, str, str]]:
    candidates: list[tuple[str, str, str]] = []

    class Visitor(ast.NodeVisitor):
        def visit_Name(self, inner: ast.Name) -> None:
            resolved = provenance_map.get(inner.id) or alias_map.get(inner.id)
            if resolved is not None:
                candidates.append((resolved[0], resolved[1], "direct_reference"))
            self.generic_visit(inner)

        def visit_Constant(self, inner: ast.Constant) -> None:
            if isinstance(inner.value, str):
                literal = inner.value
                if "repo_symbol_catalog" in literal:
                    symbol_id = unique_qualname_index.get("REPO_SYMBOL_CATALOG_SCHEMA")
                    if symbol_id is not None:
                        candidates.append(("internal_symbol", symbol_id, "bounded_inference"))
                if "repo_dependency_graph" in literal:
                    symbol_id = unique_qualname_index.get("REPO_DEPENDENCY_GRAPH_SCHEMA")
                    if symbol_id is not None:
                        candidates.append(("internal_symbol", symbol_id, "bounded_inference"))
            self.generic_visit(inner)

    Visitor().visit(node)
    kind_order = {
        "internal_symbol": 0,
        "internal_module_boundary": 1,
        "external_boundary": 2,
    }
    source_order = {
        "direct_reference": 0,
        "bounded_inference": 1,
        "test_name_convention": 2,
    }
    unique_candidates = sorted(
        set(candidates),
        key=lambda row: (
            kind_order.get(row[0], 99),
            source_order.get(row[2], 99),
            row[1],
        ),
    )
    return unique_candidates


def _fallback_guarded_surface_ref(
    *,
    test_name: str,
    unique_qualname_index: dict[str, str],
    bound_module_to_source_path: dict[str, str],
) -> tuple[str, str, str]:
    lowered = test_name.lower()
    fallback_symbol_names: list[str] = []
    if "symbol_catalog_id" in lowered:
        fallback_symbol_names.append("compute_repo_symbol_catalog_id")
    elif "dependency_graph_id" in lowered:
        fallback_symbol_names.append("compute_repo_dependency_graph_id")
    elif "symbol_catalog" in lowered:
        fallback_symbol_names.append("RepoSymbolCatalog")
        fallback_symbol_names.append("REPO_SYMBOL_CATALOG_SCHEMA")
    elif "dependency_graph" in lowered:
        fallback_symbol_names.append("RepoDependencyGraph")
        fallback_symbol_names.append("REPO_DEPENDENCY_GRAPH_SCHEMA")
    for symbol_name in fallback_symbol_names:
        symbol_id = unique_qualname_index.get(symbol_name)
        if symbol_id is not None:
            return ("internal_symbol", symbol_id, "test_name_convention")
    extract_source = bound_module_to_source_path.get("adeu_repo_description.extract")
    if extract_source is not None:
        return (
            "internal_module_boundary",
            compute_internal_module_boundary_ref(module_path=extract_source),
            "test_name_convention",
        )
    return ("external_boundary", "external:pytest", "test_name_convention")


def _humanize_test_name(name: str) -> str:
    tokens = [token for token in name.split("_") if token and token != "test"]
    if tokens and re.fullmatch(r"v[0-9]+[a-z]?", tokens[0]):
        tokens = tokens[1:]
    return " ".join(tokens)


def _infer_invariant_domain(binding_statement: str) -> str:
    normalized = binding_statement.lower()
    has_deontic = any(
        token in normalized
        for token in (
            "authority",
            "entitlement",
            "gating",
            "scheduler",
            "mutation",
            "blocked",
        )
    )
    has_epistemic = any(
        token in normalized
        for token in (
            "deterministic",
            "validate",
            "replay",
            "snapshot",
            "source",
            "hash",
            "id",
        )
    )
    has_ontic = any(
        token in normalized
        for token in ("schema", "symbol", "dependency", "module", "fixture", "graph")
    )
    if sum([has_deontic, has_epistemic, has_ontic]) > 1:
        return "mixed"
    if has_deontic:
        return "deontics"
    if has_epistemic:
        return "epistemics"
    return "ontology" if has_ontic else "epistemics"


def _assertion_surface_kind(unit_node: ast.AST, unit_expr: ast.AST) -> str:
    if isinstance(unit_node, ast.Assert):
        if isinstance(unit_expr, ast.Compare) and any(
            isinstance(op, (ast.Eq, ast.NotEq)) for op in unit_expr.ops
        ):
            return "equality_assertion"
        return "assert_statement"
    if isinstance(unit_node, (ast.With, ast.AsyncWith)):
        return "pytest_raises"
    return "predicate_call_assertion"


def _derivation_labels(source_kind: str, assertion_surface_kind: str) -> tuple[str, str]:
    if source_kind == "direct_reference":
        return (
            "derived_deterministically",
            "assertion_ast"
            if assertion_surface_kind in {"assert_statement", "equality_assertion", "pytest_raises"}
            else "fixture_or_helper_binding",
        )
    if source_kind == "bounded_inference":
        return ("inferred_heuristically", "bounded_inference_rule")
    return ("inferred_heuristically", "test_name_convention")


def _confidence_posture(derivation_method: str, assertion_surface_kind: str) -> str:
    if derivation_method == "assertion_ast":
        if assertion_surface_kind in {"equality_assertion", "pytest_raises"}:
            return "high"
        return "medium"
    if derivation_method == "fixture_or_helper_binding":
        return "medium"
    return "low"


def _binding_statement_from_test_name(test_name: str) -> str:
    humanized = _humanize_test_name(test_name)
    if not humanized:
        return "bounded test intent claim"
    return humanized


def _entry_payload_for_assertion_unit(
    *,
    source_path: str,
    qualname: str,
    test_kind: str,
    test_name: str,
    unit_node: ast.AST,
    unit_expr: ast.AST,
    alias_map: dict[str, tuple[str, str]],
    provenance_map: dict[str, tuple[str, str]],
    unique_qualname_index: dict[str, str],
    bound_module_to_source_path: dict[str, str],
    evidence_ref: str,
) -> dict[str, Any]:
    assertion_kind = _assertion_surface_kind(unit_node, unit_expr)
    candidate_nodes: list[ast.AST] = [unit_expr]
    if isinstance(unit_node, (ast.With, ast.AsyncWith)):
        candidate_nodes.extend(unit_node.body)
    candidates: list[tuple[str, str, str]] = []
    for candidate_node in candidate_nodes:
        candidates.extend(
            _collect_candidate_refs(
                candidate_node,
                alias_map=alias_map,
                provenance_map=provenance_map,
                unique_qualname_index=unique_qualname_index,
            )
        )
    deduped_candidates = sorted(
        set(candidates),
        key=lambda row: (
            {"internal_symbol": 0, "internal_module_boundary": 1, "external_boundary": 2}.get(
                row[0], 99
            ),
            {"direct_reference": 0, "bounded_inference": 1, "test_name_convention": 2}.get(
                row[2], 99
            ),
            row[1],
        ),
    )
    if deduped_candidates:
        guarded_ref_kind, guarded_ref_value, source_kind = deduped_candidates[0]
    else:
        guarded_ref_kind, guarded_ref_value, source_kind = _fallback_guarded_surface_ref(
            test_name=test_name,
            unique_qualname_index=unique_qualname_index,
            bound_module_to_source_path=bound_module_to_source_path,
        )
    derivation_posture, derivation_method = _derivation_labels(source_kind, assertion_kind)
    binding_statement = _binding_statement_from_test_name(test_name)
    test_ref = compute_repo_test_ref(source_path=source_path, qualname=qualname)
    observed_assertion_surface = {
        "assertion_surface_kind": assertion_kind,
        "assertion_source_ref": f"assertion:{source_path}#L{unit_node.lineno}",
        "assertion_summary": ast.unparse(unit_expr),
    }
    payload_without_entry_id = {
        "test_ref": test_ref,
        "test_kind": test_kind,
        "guarded_surface_ref": {
            "guarded_surface_ref_kind": guarded_ref_kind,
            "guarded_surface_ref_value": guarded_ref_value,
        },
        "claimed_invariant_binding": {
            "binding_id": compute_claimed_invariant_binding_id(
                binding_statement=binding_statement
            ),
            "binding_statement": binding_statement,
        },
        "observed_assertion_surface": observed_assertion_surface,
        "invariant_domain": _infer_invariant_domain(binding_statement),
        "gating_posture": "release_gating",
        "confidence_posture": _confidence_posture(derivation_method, assertion_kind),
        "derivation_posture": derivation_posture,
        "derivation_method": derivation_method,
        "source_artifact_refs": [source_path],
        "supporting_evidence_refs": [evidence_ref],
    }
    return {
        "entry_id": compute_repo_test_intent_entry_id(payload_without_entry_id),
        **payload_without_entry_id,
    }


def _derive_entries_for_test_function(
    *,
    source_path: str,
    function_node: ast.FunctionDef | ast.AsyncFunctionDef,
    qualname: str,
    test_kind: str,
    alias_map: dict[str, tuple[str, str]],
    unique_qualname_index: dict[str, str],
    bound_module_to_source_path: dict[str, str],
    evidence_ref: str,
) -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []

    def visit_body(body: list[ast.stmt], *, provenance_map: dict[str, tuple[str, str]]) -> None:
        for node in body:
            if isinstance(node, (ast.Assign, ast.AnnAssign)):
                _update_test_provenance_for_assignment(
                    node,
                    alias_map=alias_map,
                    provenance_map=provenance_map,
                )
            units = _iter_assertion_units([node])
            for unit_node, unit_expr in units:
                entries.append(
                    _entry_payload_for_assertion_unit(
                        source_path=source_path,
                        qualname=qualname,
                        test_kind=test_kind,
                        test_name=function_node.name,
                        unit_node=unit_node,
                        unit_expr=unit_expr,
                        alias_map=alias_map,
                        provenance_map=provenance_map,
                        unique_qualname_index=unique_qualname_index,
                        bound_module_to_source_path=bound_module_to_source_path,
                        evidence_ref=evidence_ref,
                    )
                )
            for nested in _nested_statement_bodies(node):
                visit_body(nested, provenance_map=dict(provenance_map))

    visit_body(function_node.body, provenance_map={})
    return entries


def _derive_v45d_entries_for_source_path(
    *,
    source_path: str,
    tree: ast.Module,
    alias_map: dict[str, tuple[str, str]],
    unique_qualname_index: dict[str, str],
    bound_module_to_source_path: dict[str, str],
) -> list[dict[str, Any]]:
    evidence_ref = f"evidence:test_source:{source_path}:ast"
    entries: list[dict[str, Any]] = []
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name.startswith(
            "test_"
        ):
            entries.extend(
                _derive_entries_for_test_function(
                    source_path=source_path,
                    function_node=node,
                    qualname=node.name,
                    test_kind="pytest_function",
                    alias_map=alias_map,
                    unique_qualname_index=unique_qualname_index,
                    bound_module_to_source_path=bound_module_to_source_path,
                    evidence_ref=evidence_ref,
                )
            )
        elif isinstance(node, ast.ClassDef) and node.name.startswith("Test"):
            for inner in node.body:
                if isinstance(
                    inner, (ast.FunctionDef, ast.AsyncFunctionDef)
                ) and inner.name.startswith("test_"):
                    entries.extend(
                        _derive_entries_for_test_function(
                            source_path=source_path,
                            function_node=inner,
                            qualname=f"{node.name}.{inner.name}",
                            test_kind="pytest_method",
                            alias_map=alias_map,
                            unique_qualname_index=unique_qualname_index,
                            bound_module_to_source_path=bound_module_to_source_path,
                            evidence_ref=evidence_ref,
                        )
                    )
    if not entries:
        raise ValueError(f"test source path did not yield any test-intent rows: {source_path}")
    return entries


def _nested_statement_bodies(node: ast.stmt) -> list[list[ast.stmt]]:
    if isinstance(node, (ast.If, ast.For, ast.AsyncFor, ast.While)):
        return [body for body in (node.body, node.orelse) if body]
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return [node.body] if node.body else []
    if isinstance(node, ast.Try):
        bodies = [node.body, node.orelse, node.finalbody]
        bodies.extend(handler.body for handler in node.handlers)
        return [body for body in bodies if body]
    if isinstance(node, ast.Match):
        return [case.body for case in node.cases if case.body]
    return []


def _repo_out_of_scope_module(module_import_path: str) -> bool:
    root = module_import_path.split(".", 1)[0]
    return root.startswith("adeu_") or root.startswith("urm_")


def _classify_external_target(module_or_symbol: str) -> tuple[str, str]:
    if _repo_out_of_scope_module(module_or_symbol):
        return "boundary_out_of_scope", f"out_of_scope:{module_or_symbol}"
    return "boundary_external", f"external:{module_or_symbol}"


def _edge_id_for_payload(payload: dict[str, Any]) -> str:
    digest = sha256_canonical_json(payload)
    return f"edge_{digest[:24]}"


def _merge_external_dependency_suffix(*, endpoint_ref: str, rest: list[str]) -> str:
    prefix, suffix = endpoint_ref.split(":", 1)
    suffix_parts = suffix.split(".")
    overlap = 0
    max_overlap = min(len(suffix_parts), len(rest))
    for size in range(max_overlap, 0, -1):
        if suffix_parts[-size:] == rest[:size]:
            overlap = size
            break
    merged_parts = suffix_parts + rest[overlap:]
    return f"{prefix}:{'.'.join(merged_parts)}"


def _extract_json_blocks(text: str) -> list[dict[str, Any]]:
    blocks: list[dict[str, Any]] = []
    lines = text.splitlines()
    index = 0
    while index < len(lines):
        if lines[index].strip() != "```json":
            index += 1
            continue
        index += 1
        block_lines: list[str] = []
        while index < len(lines) and lines[index].strip() != "```":
            block_lines.append(lines[index])
            index += 1
        if index < len(lines):
            index += 1
        try:
            payload = json.loads("\n".join(block_lines))
        except json.JSONDecodeError:
            continue
        if isinstance(payload, dict):
            blocks.append(payload)
    return blocks


def _extract_lock_contract(*, text: str, target_arc: str, target_path: str) -> dict[str, Any]:
    for payload in _extract_json_blocks(text):
        if payload.get("target_arc") == target_arc and payload.get("target_path") == target_path:
            return payload
    raise ValueError(f"{target_arc} lock contract block is missing from source set")


def _extract_v45_path_rows(*, text: str) -> dict[str, str]:
    rows: dict[str, str] = {}
    lines = text.splitlines()
    table_header = "| Path | Theme | Primary output | Status |"
    in_table = False
    for line in lines:
        if line.strip() == table_header:
            in_table = True
            continue
        if not in_table:
            continue
        stripped = line.strip()
        if not stripped.startswith("|"):
            break
        if stripped.startswith("|---"):
            continue
        cells = [cell.strip() for cell in stripped.strip("|").split("|")]
        if len(cells) != 4:
            continue
        path = cells[0].strip("`")
        status = cells[3]
        if path.startswith("V45-"):
            rows[path] = status
    if not rows:
        raise ValueError("V45 path ladder rows are missing from planning source")
    return rows


def _extract_selected_v45_path(*, text: str) -> str:
    candidates: set[str] = set()

    phrase_match = re.search(
        r"select\s+`(?P<path>V45-[A-Z])`\s+as the next default candidate",
        text,
    )
    if phrase_match is not None:
        candidates.add(phrase_match.group("path"))

    branch_path_match = re.search(
        r"Recommended next path for this branch:\s*\n\s*-\s*`(?P<path>V45-[A-Z])`",
        text,
    )
    if branch_path_match is not None:
        candidates.add(branch_path_match.group("path"))

    section_match = re.search(
        r"^## Recommended Next Path \(`(?P<path>V45-[A-Z])`\)$",
        text,
        flags=re.MULTILINE,
    )
    if section_match is not None:
        candidates.add(section_match.group("path"))

    try:
        path_rows = _extract_v45_path_rows(text=text)
    except ValueError:
        path_rows = {}
    selected_table_paths = sorted(
        path for path, status in path_rows.items() if status == "selected_next_branch_local"
    )
    candidates.update(selected_table_paths)

    if not candidates:
        raise ValueError("branch-local V45 default selection markers are missing")
    if len(candidates) != 1:
        raise ValueError(
            "branch-local V45 default selection markers must agree on one selected path"
        )
    return next(iter(candidates))


def _extract_v45c_corrective_selected_path(*, text: str) -> str:
    corrective_match = re.search(
        (
            r"select\s+`(?P<path>V45-[A-Z])`\s+as the next default "
            r"candidate\s+for\s+that bounded corrective follow-up"
        ),
        text,
        flags=re.MULTILINE,
    )
    if corrective_match is None:
        raise ValueError("bounded V45-C corrective selection marker is missing")
    return corrective_match.group("path")


def _validate_v45c_corrective_planning_markers(*, text: str) -> str:
    path_rows = _extract_v45_path_rows(text=text)
    selected_table_paths = sorted(
        path for path, status in path_rows.items() if status == "selected_next_branch_local"
    )
    if selected_table_paths != ["V45-B"]:
        raise ValueError(
            "v45c corrective extractor requires V45-B to remain the broader "
            "selected_next_branch_local path in planning"
        )
    return _extract_v45c_corrective_selected_path(text=text)


def derive_v45a_repo_schema_family_registry(
    *,
    source_paths: list[str] | None = None,
    snapshot_validity_posture: str = "snapshot_bound_current",
) -> dict[str, Any]:
    root = repo_root(anchor=Path(__file__))
    normalized_source_paths = source_paths if source_paths is not None else _default_source_paths()
    normalized_source_paths = sorted(
        {_assert_repo_rel_path(path, field_name="source_paths") for path in normalized_source_paths}
    )
    if not normalized_source_paths:
        raise ValueError("source_paths must not be empty")

    source_files: list[dict[str, Any]] = []
    schema_entries: list[dict[str, Any]] = []
    evidence_refs_by_id: dict[str, RepoDescriptionEvidenceRef] = {}
    schema_by_key: dict[str, dict[str, Any]] = {}

    for source_path in normalized_source_paths:
        absolute_path = root / source_path
        if not absolute_path.is_file():
            raise FileNotFoundError(f"source path does not exist: {source_path}")
        raw_payload = json.loads(absolute_path.read_text(encoding="utf-8"))
        if not isinstance(raw_payload, dict):
            raise ValueError(f"source schema must be a json object: {source_path}")
        source_hash = sha256_canonical_json(raw_payload)
        source_files.append({"source_path": source_path, "source_hash": source_hash})

        schema_discriminator = _schema_discriminator(raw_payload, fallback_path=source_path)
        schema_key = _schema_key(schema_discriminator, schema_path=source_path)
        if schema_key in schema_by_key:
            raise ValueError(f"duplicate schema_key in source set: {schema_key}")
        schema_by_key[schema_key] = raw_payload

        family_cluster = _family_cluster(schema_key)
        primary_carrier_class = _primary_carrier_class(schema_key)
        lineage_overlay = _lineage_overlay(family_cluster)
        classification_method = _classification_method(
            raw_payload, schema_discriminator=schema_discriminator
        )
        classification_posture = _classification_posture(classification_method)

        base_evidence_id = f"evidence:{schema_key}"
        row_evidence: list[RepoDescriptionEvidenceRef] = [
            RepoDescriptionEvidenceRef(
                evidence_ref=f"{base_evidence_id}:anchor",
                evidence_kind="observed_anchor_tuple_evidence",
            ),
            RepoDescriptionEvidenceRef(
                evidence_ref=f"{base_evidence_id}:lexical",
                evidence_kind="lexical_cue_evidence",
            ),
        ]
        if classification_method == "structural_signature":
            row_evidence.append(
                RepoDescriptionEvidenceRef(
                    evidence_ref=f"{base_evidence_id}:structural",
                    evidence_kind="structural_signature_evidence",
                )
            )
        if classification_method != "lexical_naming" and any(
            token in schema_key for token in ("request", "report", "result", "registry")
        ):
            row_evidence.append(
                RepoDescriptionEvidenceRef(
                    evidence_ref=f"{base_evidence_id}:semantic",
                    evidence_kind="semantic_function_cue_evidence",
                )
            )
        if classification_method != "lexical_naming" and any(
            token in schema_key for token in ("contract", "policy")
        ):
            row_evidence.append(
                RepoDescriptionEvidenceRef(
                    evidence_ref=f"{base_evidence_id}:governance",
                    evidence_kind="governance_cue_evidence",
                )
            )
        for evidence in row_evidence:
            evidence_refs_by_id[evidence.evidence_ref] = evidence

        schema_entries.append(
            {
                "schema_key": schema_key,
                "schema_path": source_path,
                "schema_discriminator": schema_discriminator,
                "family_cluster": family_cluster,
                "primary_carrier_class": primary_carrier_class,
                "secondary_role_form_tags": _secondary_role_form_tags(schema_key),
                "lineage_overlay": lineage_overlay,
                "core_envelope_features": _core_envelope_features(raw_payload),
                "residual_flags": _residual_flags(raw_payload),
                "classification_posture": classification_posture,
                "classification_method": classification_method,
                "adjudicator_ref": None,
                "supporting_evidence_refs": sorted(
                    evidence.evidence_ref for evidence in row_evidence
                ),
            }
        )

    source_set_hash = sha256_canonical_json(
        {
            "source_paths": [
                entry["source_path"]
                for entry in sorted(source_files, key=lambda row: row["source_path"])
            ],
            "source_hashes": {
                entry["source_path"]: entry["source_hash"]
                for entry in sorted(source_files, key=lambda row: row["source_path"])
            },
        }
    )
    repo_snapshot_hash = source_set_hash
    repo_snapshot_id = f"repo_snapshot_{repo_snapshot_hash[:24]}"

    reconstruction_subset: list[dict[str, Any]] = []
    for schema_key in representative_schema_keys():
        payload = schema_by_key.get(schema_key)
        if payload is None:
            raise ValueError(
                f"representative reconstruction schema is missing from source set: {schema_key}"
            )
        reconstruction_evidence_ref = f"evidence:{schema_key}:reconstruction"
        evidence_refs_by_id[reconstruction_evidence_ref] = RepoDescriptionEvidenceRef(
            evidence_ref=reconstruction_evidence_ref,
            evidence_kind="reconstruction_subset_evidence",
        )
        reconstruction_subset.append(
            {
                "schema_key": schema_key,
                "source_schema_definition": payload,
                "reconstructed_schema_definition": deepcopy(payload),
                "evidence_refs": sorted(
                    {
                        reconstruction_evidence_ref,
                        f"evidence:{schema_key}:anchor",
                    }
                ),
            }
        )

    payload_without_registry_id = {
        "schema": "repo_schema_family_registry@1",
        "repo_snapshot_id": repo_snapshot_id,
        "repo_snapshot_hash": repo_snapshot_hash,
        "snapshot_validity_posture": snapshot_validity_posture,
        "source_set": {
            "source_paths": normalized_source_paths,
            "source_set_hash": source_set_hash,
        },
        "classification_policy_ref": V45A_CLASSIFICATION_POLICY_REF,
        "classification_policy_hash": compute_v45a_classification_policy_hash(),
        "reconstruction_equivalence_mode": "canonical_normalized_semantic_equivalence",
        "schema_entries": sorted(schema_entries, key=lambda row: row["schema_key"]),
        "reconstruction_subset": sorted(reconstruction_subset, key=lambda row: row["schema_key"]),
        "evidence_refs": [
            evidence_refs_by_id[key].model_dump(mode="json") for key in sorted(evidence_refs_by_id)
        ],
    }
    return materialize_repo_schema_family_registry_payload(payload_without_registry_id)


def derive_v45a_repo_entity_catalog(
    *,
    schema_family_registry: dict[str, Any],
) -> dict[str, Any]:
    registry = RepoSchemaFamilyRegistry.model_validate(schema_family_registry)
    evidence_refs = [
        RepoDescriptionEvidenceRef.model_validate(entry).model_dump(mode="json")
        for entry in registry.evidence_refs
    ]
    entries = []
    derivation_posture_map = {
        "observed": "observed",
        "derived_deterministically": "derived",
        "inferred_heuristically": "inferred",
        "adjudicated": "adjudicated",
        "settled": "settled",
    }
    for schema_entry in registry.schema_entries:
        entries.append(
            {
                "entity_ref": f"schema:{schema_entry.schema_key}",
                "surface_kind": "schema",
                "semantic_role": _semantic_role_for_carrier(schema_entry.primary_carrier_class),
                "governance_posture": "descriptive_registry_row",
                "derivation_posture": derivation_posture_map[schema_entry.classification_posture],
                "mutation_posture": "read_only_descriptive",
                "classification_posture": schema_entry.classification_posture,
                "classification_method": schema_entry.classification_method,
                "adjudicator_ref": schema_entry.adjudicator_ref,
                "supporting_evidence_refs": schema_entry.supporting_evidence_refs,
            }
        )
    payload_without_catalog_id = {
        "schema": "repo_entity_catalog@1",
        "repo_snapshot_id": registry.repo_snapshot_id,
        "repo_snapshot_hash": registry.repo_snapshot_hash,
        "snapshot_validity_posture": registry.snapshot_validity_posture,
        "catalog_scope": "schema-visible-entity-catalog-over-bounded-repo-snapshot",
        "entity_coverage_mode": SCHEMA_VISIBLE_ENTITY_COVERAGE_MODE,
        "classification_policy_ref": registry.classification_policy_ref,
        "classification_policy_hash": registry.classification_policy_hash,
        "entities": sorted(entries, key=lambda row: row["entity_ref"]),
        "evidence_refs": evidence_refs,
    }
    return materialize_repo_entity_catalog_payload(payload_without_catalog_id)


def derive_v45a_repo_description_bundle(
    *,
    source_paths: list[str] | None = None,
    snapshot_validity_posture: str = "snapshot_bound_current",
) -> tuple[dict[str, Any], dict[str, Any]]:
    registry = derive_v45a_repo_schema_family_registry(
        source_paths=source_paths,
        snapshot_validity_posture=snapshot_validity_posture,
    )
    catalog = derive_v45a_repo_entity_catalog(schema_family_registry=registry)
    return registry, catalog


def _collect_v45b_symbol_entries(
    *,
    tree: ast.Module,
    source_path: str,
) -> tuple[list[dict[str, Any]], list[tuple[str, ast.ClassDef]]]:
    entries: list[dict[str, Any]] = []
    class_nodes: list[tuple[str, ast.ClassDef]] = []
    seen_symbol_ids: set[str] = set()
    evidence_ref = f"evidence:source:{source_path}"

    def add_symbol(*, qualname: str, symbol_kind: str, method: str) -> None:
        symbol_id = compute_symbol_id(
            module_path=source_path,
            qualname=qualname,
            symbol_kind=symbol_kind,
        )
        if symbol_id in seen_symbol_ids:
            return
        seen_symbol_ids.add(symbol_id)
        entries.append(
            {
                "symbol_id": symbol_id,
                "module_path": source_path,
                "qualname": qualname,
                "symbol_kind": symbol_kind,
                "role_classification_posture": "derived_deterministically",
                "role_classification_method": method,
                "source_artifact_refs": [source_path],
                "supporting_evidence_refs": [evidence_ref],
            }
        )

    add_symbol(qualname="__module__", symbol_kind="module", method="ast_signature")

    def visit_body(body: list[ast.stmt], *, parent_qualname: str | None = None) -> None:
        for node in body:
            if isinstance(node, ast.ClassDef):
                qualname = _qualname_join(parent_qualname, node.name)
                add_symbol(
                    qualname=qualname,
                    symbol_kind="class",
                    method=_symbol_role_method_for_node(node),
                )
                class_nodes.append((qualname, node))
                visit_body(node.body, parent_qualname=qualname)
                continue
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                qualname = _qualname_join(parent_qualname, node.name)
                add_symbol(
                    qualname=qualname,
                    symbol_kind="method" if parent_qualname else "function",
                    method=_symbol_role_method_for_node(node),
                )
                continue
            if isinstance(node, (ast.Assign, ast.AnnAssign)):
                for name in _assignment_target_names(node):
                    qualname = _qualname_join(parent_qualname, name)
                    add_symbol(qualname=qualname, symbol_kind="attribute", method="ast_signature")
            for nested_body in _nested_statement_bodies(node):
                visit_body(nested_body, parent_qualname=parent_qualname)

    visit_body(tree.body)
    return sorted(entries, key=lambda row: row["symbol_id"]), class_nodes


def _build_v45b_top_level_symbol_index(
    *,
    symbol_entries: list[dict[str, Any]],
) -> dict[str, dict[str, str]]:
    index: dict[str, dict[str, str]] = {}
    for entry in symbol_entries:
        qualname = entry["qualname"]
        if qualname == "__module__" or "." in qualname:
            continue
        module_import_path = _module_import_path_for_source_path(entry["module_path"])
        index.setdefault(module_import_path, {})[qualname] = entry["symbol_id"]
    return index


def _module_endpoint_info(
    *,
    module_import_path: str,
    module_to_source_path: dict[str, str],
) -> tuple[str, str, str]:
    source_path = _source_path_for_module_import_path(
        module_import_path=module_import_path,
        module_to_source_path=module_to_source_path,
    )
    if source_path is not None:
        return (
            "internal_module_boundary",
            compute_internal_module_boundary_ref(module_path=source_path),
            "internal_resolved",
        )
    posture, ref = _classify_external_target(module_import_path)
    return "external_dependency", ref, posture


def _symbol_endpoint_info(
    *,
    module_import_path: str,
    symbol_name: str,
    top_level_symbol_index: dict[str, dict[str, str]],
    module_to_source_path: dict[str, str],
) -> tuple[str, str, str]:
    internal_symbols = top_level_symbol_index.get(module_import_path, {})
    symbol_id = internal_symbols.get(symbol_name)
    if symbol_id is not None:
        return "internal_symbol", symbol_id, "internal_resolved"
    return _module_endpoint_info(
        module_import_path=module_import_path,
        module_to_source_path=module_to_source_path,
    )


def _resolve_dotted_dependency_target(
    *,
    dotted_name: str,
    current_module_import_path: str,
    alias_map: dict[str, tuple[str, str, str]],
    top_level_symbol_index: dict[str, dict[str, str]],
    module_to_source_path: dict[str, str],
) -> tuple[str, str, str]:
    if dotted_name in top_level_symbol_index.get(current_module_import_path, {}):
        return (
            "internal_symbol",
            top_level_symbol_index[current_module_import_path][dotted_name],
            "internal_resolved",
        )
    root, *rest = dotted_name.split(".")
    if root in alias_map:
        endpoint_kind, endpoint_ref, dependency_posture = alias_map[root]
        if endpoint_kind == "internal_symbol" or not rest:
            return endpoint_kind, endpoint_ref, dependency_posture
        if endpoint_kind == "internal_module_boundary":
            module_path = endpoint_ref[len("module:") :]
            target_module = _module_import_path_for_source_path(module_path)
            internal_symbols = top_level_symbol_index.get(target_module, {})
            candidate = internal_symbols.get(rest[0])
            if candidate is not None:
                return "internal_symbol", candidate, "internal_resolved"
            return endpoint_kind, endpoint_ref, dependency_posture
        return (
            "external_dependency",
            _merge_external_dependency_suffix(endpoint_ref=endpoint_ref, rest=rest),
            dependency_posture,
        )
    return _symbol_endpoint_info(
        module_import_path=current_module_import_path,
        symbol_name=dotted_name,
        top_level_symbol_index=top_level_symbol_index,
        module_to_source_path=module_to_source_path,
    )


def derive_v45b_repo_symbol_catalog_and_dependency_graph(
    *,
    source_paths: list[str] | None = None,
    snapshot_validity_posture: str = "snapshot_bound_current",
) -> tuple[dict[str, Any], dict[str, Any]]:
    root = repo_root(anchor=Path(__file__))
    normalized_source_paths = (
        source_paths if source_paths is not None else list(_DEFAULT_V45B_SOURCE_PATHS)
    )
    normalized_source_paths = sorted(
        {_assert_repo_rel_path(path, field_name="source_paths") for path in normalized_source_paths}
    )
    if not normalized_source_paths:
        raise ValueError("source_paths must not be empty")

    source_hashes: dict[str, str] = {}
    parsed_modules: dict[str, dict[str, Any]] = {}
    module_to_source_path: dict[str, str] = {}
    evidence_refs_by_id: dict[str, RepoDescriptionEvidenceRef] = {}

    for source_path in normalized_source_paths:
        absolute_path = root / source_path
        if not absolute_path.is_file():
            raise FileNotFoundError(f"source path does not exist: {source_path}")
        text = absolute_path.read_text(encoding="utf-8")
        source_hashes[source_path] = sha256_canonical_json({"text": text})
        tree = ast.parse(text, filename=source_path)
        module_import_path = _module_import_path_for_source_path(source_path)
        existing_source_path = module_to_source_path.get(module_import_path)
        if existing_source_path is not None and existing_source_path != source_path:
            raise ValueError(
                "source_paths must not normalize to duplicate module import paths: "
                f"{module_import_path}"
            )
        parsed_modules[source_path] = {
            "tree": tree,
            "module_import_path": module_import_path,
            "text": text,
        }
        module_to_source_path[module_import_path] = source_path
        evidence_ref = f"evidence:source:{source_path}"
        evidence_refs_by_id[evidence_ref] = RepoDescriptionEvidenceRef(
            evidence_ref=evidence_ref,
            evidence_kind="structural_signature_evidence",
        )

    source_set_hash = sha256_canonical_json(
        {
            "source_paths": normalized_source_paths,
            "source_hashes": {path: source_hashes[path] for path in normalized_source_paths},
        }
    )
    repo_snapshot_hash = source_set_hash
    repo_snapshot_id = f"repo_snapshot_{repo_snapshot_hash[:24]}"
    graph_scope = (
        "v45b-bounded-python-symbol-catalog-and-dependency-graph-over-adeu_repo_description"
    )

    symbol_entries: list[dict[str, Any]] = []
    class_nodes_by_source: dict[str, list[tuple[str, ast.ClassDef]]] = {}
    for source_path in normalized_source_paths:
        entries, class_nodes = _collect_v45b_symbol_entries(
            tree=parsed_modules[source_path]["tree"],
            source_path=source_path,
        )
        symbol_entries.extend(entries)
        class_nodes_by_source[source_path] = class_nodes

    symbol_entries = sorted(symbol_entries, key=lambda row: row["symbol_id"])
    top_level_symbol_index = _build_v45b_top_level_symbol_index(symbol_entries=symbol_entries)

    dependency_edges: list[dict[str, Any]] = []
    seen_edge_ids: set[str] = set()
    for source_path in normalized_source_paths:
        module_import_path = parsed_modules[source_path]["module_import_path"]
        tree = parsed_modules[source_path]["tree"]
        module_boundary_ref = compute_internal_module_boundary_ref(module_path=source_path)
        evidence_ref = f"evidence:source:{source_path}"
        alias_map: dict[str, tuple[str, str, str]] = {}

        def visit_dependency_body(body: list[ast.stmt]) -> None:
            for node in body:
                if isinstance(node, ast.Import):
                    for alias in sorted(node.names, key=lambda item: item.asname or item.name):
                        endpoint_kind, endpoint_ref, dependency_posture = _module_endpoint_info(
                            module_import_path=alias.name,
                            module_to_source_path=module_to_source_path,
                        )
                        local_name = alias.asname or alias.name.split(".", 1)[0]
                        alias_map[local_name] = (endpoint_kind, endpoint_ref, dependency_posture)
                        payload = {
                            "from_ref_kind": "internal_module_boundary",
                            "from_ref": module_boundary_ref,
                            "to_ref_kind": endpoint_kind,
                            "to_ref": endpoint_ref,
                            "dependency_kind": "module_import",
                            "dependency_posture": dependency_posture,
                            "derivation_posture": "derived_deterministically",
                            "derivation_method": "ast_parse",
                            "source_artifact_refs": [source_path],
                            "supporting_evidence_refs": [evidence_ref],
                        }
                        edge_id = _edge_id_for_payload(payload)
                        if edge_id not in seen_edge_ids:
                            seen_edge_ids.add(edge_id)
                            dependency_edges.append({"edge_id": edge_id, **payload})
                elif isinstance(node, ast.ImportFrom):
                    resolved_module = _resolve_import_from_module(
                        source_path=source_path,
                        module=node.module,
                        level=node.level,
                    )
                    if resolved_module == "__future__":
                        continue
                    for alias in sorted(node.names, key=lambda item: item.asname or item.name):
                        local_name = alias.asname or alias.name
                        if node.module is None and alias.name != "*":
                            candidate_module = (
                                f"{resolved_module}.{alias.name}" if resolved_module else alias.name
                            )
                            if candidate_module in module_to_source_path:
                                endpoint_kind, endpoint_ref, dependency_posture = (
                                    _module_endpoint_info(
                                        module_import_path=candidate_module,
                                        module_to_source_path=module_to_source_path,
                                    )
                                )
                                dependency_kind = "module_import"
                            else:
                                endpoint_kind, endpoint_ref, dependency_posture = (
                                    _symbol_endpoint_info(
                                        module_import_path=resolved_module,
                                        symbol_name=alias.name,
                                        top_level_symbol_index=top_level_symbol_index,
                                        module_to_source_path=module_to_source_path,
                                    )
                                )
                                dependency_kind = "symbol_reference"
                        elif alias.name == "*":
                            endpoint_kind, endpoint_ref, dependency_posture = _module_endpoint_info(
                                module_import_path=resolved_module,
                                module_to_source_path=module_to_source_path,
                            )
                            dependency_kind = "module_import"
                        else:
                            endpoint_kind, endpoint_ref, dependency_posture = _symbol_endpoint_info(
                                module_import_path=resolved_module,
                                symbol_name=alias.name,
                                top_level_symbol_index=top_level_symbol_index,
                                module_to_source_path=module_to_source_path,
                            )
                            dependency_kind = "symbol_reference"
                        alias_map[local_name] = (endpoint_kind, endpoint_ref, dependency_posture)
                        payload = {
                            "from_ref_kind": "internal_module_boundary",
                            "from_ref": module_boundary_ref,
                            "to_ref_kind": endpoint_kind,
                            "to_ref": endpoint_ref,
                            "dependency_kind": dependency_kind,
                            "dependency_posture": dependency_posture,
                            "derivation_posture": "derived_deterministically",
                            "derivation_method": "ast_parse",
                            "source_artifact_refs": [source_path],
                            "supporting_evidence_refs": [evidence_ref],
                        }
                        edge_id = _edge_id_for_payload(payload)
                        if edge_id not in seen_edge_ids:
                            seen_edge_ids.add(edge_id)
                            dependency_edges.append({"edge_id": edge_id, **payload})
                for nested_body in _nested_statement_bodies(node):
                    visit_dependency_body(nested_body)

        visit_dependency_body(tree.body)

        for class_qualname, class_node in class_nodes_by_source[source_path]:
            from_ref = compute_symbol_id(
                module_path=source_path,
                qualname=class_qualname,
                symbol_kind="class",
            )
            for base in class_node.bases:
                dotted = _expr_to_dotted_name(base)
                if dotted is None:
                    continue
                endpoint_kind, endpoint_ref, dependency_posture = _resolve_dotted_dependency_target(
                    dotted_name=dotted,
                    current_module_import_path=module_import_path,
                    alias_map=alias_map,
                    top_level_symbol_index=top_level_symbol_index,
                    module_to_source_path=module_to_source_path,
                )
                payload = {
                    "from_ref_kind": "internal_symbol",
                    "from_ref": from_ref,
                    "to_ref_kind": endpoint_kind,
                    "to_ref": endpoint_ref,
                    "dependency_kind": "inheritance",
                    "dependency_posture": dependency_posture,
                    "derivation_posture": "derived_deterministically",
                    "derivation_method": "ast_parse",
                    "source_artifact_refs": [source_path],
                    "supporting_evidence_refs": [evidence_ref],
                }
                edge_id = _edge_id_for_payload(payload)
                if edge_id not in seen_edge_ids:
                    seen_edge_ids.add(edge_id)
                    dependency_edges.append({"edge_id": edge_id, **payload})

    symbol_catalog = materialize_repo_symbol_catalog_payload(
        {
            "schema": REPO_SYMBOL_CATALOG_SCHEMA,
            "repo_snapshot_id": repo_snapshot_id,
            "repo_snapshot_hash": repo_snapshot_hash,
            "snapshot_validity_posture": snapshot_validity_posture,
            "source_set": normalized_source_paths,
            "source_set_hash": source_set_hash,
            "graph_scope": graph_scope,
            "extraction_posture": "derived_deterministically",
            "extraction_method": "ast_parse",
            "symbol_entries": symbol_entries,
            "evidence_refs": [
                evidence_refs_by_id[key].model_dump(mode="json")
                for key in sorted(evidence_refs_by_id)
            ],
        }
    )
    dependency_graph = materialize_repo_dependency_graph_payload(
        {
            "schema": REPO_DEPENDENCY_GRAPH_SCHEMA,
            "repo_snapshot_id": repo_snapshot_id,
            "repo_snapshot_hash": repo_snapshot_hash,
            "snapshot_validity_posture": snapshot_validity_posture,
            "source_set": normalized_source_paths,
            "source_set_hash": source_set_hash,
            "graph_scope": graph_scope,
            "extraction_posture": "derived_deterministically",
            "extraction_method": "ast_parse",
            "dependency_edges": sorted(dependency_edges, key=lambda row: row["edge_id"]),
            "evidence_refs": [
                evidence_refs_by_id[key].model_dump(mode="json")
                for key in sorted(evidence_refs_by_id)
            ],
        }
    )
    validate_repo_symbol_catalog_dependency_graph_pair(
        symbol_catalog_payload=symbol_catalog,
        dependency_graph_payload=dependency_graph,
    )
    return symbol_catalog, dependency_graph


def derive_v45b_repo_symbol_catalog(
    *,
    source_paths: list[str] | None = None,
    snapshot_validity_posture: str = "snapshot_bound_current",
) -> dict[str, Any]:
    symbol_catalog, _dependency_graph = derive_v45b_repo_symbol_catalog_and_dependency_graph(
        source_paths=source_paths,
        snapshot_validity_posture=snapshot_validity_posture,
    )
    return symbol_catalog


def derive_v45b_repo_dependency_graph(
    *,
    source_paths: list[str] | None = None,
    snapshot_validity_posture: str = "snapshot_bound_current",
) -> dict[str, Any]:
    _symbol_catalog, dependency_graph = derive_v45b_repo_symbol_catalog_and_dependency_graph(
        source_paths=source_paths,
        snapshot_validity_posture=snapshot_validity_posture,
    )
    return dependency_graph


def derive_v45c_repo_arc_dependency_register(
    *,
    source_paths: list[str] | None = None,
    snapshot_validity_posture: str = "snapshot_bound_current",
) -> dict[str, Any]:
    root = repo_root(anchor=Path(__file__))
    normalized_source_paths = (
        source_paths if source_paths is not None else list(_DEFAULT_V45C_SOURCE_PATHS)
    )
    normalized_source_paths = sorted(
        {_assert_repo_rel_path(path, field_name="source_paths") for path in normalized_source_paths}
    )
    if not normalized_source_paths:
        raise ValueError("source_paths must not be empty")

    source_hashes: dict[str, str] = {}
    options_text: str | None = None
    lock_text: str | None = None
    lock102_text: str | None = None
    for source_path in normalized_source_paths:
        absolute_path = root / source_path
        if not absolute_path.is_file():
            raise FileNotFoundError(f"source path does not exist: {source_path}")
        text = absolute_path.read_text(encoding="utf-8")
        source_hashes[source_path] = sha256_canonical_json({"text": text})
        filename = Path(source_path).name
        if filename == "DRAFT_NEXT_ARC_OPTIONS_v28.md":
            options_text = text
        elif filename == "LOCKED_CONTINUATION_vNEXT_PLUS100.md":
            if lock_text is not None:
                raise ValueError("duplicate v100 lock source provided")
            lock_text = text
        elif filename == "LOCKED_CONTINUATION_vNEXT_PLUS102.md":
            if lock102_text is not None:
                raise ValueError("duplicate v102 lock source provided")
            lock102_text = text

    if options_text is None:
        raise ValueError("source_paths must include docs/DRAFT_NEXT_ARC_OPTIONS_v28.md")
    if lock_text is None:
        raise ValueError("source_paths must include docs/LOCKED_CONTINUATION_vNEXT_PLUS100.md")
    if lock102_text is None:
        raise ValueError("source_paths must include docs/LOCKED_CONTINUATION_vNEXT_PLUS102.md")

    path_rows = _extract_v45_path_rows(text=options_text)
    corrective_selected_path = _validate_v45c_corrective_planning_markers(text=options_text)
    lock_contract_v100 = _extract_lock_contract(
        text=lock_text,
        target_arc="vNext+100",
        target_path="V45-C",
    )
    lock_contract_v102 = _extract_lock_contract(
        text=lock102_text,
        target_arc="vNext+102",
        target_path="V45-C",
    )
    selected_path = lock_contract_v102["target_path"]
    if corrective_selected_path != selected_path:
        raise ValueError("planning corrective V45 path must match the v102 lock target path")

    source_set_hash = sha256_canonical_json(
        {
            "source_paths": normalized_source_paths,
            "source_hashes": {path: source_hashes[path] for path in normalized_source_paths},
        }
    )
    repo_snapshot_hash = source_set_hash
    repo_snapshot_id = f"repo_snapshot_{repo_snapshot_hash[:24]}"

    evidence_refs_by_id: dict[str, RepoDescriptionEvidenceRef] = {}
    for path in sorted(path_rows):
        evidence_ref = f"evidence:planning:v28:row:{path}"
        evidence_refs_by_id[evidence_ref] = RepoDescriptionEvidenceRef(
            evidence_ref=evidence_ref,
            evidence_kind="planning_table_row_evidence",
        )
    evidence_refs_by_id["evidence:planning:v28:corrective_selection"] = RepoDescriptionEvidenceRef(
        evidence_ref="evidence:planning:v28:corrective_selection",
        evidence_kind="planning_selection_evidence",
    )
    evidence_refs_by_id["evidence:lock:v100:contract"] = RepoDescriptionEvidenceRef(
        evidence_ref="evidence:lock:v100:contract",
        evidence_kind="lock_contract_evidence",
    )
    evidence_refs_by_id["evidence:policy:v45c"] = RepoDescriptionEvidenceRef(
        evidence_ref="evidence:policy:v45c",
        evidence_kind="dependency_policy_evidence",
    )
    evidence_refs_by_id["evidence:lock:v102:contract"] = RepoDescriptionEvidenceRef(
        evidence_ref="evidence:lock:v102:contract",
        evidence_kind="lock_contract_evidence",
    )

    dependency_map: dict[str, list[str]] = {
        "V45-F": ["V45-B", "V45-C", "V45-D", "V45-E"],
    }
    tracked_paths = ("V45-B", "V45-C", "V45-D", "V45-E", "V45-F")
    missing_paths = [path for path in tracked_paths if path not in path_rows]
    if missing_paths:
        raise ValueError(f"planning source is missing tracked V45 paths: {missing_paths}")

    open_arc_entries: list[dict[str, Any]] = []
    for path in tracked_paths:
        blocked_by = sorted(dependency_map.get(path, []))
        if path == selected_path:
            phase_status = "locked_start_bundle"
            authority_layer = "lock"
        else:
            phase_status = path_rows[path]
            authority_layer = "planning"
        open_arc_entries.append(
            {
                "arc_id": path,
                "family_path": path,
                "phase_status": phase_status,
                "authority_layer": authority_layer,
                "readiness_posture": "blocked" if blocked_by else "ready",
                "blocker_arc_ids": blocked_by,
                "blocked_by_arc_ids": blocked_by,
                "derivation_posture": "derived_deterministically",
                "derivation_method": "deterministic_projection",
                "source_artifact_refs": sorted(
                    {
                        "docs/DRAFT_NEXT_ARC_OPTIONS_v28.md",
                        *(
                            {
                                "docs/LOCKED_CONTINUATION_vNEXT_PLUS100.md",
                                "docs/LOCKED_CONTINUATION_vNEXT_PLUS102.md",
                            }
                            if path == selected_path
                            else set()
                        ),
                    }
                ),
                "supporting_evidence_refs": sorted(
                    {
                        f"evidence:planning:v28:row:{path}",
                        (
                            "evidence:planning:v28:corrective_selection"
                            if path == selected_path
                            else f"evidence:planning:v28:row:{path}"
                        ),
                        (
                            "evidence:lock:v102:contract"
                            if path == selected_path
                            else f"evidence:planning:v28:row:{path}"
                        ),
                        (
                            "evidence:lock:v100:contract"
                            if path == selected_path
                            else f"evidence:planning:v28:row:{path}"
                        ),
                    }
                ),
            }
        )

    dependency_edges: list[dict[str, Any]] = []
    for to_arc_id, from_arc_ids in sorted(dependency_map.items()):
        for from_arc_id in sorted(from_arc_ids):
            dependency_edges.append(
                {
                    "edge_id": f"edge:{from_arc_id.lower()}-to-{to_arc_id.lower()}",
                    "from_arc_id": from_arc_id,
                    "to_arc_id": to_arc_id,
                    "dependency_kind": "descriptive_prerequisite"
                    if to_arc_id == "V45-F"
                    else "family_progression",
                    "dependency_strength": "hard",
                    "dependency_status": "unresolved",
                    "derivation_posture": "derived_deterministically",
                    "derivation_method": "deterministic_projection",
                    "source_artifact_refs": ["docs/DRAFT_NEXT_ARC_OPTIONS_v28.md"],
                    "supporting_evidence_refs": sorted(
                        {
                            f"evidence:planning:v28:row:{from_arc_id}",
                            f"evidence:planning:v28:row:{to_arc_id}",
                            "evidence:policy:v45c",
                        }
                    ),
                }
            )

    payload_without_register_id = {
        "schema": "repo_arc_dependency_register@2",
        "repo_snapshot_id": repo_snapshot_id,
        "repo_snapshot_hash": repo_snapshot_hash,
        "snapshot_validity_posture": snapshot_validity_posture,
        "source_set": normalized_source_paths,
        "source_set_hash": source_set_hash,
        "register_scope": (
            "v45-open-arc-dependency-register-corrective-hardening-over-branch-local-selection"
        ),
        "pending_list_posture": "machine_enforced_open_arc_register",
        "cycle_posture": "cycles_forbidden",
        "cycle_detection_scope": "all_declared_edges",
        "dependency_policy_ref": V45C_DEPENDENCY_POLICY_REF,
        "dependency_policy_hash": compute_v45c_v102_dependency_policy_hash(),
        "extraction_posture": "derived_deterministically",
        "extraction_method": "deterministic_projection",
        "open_arc_entries": sorted(open_arc_entries, key=lambda row: row["arc_id"]),
        "dependency_edges": sorted(dependency_edges, key=lambda row: row["edge_id"]),
        "evidence_refs": [
            evidence_refs_by_id[key].model_dump(mode="json") for key in sorted(evidence_refs_by_id)
        ],
    }
    if lock_contract_v100.get("target_path") != selected_path:
        raise ValueError("released v100 and corrective v102 lock target paths must agree")
    return materialize_repo_arc_dependency_register_payload(payload_without_register_id)


def derive_v45d_repo_test_intent_matrix(
    *,
    source_paths: list[str] | None = None,
    bound_symbol_catalog_payload: dict[str, Any] | None = None,
    bound_dependency_graph_payload: dict[str, Any] | None = None,
    snapshot_validity_posture: str | None = None,
) -> dict[str, Any]:
    root = repo_root(anchor=Path(__file__))
    normalized_source_paths = (
        source_paths if source_paths is not None else _default_v45d_source_paths()
    )
    normalized_source_paths = sorted(
        {_assert_repo_rel_path(path, field_name="source_paths") for path in normalized_source_paths}
    )
    if not normalized_source_paths:
        raise ValueError("source_paths must not be empty")

    if bound_symbol_catalog_payload is None or bound_dependency_graph_payload is None:
        (
            derived_symbol_catalog,
            derived_dependency_graph,
        ) = derive_v45b_repo_symbol_catalog_and_dependency_graph(
            source_paths=default_v45b_source_paths(),
            snapshot_validity_posture="snapshot_bound_current",
        )
        bound_symbol_catalog_payload = (
            derived_symbol_catalog
            if bound_symbol_catalog_payload is None
            else bound_symbol_catalog_payload
        )
        bound_dependency_graph_payload = (
            derived_dependency_graph
            if bound_dependency_graph_payload is None
            else bound_dependency_graph_payload
        )

    (
        bound_symbol_catalog,
        bound_dependency_graph,
    ) = validate_repo_symbol_catalog_dependency_graph_pair(
        symbol_catalog_payload=bound_symbol_catalog_payload,
        dependency_graph_payload=bound_dependency_graph_payload,
    )
    effective_snapshot_validity_posture = (
        snapshot_validity_posture or bound_symbol_catalog.snapshot_validity_posture
    )
    if effective_snapshot_validity_posture != bound_symbol_catalog.snapshot_validity_posture:
        raise ValueError(
            "snapshot_validity_posture must match the bound V45-B snapshot_validity_posture"
        )

    source_hashes: dict[str, str] = {}
    parsed_trees: dict[str, ast.Module] = {}
    for source_path in normalized_source_paths:
        absolute_path = root / source_path
        if not absolute_path.is_file():
            raise FileNotFoundError(f"source path does not exist: {source_path}")
        text = absolute_path.read_text(encoding="utf-8")
        source_hashes[source_path] = sha256_canonical_json({"text": text})
        parsed_trees[source_path] = ast.parse(text, filename=source_path)

    test_source_set_hash = sha256_canonical_json(
        {
            "source_paths": normalized_source_paths,
            "source_hashes": {path: source_hashes[path] for path in normalized_source_paths},
        }
    )

    unique_qualname_index, module_qualname_to_symbol, source_path_to_module_import_path = (
        _bound_unique_symbol_index(symbol_catalog=bound_symbol_catalog.model_dump(mode="json"))
    )
    bound_module_to_source_path = {
        module_import_path: source_path
        for source_path, module_import_path in source_path_to_module_import_path.items()
    }

    evidence_refs_by_id: dict[str, RepoDescriptionEvidenceRef] = {}
    evidence_refs_by_id["evidence:contract:v45d:v103"] = RepoDescriptionEvidenceRef(
        evidence_ref="evidence:contract:v45d:v103",
        evidence_kind="lock_contract_evidence",
    )
    evidence_refs_by_id["evidence:bound:v45b:symbol_catalog"] = RepoDescriptionEvidenceRef(
        evidence_ref="evidence:bound:v45b:symbol_catalog",
        evidence_kind="observed_anchor_tuple_evidence",
    )
    evidence_refs_by_id["evidence:bound:v45b:dependency_graph"] = RepoDescriptionEvidenceRef(
        evidence_ref="evidence:bound:v45b:dependency_graph",
        evidence_kind="observed_anchor_tuple_evidence",
    )

    entries: list[dict[str, Any]] = []
    for source_path in normalized_source_paths:
        evidence_ref = f"evidence:test_source:{source_path}:ast"
        evidence_refs_by_id[evidence_ref] = RepoDescriptionEvidenceRef(
            evidence_ref=evidence_ref,
            evidence_kind="structural_signature_evidence",
        )
        evidence_refs_by_id[f"evidence:test_source:{source_path}:inference"] = (
            RepoDescriptionEvidenceRef(
                evidence_ref=f"evidence:test_source:{source_path}:inference",
                evidence_kind="semantic_function_cue_evidence",
            )
        )
        alias_map = _extract_test_import_aliases(
            source_path=source_path,
            tree=parsed_trees[source_path],
            unique_qualname_index=unique_qualname_index,
            module_qualname_to_symbol=module_qualname_to_symbol,
            bound_module_to_source_path=bound_module_to_source_path,
        )
        entries.extend(
            _derive_v45d_entries_for_source_path(
                source_path=source_path,
                tree=parsed_trees[source_path],
                alias_map=alias_map,
                unique_qualname_index=unique_qualname_index,
                bound_module_to_source_path=bound_module_to_source_path,
            )
        )

    payload_without_matrix_id = {
        "schema": REPO_TEST_INTENT_MATRIX_SCHEMA,
        "repo_snapshot_id": bound_symbol_catalog.repo_snapshot_id,
        "repo_snapshot_hash": bound_symbol_catalog.repo_snapshot_hash,
        "snapshot_validity_posture": effective_snapshot_validity_posture,
        "test_source_set": normalized_source_paths,
        "test_source_set_hash": test_source_set_hash,
        "bound_symbol_catalog_ref": bound_symbol_catalog.repo_symbol_catalog_id,
        "bound_dependency_graph_ref": bound_dependency_graph.repo_dependency_graph_id,
        "matrix_scope": (
            "v45d-bounded-python-test-intent-matrix-over-adeu_repo_description-tests"
        ),
        "extraction_posture": "derived_deterministically",
        "extraction_method": "bounded_inference_rule",
        "test_intent_entries": sorted(entries, key=lambda row: row["entry_id"]),
        "evidence_refs": [
            evidence_refs_by_id[key].model_dump(mode="json") for key in sorted(evidence_refs_by_id)
        ],
    }
    matrix = materialize_repo_test_intent_matrix_payload(payload_without_matrix_id)
    validate_repo_test_intent_matrix_against_v45b(
        test_intent_matrix_payload=matrix,
        symbol_catalog_payload=bound_symbol_catalog.model_dump(mode="json"),
        dependency_graph_payload=bound_dependency_graph.model_dump(mode="json"),
    )
    return matrix


def _count_symbol_entries_by_module(symbol_catalog: dict[str, Any]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for entry in symbol_catalog["symbol_entries"]:
        counts[entry["module_path"]] = counts.get(entry["module_path"], 0) + 1
    return counts


def _count_dependency_edges_by_source_path(dependency_graph: dict[str, Any]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for edge in dependency_graph["dependency_edges"]:
        for source_path in edge["source_artifact_refs"]:
            counts[source_path] = counts.get(source_path, 0) + 1
    return counts


def _guarded_surface_counts_by_module(
    *,
    test_intent_matrix: dict[str, Any],
    symbol_catalog: dict[str, Any],
) -> dict[str, int]:
    symbol_to_module = {
        entry["symbol_id"]: entry["module_path"] for entry in symbol_catalog["symbol_entries"]
    }
    counts: dict[str, int] = {}
    for entry in test_intent_matrix["test_intent_entries"]:
        guarded = entry["guarded_surface_ref"]
        kind = guarded["guarded_surface_ref_kind"]
        value = guarded["guarded_surface_ref_value"]
        if kind == "internal_symbol":
            module_path = symbol_to_module.get(value)
            if module_path is None:
                continue
        elif kind == "internal_module_boundary":
            module_path = value[len("module:") :]
        else:
            continue
        counts[module_path] = counts.get(module_path, 0) + 1
    return counts


def derive_v45e_repo_optimization_register(
    *,
    source_paths: list[str] | None = None,
    bound_entity_catalog_payload: dict[str, Any] | None = None,
    bound_schema_family_registry_payload: dict[str, Any] | None = None,
    bound_symbol_catalog_payload: dict[str, Any] | None = None,
    bound_dependency_graph_payload: dict[str, Any] | None = None,
    bound_test_intent_matrix_payload: dict[str, Any] | None = None,
    bound_arc_dependency_register_payload: dict[str, Any] | None = None,
    snapshot_validity_posture: str | None = None,
) -> dict[str, Any]:
    root = repo_root(anchor=Path(__file__))
    normalized_source_paths = (
        source_paths if source_paths is not None else _default_v45e_source_paths()
    )
    normalized_source_paths = sorted(
        {_assert_repo_rel_path(path, field_name="source_paths") for path in normalized_source_paths}
    )
    if not normalized_source_paths:
        raise ValueError("source_paths must not be empty")

    if bound_schema_family_registry_payload is None or bound_entity_catalog_payload is None:
        derived_schema_registry, derived_entity_catalog = derive_v45a_repo_description_bundle(
            snapshot_validity_posture="snapshot_bound_current"
        )
        bound_schema_family_registry_payload = (
            derived_schema_registry
            if bound_schema_family_registry_payload is None
            else bound_schema_family_registry_payload
        )
        bound_entity_catalog_payload = (
            derived_entity_catalog
            if bound_entity_catalog_payload is None
            else bound_entity_catalog_payload
        )
    if bound_symbol_catalog_payload is None or bound_dependency_graph_payload is None:
        derived_symbol_catalog, derived_dependency_graph = (
            derive_v45b_repo_symbol_catalog_and_dependency_graph(
                source_paths=default_v45b_source_paths(),
                snapshot_validity_posture="snapshot_bound_current",
            )
        )
        bound_symbol_catalog_payload = (
            derived_symbol_catalog
            if bound_symbol_catalog_payload is None
            else bound_symbol_catalog_payload
        )
        bound_dependency_graph_payload = (
            derived_dependency_graph
            if bound_dependency_graph_payload is None
            else bound_dependency_graph_payload
        )
    if bound_test_intent_matrix_payload is None:
        bound_test_intent_matrix_payload = derive_v45d_repo_test_intent_matrix(
            source_paths=default_v45d_source_paths(),
            bound_symbol_catalog_payload=bound_symbol_catalog_payload,
            bound_dependency_graph_payload=bound_dependency_graph_payload,
        )
    if bound_arc_dependency_register_payload is None:
        bound_arc_dependency_register_payload = _load_historical_v45c_v102_reference(
            root=root
        )

    effective_snapshot_validity_posture = snapshot_validity_posture or "snapshot_bound_current"

    source_hashes: dict[str, str] = {}
    source_line_counts: dict[str, int] = {}
    for source_path in normalized_source_paths:
        absolute_path = root / source_path
        if not absolute_path.is_file():
            raise FileNotFoundError(f"source path does not exist: {source_path}")
        text = absolute_path.read_text(encoding="utf-8")
        source_hashes[source_path] = sha256_canonical_json({"text": text})
        source_line_counts[source_path] = len(text.splitlines())

    source_set_hash = sha256_canonical_json(
        {
            "source_paths": normalized_source_paths,
            "source_hashes": {path: source_hashes[path] for path in normalized_source_paths},
        }
    )

    symbol_counts = _count_symbol_entries_by_module(bound_symbol_catalog_payload)
    dependency_counts = _count_dependency_edges_by_source_path(bound_dependency_graph_payload)
    guarded_surface_counts = _guarded_surface_counts_by_module(
        test_intent_matrix=bound_test_intent_matrix_payload,
        symbol_catalog=bound_symbol_catalog_payload,
    )

    evidence_refs_by_id: dict[str, RepoDescriptionEvidenceRef] = {
        "evidence:contract:v45e:v104": RepoDescriptionEvidenceRef(
            evidence_ref="evidence:contract:v45e:v104",
            evidence_kind="lock_contract_evidence",
        ),
        "evidence:bound:v45a:entity_catalog": RepoDescriptionEvidenceRef(
            evidence_ref="evidence:bound:v45a:entity_catalog",
            evidence_kind="observed_anchor_tuple_evidence",
        ),
        "evidence:bound:v45a:schema_family_registry": RepoDescriptionEvidenceRef(
            evidence_ref="evidence:bound:v45a:schema_family_registry",
            evidence_kind="observed_anchor_tuple_evidence",
        ),
        "evidence:bound:v45b:symbol_catalog": RepoDescriptionEvidenceRef(
            evidence_ref="evidence:bound:v45b:symbol_catalog",
            evidence_kind="observed_anchor_tuple_evidence",
        ),
        "evidence:bound:v45b:dependency_graph": RepoDescriptionEvidenceRef(
            evidence_ref="evidence:bound:v45b:dependency_graph",
            evidence_kind="observed_anchor_tuple_evidence",
        ),
        "evidence:bound:v45c:arc_dependency_register": RepoDescriptionEvidenceRef(
            evidence_ref="evidence:bound:v45c:arc_dependency_register",
            evidence_kind="observed_anchor_tuple_evidence",
        ),
        "evidence:bound:v45d:test_intent_matrix": RepoDescriptionEvidenceRef(
            evidence_ref="evidence:bound:v45d:test_intent_matrix",
            evidence_kind="observed_anchor_tuple_evidence",
        ),
    }
    for source_path in normalized_source_paths:
        evidence_refs_by_id[f"evidence:source:{source_path}:metrics"] = RepoDescriptionEvidenceRef(
            evidence_ref=f"evidence:source:{source_path}:metrics",
            evidence_kind="structural_signature_evidence",
        )
    evidence_refs_by_id["evidence:cluster:v45e:core_logic"] = RepoDescriptionEvidenceRef(
        evidence_ref="evidence:cluster:v45e:core_logic",
        evidence_kind="semantic_function_cue_evidence",
    )

    ranked_paths = sorted(
        normalized_source_paths,
        key=lambda path: (
            -source_line_counts.get(path, 0),
            -symbol_counts.get(path, 0),
            path,
        ),
    )
    hotspot_paths = ranked_paths[:2]
    optimization_entries: list[dict[str, Any]] = []

    for path in hotspot_paths:
        symbol_count = symbol_counts.get(path, 0)
        dependency_count = dependency_counts.get(path, 0)
        test_count = guarded_surface_counts.get(path, 0)
        payload_without_entry_id = {
            "finding_scope": {
                "finding_scope_kind": "file_surface",
                "finding_scope_ref": path,
                "cluster_member_refs": [],
            },
            "compression_axis": "surface_compression",
            "optimization_posture": "hotspot",
            "support_basis": "long_file_or_concentrated_surface",
            "secondary_compression_axes": ["governance_compression"],
            "secondary_support_basis_tags": ["test_and_dependency_concentration"],
            "descriptive_finding_summary": (
                f"{path} concentrates {source_line_counts.get(path, 0)} lines, "
                f"{symbol_count} symbols, {dependency_count} dependency edges, and "
                f"{test_count} test-intent bindings in the current repo-description baseline."
            ),
            "optimization_candidate_summary": (
                "Inspect whether bounded validation and payload-assembly responsibilities "
                "can be decomposed into smaller descriptive helper surfaces while "
                "preserving descriptive-only authority boundaries."
            ),
            "priority_posture": "planning_candidate",
            "amendment_entitlement": "not_authorized_by_this_artifact",
            "derivation_posture": "derived_deterministically",
            "derivation_method": "cross_artifact_join",
            "source_artifact_refs": [path],
            "supporting_evidence_refs": sorted(
                {
                    "evidence:contract:v45e:v104",
                    "evidence:bound:v45b:symbol_catalog",
                    "evidence:bound:v45b:dependency_graph",
                    "evidence:bound:v45d:test_intent_matrix",
                    f"evidence:source:{path}:metrics",
                }
            ),
        }
        optimization_entries.append(
            {
                "entry_id": compute_repo_optimization_entry_id(payload_without_entry_id),
                **payload_without_entry_id,
            }
        )

    cluster_members = [
        {
            "member_ref_kind": "file_surface",
            "member_ref": path,
        }
        for path in hotspot_paths
    ]
    for path in sorted(bound_test_intent_matrix_payload["test_source_set"]):
        cluster_members.append(
            {
                "member_ref_kind": "test_surface",
                "member_ref": path,
            }
        )
    cluster_source_refs = sorted(
        {
            *hotspot_paths,
            *bound_test_intent_matrix_payload["test_source_set"],
        }
    )
    cluster_payload_without_entry_id = {
        "finding_scope": {
            "finding_scope_kind": "cross_surface_cluster",
            "finding_scope_ref": "cluster:repo_description_core_logic",
            "cluster_member_refs": cluster_members,
        },
        "compression_axis": "surface_compression",
        "optimization_posture": "consolidation_candidate",
        "support_basis": "test_and_dependency_concentration",
        "secondary_compression_axes": ["governance_compression"],
        "secondary_support_basis_tags": ["long_file_or_concentrated_surface"],
        "descriptive_finding_summary": (
            "Current repo-description logic and its defensive tests are concentrated across "
            f"{len(cluster_members)} bound surfaces with repeated fail-closed joins "
            "between code, dependency, and test-intent baselines."
        ),
        "optimization_candidate_summary": (
            "Inspect whether shared helper seams for V45 binding, scope resolution, and "
            "fail-closed validation should be factored more explicitly while preserving "
            "descriptive-only authority boundaries."
        ),
        "priority_posture": "planning_candidate",
        "amendment_entitlement": "not_authorized_by_this_artifact",
        "derivation_posture": "derived_deterministically",
        "derivation_method": "cross_artifact_join",
        "source_artifact_refs": cluster_source_refs,
        "supporting_evidence_refs": sorted(
            {
                "evidence:contract:v45e:v104",
                "evidence:bound:v45b:symbol_catalog",
                "evidence:bound:v45b:dependency_graph",
                "evidence:bound:v45c:arc_dependency_register",
                "evidence:bound:v45d:test_intent_matrix",
                "evidence:cluster:v45e:core_logic",
                *(f"evidence:source:{path}:metrics" for path in cluster_source_refs),
            }
        ),
    }
    optimization_entries.append(
        {
            "entry_id": compute_repo_optimization_entry_id(cluster_payload_without_entry_id),
            **cluster_payload_without_entry_id,
        }
    )

    payload_without_register_id = {
        "schema": REPO_OPTIMIZATION_REGISTER_SCHEMA,
        "repo_snapshot_id": bound_symbol_catalog_payload["repo_snapshot_id"],
        "repo_snapshot_hash": bound_symbol_catalog_payload["repo_snapshot_hash"],
        "snapshot_validity_posture": effective_snapshot_validity_posture,
        "source_set": normalized_source_paths,
        "source_set_hash": source_set_hash,
        "bound_entity_catalog_ref": bound_entity_catalog_payload["repo_entity_catalog_id"],
        "bound_schema_family_registry_ref": bound_schema_family_registry_payload[
            "schema_family_registry_id"
        ],
        "bound_symbol_catalog_ref": bound_symbol_catalog_payload["repo_symbol_catalog_id"],
        "bound_dependency_graph_ref": bound_dependency_graph_payload[
            "repo_dependency_graph_id"
        ],
        "bound_test_intent_matrix_ref": bound_test_intent_matrix_payload[
            "repo_test_intent_matrix_id"
        ],
        "register_scope": (
            "v45e-bounded-optimization-register-over-adeu_repo_description-surfaces"
        ),
        "extraction_posture": "derived_deterministically",
        "extraction_method": "cross_artifact_join",
        "optimization_entries": sorted(optimization_entries, key=lambda row: row["entry_id"]),
        "evidence_refs": [
            evidence_refs_by_id[key].model_dump(mode="json") for key in sorted(evidence_refs_by_id)
        ],
    }
    register = materialize_repo_optimization_register_payload(payload_without_register_id)
    validate_repo_optimization_register_against_v45_baseline(
        optimization_register_payload=register,
        entity_catalog_payload=bound_entity_catalog_payload,
        schema_family_registry_payload=bound_schema_family_registry_payload,
        symbol_catalog_payload=bound_symbol_catalog_payload,
        dependency_graph_payload=bound_dependency_graph_payload,
        test_intent_matrix_payload=bound_test_intent_matrix_payload,
        arc_dependency_register_payload=bound_arc_dependency_register_payload,
    )
    return register


def derive_v45f_repo_descriptive_normative_binding_frame(
    *,
    source_paths: list[str] | None = None,
    bound_entity_catalog_payload: dict[str, Any] | None = None,
    bound_schema_family_registry_payload: dict[str, Any] | None = None,
    bound_symbol_catalog_payload: dict[str, Any] | None = None,
    bound_dependency_graph_payload: dict[str, Any] | None = None,
    bound_arc_dependency_register_payload: dict[str, Any] | None = None,
    bound_test_intent_matrix_payload: dict[str, Any] | None = None,
    bound_optimization_register_payload: dict[str, Any] | None = None,
    snapshot_validity_posture: str | None = None,
) -> dict[str, Any]:
    root = repo_root(anchor=Path(__file__))
    requested_snapshot_validity_posture = snapshot_validity_posture or "snapshot_bound_current"
    normalized_source_paths = (
        source_paths if source_paths is not None else _default_v45f_source_paths()
    )
    normalized_source_paths = sorted(
        {_assert_repo_rel_path(path, field_name="source_paths") for path in normalized_source_paths}
    )
    if not normalized_source_paths:
        raise ValueError("source_paths must not be empty")

    if bound_schema_family_registry_payload is None or bound_entity_catalog_payload is None:
        derived_schema_registry, derived_entity_catalog = derive_v45a_repo_description_bundle(
            snapshot_validity_posture=requested_snapshot_validity_posture
        )
        bound_schema_family_registry_payload = (
            derived_schema_registry
            if bound_schema_family_registry_payload is None
            else bound_schema_family_registry_payload
        )
        bound_entity_catalog_payload = (
            derived_entity_catalog
            if bound_entity_catalog_payload is None
            else bound_entity_catalog_payload
        )
    if bound_symbol_catalog_payload is None or bound_dependency_graph_payload is None:
        derived_symbol_catalog, derived_dependency_graph = (
            derive_v45b_repo_symbol_catalog_and_dependency_graph(
                source_paths=default_v45b_source_paths(),
                snapshot_validity_posture=requested_snapshot_validity_posture,
            )
        )
        bound_symbol_catalog_payload = (
            derived_symbol_catalog
            if bound_symbol_catalog_payload is None
            else bound_symbol_catalog_payload
        )
        bound_dependency_graph_payload = (
            derived_dependency_graph
            if bound_dependency_graph_payload is None
            else bound_dependency_graph_payload
        )
    if bound_arc_dependency_register_payload is None:
        bound_arc_dependency_register_payload = _load_historical_v45c_v102_reference(root=root)
    if bound_test_intent_matrix_payload is None:
        bound_test_intent_matrix_payload = derive_v45d_repo_test_intent_matrix(
            source_paths=default_v45d_source_paths(),
            bound_symbol_catalog_payload=bound_symbol_catalog_payload,
            bound_dependency_graph_payload=bound_dependency_graph_payload,
            snapshot_validity_posture=requested_snapshot_validity_posture,
        )
    if bound_optimization_register_payload is None:
        bound_optimization_register_payload = derive_v45e_repo_optimization_register(
            source_paths=default_v45e_source_paths(),
            bound_entity_catalog_payload=bound_entity_catalog_payload,
            bound_schema_family_registry_payload=bound_schema_family_registry_payload,
            bound_symbol_catalog_payload=bound_symbol_catalog_payload,
            bound_dependency_graph_payload=bound_dependency_graph_payload,
            bound_test_intent_matrix_payload=bound_test_intent_matrix_payload,
            bound_arc_dependency_register_payload=bound_arc_dependency_register_payload,
            snapshot_validity_posture=requested_snapshot_validity_posture,
        )

    effective_snapshot_validity_posture = (
        snapshot_validity_posture
        or bound_optimization_register_payload["snapshot_validity_posture"]
    )
    if (
        effective_snapshot_validity_posture
        != bound_optimization_register_payload["snapshot_validity_posture"]
    ):
        raise ValueError(
            "snapshot_validity_posture must match the bound V45-E snapshot_validity_posture"
        )

    source_hashes: dict[str, str] = {}
    for source_path in normalized_source_paths:
        absolute_path = root / source_path
        if not absolute_path.is_file():
            raise FileNotFoundError(f"source path does not exist: {source_path}")
        text = absolute_path.read_text(encoding="utf-8")
        source_hashes[source_path] = sha256_canonical_json({"text": text})

    source_set_hash = sha256_canonical_json(
        {
            "source_paths": normalized_source_paths,
            "source_hashes": {path: source_hashes[path] for path in normalized_source_paths},
        }
    )

    evidence_refs_by_id: dict[str, RepoDescriptionEvidenceRef] = {
        "evidence:contract:v45f:v105": RepoDescriptionEvidenceRef(
            evidence_ref="evidence:contract:v45f:v105",
            evidence_kind="lock_contract_evidence",
        ),
        "evidence:planning:v28:v45f": RepoDescriptionEvidenceRef(
            evidence_ref="evidence:planning:v28:v45f",
            evidence_kind="planning_table_row_evidence",
        ),
        "evidence:decomposition:v45f": RepoDescriptionEvidenceRef(
            evidence_ref="evidence:decomposition:v45f",
            evidence_kind="governance_cue_evidence",
        ),
        "evidence:bound:v45a:entity_catalog": RepoDescriptionEvidenceRef(
            evidence_ref="evidence:bound:v45a:entity_catalog",
            evidence_kind="observed_anchor_tuple_evidence",
        ),
        "evidence:bound:v45a:schema_family_registry": RepoDescriptionEvidenceRef(
            evidence_ref="evidence:bound:v45a:schema_family_registry",
            evidence_kind="observed_anchor_tuple_evidence",
        ),
        "evidence:bound:v45b:symbol_catalog": RepoDescriptionEvidenceRef(
            evidence_ref="evidence:bound:v45b:symbol_catalog",
            evidence_kind="observed_anchor_tuple_evidence",
        ),
        "evidence:bound:v45b:dependency_graph": RepoDescriptionEvidenceRef(
            evidence_ref="evidence:bound:v45b:dependency_graph",
            evidence_kind="observed_anchor_tuple_evidence",
        ),
        "evidence:bound:v45c:arc_dependency_register": RepoDescriptionEvidenceRef(
            evidence_ref="evidence:bound:v45c:arc_dependency_register",
            evidence_kind="observed_anchor_tuple_evidence",
        ),
        "evidence:bound:v45d:test_intent_matrix": RepoDescriptionEvidenceRef(
            evidence_ref="evidence:bound:v45d:test_intent_matrix",
            evidence_kind="observed_anchor_tuple_evidence",
        ),
        "evidence:bound:v45e:optimization_register": RepoDescriptionEvidenceRef(
            evidence_ref="evidence:bound:v45e:optimization_register",
            evidence_kind="observed_anchor_tuple_evidence",
        ),
    }
    for source_path in normalized_source_paths:
        evidence_refs_by_id[f"evidence:source:{source_path}:binding"] = RepoDescriptionEvidenceRef(
            evidence_ref=f"evidence:source:{source_path}:binding",
            evidence_kind="governance_cue_evidence",
        )

    row_specs = [
        {
            "descriptive_input_kind": "repo_entity_catalog",
            "descriptive_input_ref": bound_entity_catalog_payload["repo_entity_catalog_id"],
            "consumer_class": "planning_consumer",
            "binding_posture": "advisory_only",
            "authority_source_kind": "descriptive_artifact_only_forbidden",
            "promotion_law_posture": "inferred_not_sufficient",
            "allowed_use_summary": (
                "Planning consumers may use the entity catalog as descriptive context when "
                "scoping follow-on repo work."
            ),
            "forbidden_use_summary": (
                "May not approve mutation, scheduling, execution, or settlement by itself."
            ),
            "derivation_posture": "derived_deterministically",
            "derivation_method": "policy_binding_rule",
            "source_artifact_refs": [
                "docs/DRAFT_NEXT_ARC_OPTIONS_v28.md",
                "docs/LOCKED_CONTINUATION_vNEXT_PLUS105.md",
            ],
            "supporting_evidence_refs": [
                "evidence:bound:v45a:entity_catalog",
                "evidence:contract:v45f:v105",
                "evidence:planning:v28:v45f",
                "evidence:source:docs/DRAFT_NEXT_ARC_OPTIONS_v28.md:binding",
                "evidence:source:docs/LOCKED_CONTINUATION_vNEXT_PLUS105.md:binding",
            ],
        },
        {
            "descriptive_input_kind": "repo_schema_family_registry",
            "descriptive_input_ref": bound_schema_family_registry_payload[
                "schema_family_registry_id"
            ],
            "consumer_class": "adjudication_consumer",
            "binding_posture": "eligibility_signal_only",
            "authority_source_kind": "separate_decision_required",
            "promotion_law_posture": "adjudication_required_before_normative_use",
            "allowed_use_summary": (
                "Adjudication consumers may use schema-family structure to determine whether a "
                "later decision surface needs explicit policy review."
            ),
            "forbidden_use_summary": (
                "May not be treated as settled normative authority or direct execution approval."
            ),
            "derivation_posture": "derived_deterministically",
            "derivation_method": "policy_binding_rule",
            "source_artifact_refs": [
                "docs/DRAFT_V45_REPO_SELF_DESCRIPTION_DECOMPOSITION_v0.md",
                "docs/LOCKED_CONTINUATION_vNEXT_PLUS105.md",
            ],
            "supporting_evidence_refs": [
                "evidence:bound:v45a:schema_family_registry",
                "evidence:contract:v45f:v105",
                "evidence:decomposition:v45f",
                "evidence:source:docs/DRAFT_V45_REPO_SELF_DESCRIPTION_DECOMPOSITION_v0.md:binding",
                "evidence:source:docs/LOCKED_CONTINUATION_vNEXT_PLUS105.md:binding",
            ],
        },
        {
            "descriptive_input_kind": "repo_symbol_catalog",
            "descriptive_input_ref": bound_symbol_catalog_payload["repo_symbol_catalog_id"],
            "consumer_class": "policy_consumer",
            "binding_posture": "adjudication_required",
            "authority_source_kind": "separate_decision_required",
            "promotion_law_posture": "adjudication_required_before_normative_use",
            "allowed_use_summary": (
                "Policy consumers may use symbol topology as one input when evaluating whether "
                "later governance artifacts need narrower scope boundaries."
            ),
            "forbidden_use_summary": (
                "May not convert code-shape visibility into automatic authority or direct repo "
                "changes."
            ),
            "derivation_posture": "derived_deterministically",
            "derivation_method": "cross_artifact_join",
            "source_artifact_refs": [
                "docs/ASSESSMENT_vNEXT_PLUS105_EDGES.md",
                "docs/LOCKED_CONTINUATION_vNEXT_PLUS105.md",
            ],
            "supporting_evidence_refs": [
                "evidence:bound:v45b:symbol_catalog",
                "evidence:contract:v45f:v105",
                "evidence:source:docs/ASSESSMENT_vNEXT_PLUS105_EDGES.md:binding",
                "evidence:source:docs/LOCKED_CONTINUATION_vNEXT_PLUS105.md:binding",
            ],
        },
        {
            "descriptive_input_kind": "repo_dependency_graph",
            "descriptive_input_ref": bound_dependency_graph_payload["repo_dependency_graph_id"],
            "consumer_class": "recursive_governance_consumer",
            "binding_posture": "separate_normative_authority_required",
            "authority_source_kind": "separate_normative_artifact_required",
            "promotion_law_posture": "settled_authority_required_before_execution",
            "allowed_use_summary": (
                "Recursive-governance consumers may use dependency structure only as an "
                "eligibility input inside a stronger separately settled normative frame."
            ),
            "forbidden_use_summary": (
                "May not authorize recursive execution, auto-mutation, or scheduler control by "
                "itself."
            ),
            "derivation_posture": "derived_deterministically",
            "derivation_method": "cross_artifact_join",
            "source_artifact_refs": [
                "docs/ASSESSMENT_vNEXT_PLUS105_EDGES.md",
                "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS105.md",
                "docs/LOCKED_CONTINUATION_vNEXT_PLUS105.md",
            ],
            "supporting_evidence_refs": [
                "evidence:bound:v45b:dependency_graph",
                "evidence:bound:v45c:arc_dependency_register",
                "evidence:contract:v45f:v105",
                "evidence:source:docs/ASSESSMENT_vNEXT_PLUS105_EDGES.md:binding",
                "evidence:source:docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS105.md:binding",
                "evidence:source:docs/LOCKED_CONTINUATION_vNEXT_PLUS105.md:binding",
            ],
        },
        {
            "descriptive_input_kind": "repo_test_intent_matrix",
            "descriptive_input_ref": bound_test_intent_matrix_payload[
                "repo_test_intent_matrix_id"
            ],
            "consumer_class": "adjudication_consumer",
            "binding_posture": "adjudication_required",
            "authority_source_kind": "separate_decision_required",
            "promotion_law_posture": "adjudication_required_before_normative_use",
            "allowed_use_summary": (
                "Adjudication consumers may use test-intent visibility as supporting context "
                "when checking whether a later decision claim is actually defended."
            ),
            "forbidden_use_summary": (
                "May not be overread as direct release gating, merge approval, or settlement."
            ),
            "derivation_posture": "derived_deterministically",
            "derivation_method": "cross_artifact_join",
            "source_artifact_refs": [
                "docs/ASSESSMENT_vNEXT_PLUS105_EDGES.md",
                "docs/LOCKED_CONTINUATION_vNEXT_PLUS105.md",
            ],
            "supporting_evidence_refs": [
                "evidence:bound:v45d:test_intent_matrix",
                "evidence:contract:v45f:v105",
                "evidence:source:docs/ASSESSMENT_vNEXT_PLUS105_EDGES.md:binding",
                "evidence:source:docs/LOCKED_CONTINUATION_vNEXT_PLUS105.md:binding",
            ],
        },
        {
            "descriptive_input_kind": "repo_optimization_register",
            "descriptive_input_ref": bound_optimization_register_payload[
                "repo_optimization_register_id"
            ],
            "consumer_class": "policy_consumer",
            "binding_posture": "separate_normative_authority_required",
            "authority_source_kind": "separate_lock_required",
            "promotion_law_posture": "settled_authority_required_before_execution",
            "allowed_use_summary": (
                "Policy consumers may use optimization diagnostics to decide whether a later "
                "lock should narrow or reject a proposed amendment path."
            ),
            "forbidden_use_summary": (
                "May not convert diagnostics into amendment entitlement, scheduling priority, or "
                "execution approval."
            ),
            "derivation_posture": "derived_deterministically",
            "derivation_method": "policy_binding_rule",
            "source_artifact_refs": [
                "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS105.md",
                "docs/LOCKED_CONTINUATION_vNEXT_PLUS105.md",
            ],
            "supporting_evidence_refs": [
                "evidence:bound:v45e:optimization_register",
                "evidence:contract:v45f:v105",
                "evidence:source:docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS105.md:binding",
                "evidence:source:docs/LOCKED_CONTINUATION_vNEXT_PLUS105.md:binding",
            ],
        },
    ]

    binding_entries = []
    for row in row_specs:
        payload_without_entry_id = {
            **row,
            "source_artifact_refs": row["source_artifact_refs"],
            "supporting_evidence_refs": row["supporting_evidence_refs"],
        }
        binding_entries.append(
            {
                "entry_id": compute_repo_descriptive_normative_binding_entry_id(
                    payload_without_entry_id
                ),
                **payload_without_entry_id,
            }
        )

    payload_without_frame_id = {
        "schema": REPO_DESCRIPTIVE_NORMATIVE_BINDING_FRAME_SCHEMA,
        "repo_snapshot_id": bound_optimization_register_payload["repo_snapshot_id"],
        "repo_snapshot_hash": bound_optimization_register_payload["repo_snapshot_hash"],
        "snapshot_validity_posture": effective_snapshot_validity_posture,
        "source_set": normalized_source_paths,
        "source_set_hash": source_set_hash,
        "bound_entity_catalog_ref": bound_entity_catalog_payload["repo_entity_catalog_id"],
        "bound_schema_family_registry_ref": bound_schema_family_registry_payload[
            "schema_family_registry_id"
        ],
        "bound_symbol_catalog_ref": bound_symbol_catalog_payload["repo_symbol_catalog_id"],
        "bound_dependency_graph_ref": bound_dependency_graph_payload[
            "repo_dependency_graph_id"
        ],
        "bound_arc_dependency_register_ref": bound_arc_dependency_register_payload[
            "repo_arc_dependency_register_id"
        ],
        "bound_test_intent_matrix_ref": bound_test_intent_matrix_payload[
            "repo_test_intent_matrix_id"
        ],
        "bound_optimization_register_ref": bound_optimization_register_payload[
            "repo_optimization_register_id"
        ],
        "binding_scope": (
            "v45f-bounded-descriptive-to-normative-binding-frame-over-released-v45-baseline"
        ),
        "extraction_posture": "derived_deterministically",
        "extraction_method": "policy_binding_rule",
        "binding_entries": sorted(binding_entries, key=lambda row: row["entry_id"]),
        "evidence_refs": [
            evidence_refs_by_id[key].model_dump(mode="json") for key in sorted(evidence_refs_by_id)
        ],
    }
    frame = materialize_repo_descriptive_normative_binding_frame_payload(
        payload_without_frame_id
    )
    validate_repo_descriptive_normative_binding_frame_against_v45_baseline(
        binding_frame_payload=frame,
        entity_catalog_payload=bound_entity_catalog_payload,
        schema_family_registry_payload=bound_schema_family_registry_payload,
        symbol_catalog_payload=bound_symbol_catalog_payload,
        dependency_graph_payload=bound_dependency_graph_payload,
        arc_dependency_register_payload=bound_arc_dependency_register_payload,
        test_intent_matrix_payload=bound_test_intent_matrix_payload,
        optimization_register_payload=bound_optimization_register_payload,
    )
    return frame


def default_v45a_source_paths() -> list[str]:
    return list(_DEFAULT_SOURCE_PATHS)


def default_v45b_source_paths() -> list[str]:
    return list(_DEFAULT_V45B_SOURCE_PATHS)


def default_v45c_source_paths() -> list[str]:
    return list(_DEFAULT_V45C_SOURCE_PATHS)


def default_v45d_source_paths() -> list[str]:
    return _default_v45d_source_paths()


def default_v45e_source_paths() -> list[str]:
    return _default_v45e_source_paths()


def default_v45f_source_paths() -> list[str]:
    return _default_v45f_source_paths()
