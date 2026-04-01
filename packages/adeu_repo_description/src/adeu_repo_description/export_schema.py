from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from adeu_ir.repo import repo_root

from .models import (
    RepoArcDependencyRegister,
    RepoArcDependencyRegisterV1,
    RepoDependencyGraph,
    RepoDescriptiveNormativeBindingFrame,
    RepoEntityCatalog,
    RepoOptimizationRegister,
    RepoSchemaFamilyRegistry,
    RepoSymbolCatalog,
    RepoTestIntentMatrix,
)

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _write_schema(path: Path, schema: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(schema, indent=2, sort_keys=True) + "\n"
    path.write_text(payload, encoding="utf-8")


def _assert_no_absolute_path_material(
    value: Any,
    *,
    repo_root_path: Path,
    node_path: str = "$",
) -> None:
    if isinstance(value, dict):
        for key in sorted(value):
            _assert_no_absolute_path_material(
                value[key],
                repo_root_path=repo_root_path,
                node_path=f"{node_path}.{key}",
            )
        return
    if isinstance(value, list):
        for index, item in enumerate(value):
            _assert_no_absolute_path_material(
                item,
                repo_root_path=repo_root_path,
                node_path=f"{node_path}[{index}]",
            )
        return
    if not isinstance(value, str):
        return

    normalized = value.replace("\\", "/")
    root_text = repo_root_path.as_posix()
    if root_text in normalized:
        raise RuntimeError(
            f"schema export contains repository absolute path material at {node_path}: {value!r}"
        )
    if _WINDOWS_ABSOLUTE_PATH_RE.search(value):
        raise RuntimeError(
            f"schema export contains Windows absolute path material at {node_path}: {value!r}"
        )
    if normalized.startswith("/home/") or normalized.startswith("/Users/"):
        raise RuntimeError(
            f"schema export contains user-home absolute path material at {node_path}: {value!r}"
        )


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    dependency_register_v1_schema = RepoArcDependencyRegisterV1.model_json_schema(by_alias=True)
    dependency_register_schema = RepoArcDependencyRegister.model_json_schema(by_alias=True)
    dependency_graph_schema = RepoDependencyGraph.model_json_schema(by_alias=True)
    binding_frame_schema = RepoDescriptiveNormativeBindingFrame.model_json_schema(by_alias=True)
    optimization_register_schema = RepoOptimizationRegister.model_json_schema(by_alias=True)
    test_intent_matrix_schema = RepoTestIntentMatrix.model_json_schema(by_alias=True)
    registry_schema = RepoSchemaFamilyRegistry.model_json_schema(by_alias=True)
    catalog_schema = RepoEntityCatalog.model_json_schema(by_alias=True)
    symbol_catalog_schema = RepoSymbolCatalog.model_json_schema(by_alias=True)

    _assert_no_absolute_path_material(dependency_register_v1_schema, repo_root_path=root)
    _assert_no_absolute_path_material(dependency_register_schema, repo_root_path=root)
    _assert_no_absolute_path_material(dependency_graph_schema, repo_root_path=root)
    _assert_no_absolute_path_material(binding_frame_schema, repo_root_path=root)
    _assert_no_absolute_path_material(optimization_register_schema, repo_root_path=root)
    _assert_no_absolute_path_material(test_intent_matrix_schema, repo_root_path=root)
    _assert_no_absolute_path_material(registry_schema, repo_root_path=root)
    _assert_no_absolute_path_material(catalog_schema, repo_root_path=root)
    _assert_no_absolute_path_material(symbol_catalog_schema, repo_root_path=root)

    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_arc_dependency_register.v1.json",
        dependency_register_v1_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_arc_dependency_register.v2.json",
        dependency_register_schema,
    )
    _write_schema(
        root / "spec" / "repo_arc_dependency_register.schema.json",
        dependency_register_schema,
    )
    _write_schema(
        root / "packages" / "adeu_repo_description" / "schema" / "repo_dependency_graph.v1.json",
        dependency_graph_schema,
    )
    _write_schema(
        root / "spec" / "repo_dependency_graph.schema.json",
        dependency_graph_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_descriptive_normative_binding_frame.v1.json",
        binding_frame_schema,
    )
    _write_schema(
        root / "spec" / "repo_descriptive_normative_binding_frame.schema.json",
        binding_frame_schema,
    )
    _write_schema(
        root / "packages" / "adeu_repo_description" / "schema" / "repo_test_intent_matrix.v1.json",
        test_intent_matrix_schema,
    )
    _write_schema(
        root / "spec" / "repo_test_intent_matrix.schema.json",
        test_intent_matrix_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_optimization_register.v1.json",
        optimization_register_schema,
    )
    _write_schema(
        root / "spec" / "repo_optimization_register.schema.json",
        optimization_register_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_schema_family_registry.v1.json",
        registry_schema,
    )
    _write_schema(
        root / "spec" / "repo_schema_family_registry.schema.json",
        registry_schema,
    )
    _write_schema(
        root / "packages" / "adeu_repo_description" / "schema" / "repo_entity_catalog.v1.json",
        catalog_schema,
    )
    _write_schema(
        root / "spec" / "repo_entity_catalog.schema.json",
        catalog_schema,
    )
    _write_schema(
        root / "packages" / "adeu_repo_description" / "schema" / "repo_symbol_catalog.v1.json",
        symbol_catalog_schema,
    )
    _write_schema(
        root / "spec" / "repo_symbol_catalog.schema.json",
        symbol_catalog_schema,
    )


if __name__ == "__main__":
    main()
