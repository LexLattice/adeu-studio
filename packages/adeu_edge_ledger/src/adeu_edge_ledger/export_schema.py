from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from adeu_ir.repo import repo_root

from .models import (
    EdgeClassCatalog,
    EdgeProbeTemplateCatalog,
    EdgeTaxonomyRevisionRegister,
    SymbolEdgeAdjudicationLedger,
    SymbolEdgeApplicabilityFrame,
)

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _write_schema(path: Path, schema: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(schema, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _assert_no_absolute_path_material(
    value: Any,
    *,
    repo_root_path: Path,
) -> None:
    if isinstance(value, dict):
        for item in value.values():
            _assert_no_absolute_path_material(item, repo_root_path=repo_root_path)
        return
    if isinstance(value, list):
        for item in value:
            _assert_no_absolute_path_material(item, repo_root_path=repo_root_path)
        return
    if not isinstance(value, str):
        return
    normalized = value.replace("\\", "/")
    root_text = repo_root_path.as_posix()
    if root_text in normalized:
        raise RuntimeError("schema export contains repository absolute path material")
    if normalized.startswith("/home/") or normalized.startswith("/Users/"):
        raise RuntimeError("schema export contains user-home absolute path material")
    if _WINDOWS_ABSOLUTE_PATH_RE.search(value):
        raise RuntimeError("schema export contains Windows absolute path material")


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    mappings = (
        (
            EdgeClassCatalog.model_json_schema(by_alias=True),
            root / "packages" / "adeu_edge_ledger" / "schema" / "adeu_edge_class_catalog.v1.json",
            root / "spec" / "adeu_edge_class_catalog.schema.json",
        ),
        (
            EdgeProbeTemplateCatalog.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_edge_ledger"
            / "schema"
            / "adeu_edge_probe_template_catalog.v1.json",
            root / "spec" / "adeu_edge_probe_template_catalog.schema.json",
        ),
        (
            SymbolEdgeApplicabilityFrame.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_edge_ledger"
            / "schema"
            / "adeu_symbol_edge_applicability_frame.v1.json",
            root / "spec" / "adeu_symbol_edge_applicability_frame.schema.json",
        ),
        (
            SymbolEdgeAdjudicationLedger.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_edge_ledger"
            / "schema"
            / "adeu_symbol_edge_adjudication_ledger.v1.json",
            root / "spec" / "adeu_symbol_edge_adjudication_ledger.schema.json",
        ),
        (
            EdgeTaxonomyRevisionRegister.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_edge_ledger"
            / "schema"
            / "adeu_edge_taxonomy_revision_register.v1.json",
            root / "spec" / "adeu_edge_taxonomy_revision_register.schema.json",
        ),
    )
    for schema, authoritative_path, mirror_path in mappings:
        _assert_no_absolute_path_material(schema, repo_root_path=root)
        _write_schema(authoritative_path, schema)
        _write_schema(mirror_path, schema)


if __name__ == "__main__":
    main()
