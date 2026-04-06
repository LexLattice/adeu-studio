from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from adeu_ir.repo import repo_root

from .models import (
    EdgeClassCatalog,
    EdgeProbeTemplateCatalog,
    EdgeTaxonomyRevisionJudgment,
    SymbolEdgeAdjudicationLedger,
    SymbolEdgeApplicabilityFrame,
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
    edge_class_catalog_schema = EdgeClassCatalog.model_json_schema(by_alias=True)
    edge_probe_template_catalog_schema = EdgeProbeTemplateCatalog.model_json_schema(by_alias=True)
    symbol_edge_applicability_frame_schema = SymbolEdgeApplicabilityFrame.model_json_schema(
        by_alias=True
    )
    symbol_edge_adjudication_ledger_schema = SymbolEdgeAdjudicationLedger.model_json_schema(
        by_alias=True
    )
    edge_taxonomy_revision_judgment_schema = EdgeTaxonomyRevisionJudgment.model_json_schema(
        by_alias=True
    )

    for schema in (
        edge_class_catalog_schema,
        edge_probe_template_catalog_schema,
        symbol_edge_applicability_frame_schema,
        symbol_edge_adjudication_ledger_schema,
        edge_taxonomy_revision_judgment_schema,
    ):
        _assert_no_absolute_path_material(schema, repo_root_path=root)

    mappings = (
        (
            root / "packages" / "adeu_edge_ledger" / "schema" / "adeu_edge_class_catalog.v1.json",
            root / "spec" / "adeu_edge_class_catalog.schema.json",
            edge_class_catalog_schema,
        ),
        (
            root
            / "packages"
            / "adeu_edge_ledger"
            / "schema"
            / "adeu_edge_probe_template_catalog.v1.json",
            root / "spec" / "adeu_edge_probe_template_catalog.schema.json",
            edge_probe_template_catalog_schema,
        ),
        (
            root
            / "packages"
            / "adeu_edge_ledger"
            / "schema"
            / "adeu_symbol_edge_applicability_frame.v1.json",
            root / "spec" / "adeu_symbol_edge_applicability_frame.schema.json",
            symbol_edge_applicability_frame_schema,
        ),
        (
            root
            / "packages"
            / "adeu_edge_ledger"
            / "schema"
            / "adeu_symbol_edge_adjudication_ledger.v1.json",
            root / "spec" / "adeu_symbol_edge_adjudication_ledger.schema.json",
            symbol_edge_adjudication_ledger_schema,
        ),
        (
            root
            / "packages"
            / "adeu_edge_ledger"
            / "schema"
            / "adeu_edge_taxonomy_revision_judgment.v1.json",
            root / "spec" / "adeu_edge_taxonomy_revision_judgment.schema.json",
            edge_taxonomy_revision_judgment_schema,
        ),
    )
    for authoritative_path, mirror_path, schema in mappings:
        _write_schema(authoritative_path, schema)
        _write_schema(mirror_path, schema)


if __name__ == "__main__":
    main()
