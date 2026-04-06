from __future__ import annotations

import json
from pathlib import Path

from adeu_edge_ledger.export_schema import _assert_no_absolute_path_material
from adeu_edge_ledger.models import (
    EdgeClassCatalog,
    EdgeProbeTemplateCatalog,
    EdgeTaxonomyRevisionJudgment,
    SymbolEdgeAdjudicationLedger,
    SymbolEdgeApplicabilityFrame,
)
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _schema_paths() -> list[tuple[Path, Path]]:
    root = _repo_root()
    return [
        (
            root / "packages" / "adeu_edge_ledger" / "schema" / "adeu_edge_class_catalog.v1.json",
            root / "spec" / "adeu_edge_class_catalog.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_edge_ledger"
            / "schema"
            / "adeu_edge_probe_template_catalog.v1.json",
            root / "spec" / "adeu_edge_probe_template_catalog.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_edge_ledger"
            / "schema"
            / "adeu_symbol_edge_applicability_frame.v1.json",
            root / "spec" / "adeu_symbol_edge_applicability_frame.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_edge_ledger"
            / "schema"
            / "adeu_symbol_edge_adjudication_ledger.v1.json",
            root / "spec" / "adeu_symbol_edge_adjudication_ledger.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_edge_ledger"
            / "schema"
            / "adeu_edge_taxonomy_revision_judgment.v1.json",
            root / "spec" / "adeu_edge_taxonomy_revision_judgment.schema.json",
        ),
    ]


def test_exported_edge_ledger_schemas_are_valid_json_schemas() -> None:
    for authoritative, mirror in _schema_paths():
        authoritative_payload = json.loads(authoritative.read_text(encoding="utf-8"))
        mirror_payload = json.loads(mirror.read_text(encoding="utf-8"))
        Draft202012Validator.check_schema(authoritative_payload)
        Draft202012Validator.check_schema(mirror_payload)
        assert authoritative_payload == mirror_payload


def test_exported_edge_ledger_schemas_match_model_json_schema() -> None:
    expected = {
        "adeu_edge_class_catalog.v1.json": EdgeClassCatalog.model_json_schema(by_alias=True),
        "adeu_edge_probe_template_catalog.v1.json": EdgeProbeTemplateCatalog.model_json_schema(
            by_alias=True
        ),
        "adeu_symbol_edge_applicability_frame.v1.json": SymbolEdgeApplicabilityFrame.model_json_schema(
            by_alias=True
        ),
        "adeu_symbol_edge_adjudication_ledger.v1.json": SymbolEdgeAdjudicationLedger.model_json_schema(
            by_alias=True
        ),
        "adeu_edge_taxonomy_revision_judgment.v1.json": EdgeTaxonomyRevisionJudgment.model_json_schema(
            by_alias=True
        ),
    }
    for authoritative, _mirror in _schema_paths():
        payload = json.loads(authoritative.read_text(encoding="utf-8"))
        assert payload == expected[authoritative.name]


def test_exported_edge_ledger_schemas_expose_expected_schema_consts() -> None:
    expected_consts = {
        "adeu_edge_class_catalog.v1.json": "adeu_edge_class_catalog@1",
        "adeu_edge_probe_template_catalog.v1.json": "adeu_edge_probe_template_catalog@1",
        "adeu_symbol_edge_applicability_frame.v1.json": "adeu_symbol_edge_applicability_frame@1",
        "adeu_symbol_edge_adjudication_ledger.v1.json": "adeu_symbol_edge_adjudication_ledger@1",
        "adeu_edge_taxonomy_revision_judgment.v1.json": "adeu_edge_taxonomy_revision_judgment@1",
    }
    for authoritative, _mirror in _schema_paths():
        payload = json.loads(authoritative.read_text(encoding="utf-8"))
        assert payload["properties"]["schema"]["const"] == expected_consts[authoritative.name]


def test_exported_edge_ledger_schemas_contain_no_absolute_paths() -> None:
    root = _repo_root()
    for authoritative, mirror in _schema_paths():
        _assert_no_absolute_path_material(
            json.loads(authoritative.read_text(encoding="utf-8")),
            repo_root_path=root,
        )
        _assert_no_absolute_path_material(
            json.loads(mirror.read_text(encoding="utf-8")),
            repo_root_path=root,
        )
