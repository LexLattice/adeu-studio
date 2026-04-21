from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from adeu_ir.repo import repo_root

from .anm_models import (
    AnmBenchmarkPolicyConsumerBindingProfile,
    AnmDocAuthorityProfile,
    AnmDocClassPolicy,
    AnmMarkdownCoexistenceProfile,
    AnmMigrationBindingProfile,
    AnmPolicyConsumerBindingProfile,
    AnmReaderProjectionManifest,
    AnmSelectorPredicateOwnershipProfile,
    AnmSemanticDiffReport,
    AnmSourceSetManifest,
    CheckerFactBundle,
    D1NormalizedIR,
    PolicyEvaluationResultSet,
    PolicyObligationLedger,
    PredicateContractsBootstrap,
)
from .models import AdeuCommitmentsIR

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\\\")


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
    schema_outputs = [
        (
            AdeuCommitmentsIR,
            root / "packages" / "adeu_commitments_ir" / "schema" / "adeu_commitments_ir.v0_1.json",
            root / "spec" / "adeu_commitments_ir.schema.json",
        ),
        (
            D1NormalizedIR,
            root / "packages" / "adeu_commitments_ir" / "schema" / "d1_normalized_ir.v1.json",
            root / "spec" / "d1_normalized_ir.schema.json",
        ),
        (
            PredicateContractsBootstrap,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "predicate_contracts_bootstrap.v1.json",
            root / "spec" / "predicate_contracts_bootstrap.schema.json",
        ),
        (
            CheckerFactBundle,
            root / "packages" / "adeu_commitments_ir" / "schema" / "checker_fact_bundle.v1.json",
            root / "spec" / "checker_fact_bundle.schema.json",
        ),
        (
            PolicyEvaluationResultSet,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "policy_evaluation_result_set.v1.json",
            root / "spec" / "policy_evaluation_result_set.schema.json",
        ),
        (
            PolicyObligationLedger,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "policy_obligation_ledger.v1.json",
            root / "spec" / "policy_obligation_ledger.schema.json",
        ),
        (
            AnmMarkdownCoexistenceProfile,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "anm_markdown_coexistence_profile.v1.json",
            root / "spec" / "anm_markdown_coexistence_profile.schema.json",
        ),
        (
            AnmSelectorPredicateOwnershipProfile,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "anm_selector_predicate_ownership_profile.v1.json",
            root / "spec" / "anm_selector_predicate_ownership_profile.schema.json",
        ),
        (
            AnmPolicyConsumerBindingProfile,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "anm_policy_consumer_binding_profile.v1.json",
            root / "spec" / "anm_policy_consumer_binding_profile.schema.json",
        ),
        (
            AnmBenchmarkPolicyConsumerBindingProfile,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "anm_benchmark_policy_consumer_binding_profile.v1.json",
            root / "spec" / "anm_benchmark_policy_consumer_binding_profile.schema.json",
        ),
        (
            AnmSourceSetManifest,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "anm_source_set_manifest.v1.json",
            root / "spec" / "anm_source_set_manifest.schema.json",
        ),
        (
            AnmDocAuthorityProfile,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "anm_doc_authority_profile.v1.json",
            root / "spec" / "anm_doc_authority_profile.schema.json",
        ),
        (
            AnmDocClassPolicy,
            root / "packages" / "adeu_commitments_ir" / "schema" / "anm_doc_class_policy.v1.json",
            root / "spec" / "anm_doc_class_policy.schema.json",
        ),
        (
            AnmMigrationBindingProfile,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "anm_migration_binding_profile.v1.json",
            root / "spec" / "anm_migration_binding_profile.schema.json",
        ),
        (
            AnmReaderProjectionManifest,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "anm_reader_projection_manifest.v1.json",
            root / "spec" / "anm_reader_projection_manifest.schema.json",
        ),
        (
            AnmSemanticDiffReport,
            root
            / "packages"
            / "adeu_commitments_ir"
            / "schema"
            / "anm_semantic_diff_report.v1.json",
            root / "spec" / "anm_semantic_diff_report.schema.json",
        ),
    ]

    for model, authoritative_path, mirror_path in schema_outputs:
        schema = model.model_json_schema(by_alias=True)
        _assert_no_absolute_path_material(schema, repo_root_path=root)
        _write_schema(authoritative_path, schema)
        _write_schema(mirror_path, schema)


if __name__ == "__main__":
    main()
