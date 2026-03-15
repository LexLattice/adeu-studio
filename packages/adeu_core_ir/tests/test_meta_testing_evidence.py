from __future__ import annotations

import json
import shutil
from pathlib import Path
from typing import Any, cast

import pytest
from adeu_core_ir import (
    DEFAULT_META_MODULE_CATALOG_REFERENCE_PATH,
    DEFAULT_META_MODULE_CATALOG_SCHEMA_PATH,
    DEFAULT_META_TESTING_INTENT_PACKET_REFERENCE_PATH,
    DEFAULT_META_TESTING_INTENT_PACKET_SCHEMA_PATH,
    DEFAULT_V65_BASELINE_METRICS_PATH,
    materialize_v37a_meta_intent_module_catalog_evidence,
)
from adeu_core_ir.meta_testing_evidence import MetaTestingEvidenceError
from adeu_ir.repo import repo_root


def _source_repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _canonical_pretty_json(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def _write_json(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(_canonical_pretty_json(payload), encoding="utf-8")


def _copy_repo_relative_file(*, source_root: Path, target_root: Path, relative_path: str) -> None:
    source = source_root / relative_path
    target = target_root / relative_path
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, target)


def _build_temp_repo_fixture_tree(tmp_path: Path) -> Path:
    source_root = _source_repo_root()
    repo_root_path = tmp_path / "repo"
    repo_root_path.mkdir()
    for relative_path in (
        "AGENTS.md",
        "apps/api/scripts/build_quality_dashboard.py",
        "apps/api/scripts/build_stop_gate_metrics.py",
        "apps/api/scripts/generate_instruction_policy_views.py",
        "apps/api/scripts/lint_arc_bundle.py",
        "apps/api/scripts/lint_closeout_consistency.py",
        "apps/api/scripts/lint_semantic_compiler_closeout.py",
        "docs/ASSESSMENT_vNEXT_PLUS65_EDGES.md",
        "docs/DRAFT_RECURSIVE_COMPILATION_v0.md",
        "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS65.md",
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS65.md",
        DEFAULT_META_TESTING_INTENT_PACKET_SCHEMA_PATH,
        DEFAULT_META_MODULE_CATALOG_SCHEMA_PATH,
        DEFAULT_META_TESTING_INTENT_PACKET_REFERENCE_PATH,
        DEFAULT_META_MODULE_CATALOG_REFERENCE_PATH,
        "artifacts/agent_harness/v65/evidence_inputs/metric_key_continuity_assertion_v65.json",
        "artifacts/agent_harness/v65/evidence_inputs/runtime_observability_comparison_v65.json",
        "artifacts/agent_harness/v65/evidence_inputs/v36e_surface_compiler_export_evidence_v65.json",
        "artifacts/agent_harness/v65/runtime/evidence/codex/copilot/v65-closeout-main-1/urm_events.ndjson",
        "artifacts/quality_dashboard_v65_closeout.json",
        DEFAULT_V65_BASELINE_METRICS_PATH,
        "artifacts/stop_gate/report_v65_closeout.md",
        "packages/adeu_core_ir/src/adeu_core_ir/meta_testing.py",
        "packages/urm_runtime/src/urm_runtime/events_tools.py",
    ):
        _copy_repo_relative_file(
            source_root=source_root,
            target_root=repo_root_path,
            relative_path=relative_path,
        )
    return repo_root_path


def _load_json(repo_root_path: Path, relative_path: str) -> dict[str, object]:
    return json.loads((repo_root_path / relative_path).read_text(encoding="utf-8"))


def _write_current_stop_gate_metrics_fixture(
    *,
    repo_root_path: Path,
    current_rel: str = "artifacts/stop_gate/metrics_v66_closeout.json",
) -> str:
    payload = _load_json(repo_root_path, DEFAULT_V65_BASELINE_METRICS_PATH)
    _write_json(repo_root_path / current_rel, payload)
    return current_rel


def _materialize_v37a_evidence(*, repo_root_path: Path) -> dict[str, object]:
    current_rel = _write_current_stop_gate_metrics_fixture(repo_root_path=repo_root_path)
    evidence = materialize_v37a_meta_intent_module_catalog_evidence(
        repo_root=repo_root_path,
        current_metrics_path=current_rel,
    )
    return {
        "artifact": evidence,
        "payload": json.loads((repo_root_path / evidence.path).read_text(encoding="utf-8")),
    }


def test_materialize_v37a_meta_intent_module_catalog_evidence_is_deterministic(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)

    first = _materialize_v37a_evidence(repo_root_path=repo_root_path)
    second = _materialize_v37a_evidence(repo_root_path=repo_root_path)

    assert first["artifact"].hash == second["artifact"].hash
    assert first["payload"] == second["payload"]
    assert first["payload"]["schema"] == "v37a_meta_intent_module_catalog_evidence@1"


def test_materialize_v37a_evidence_fails_closed_on_authoritative_input_hash_drift(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    current_rel = _write_current_stop_gate_metrics_fixture(repo_root_path=repo_root_path)
    assessment_doc = repo_root_path / "docs/ASSESSMENT_vNEXT_PLUS65_EDGES.md"
    assessment_doc.write_text(
        assessment_doc.read_text(encoding="utf-8") + "\n",
        encoding="utf-8",
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match=(
            "authoritative_inputs\\[v65_assessment_doc\\]\\.artifact_sha256 "
            "must match repo file bytes"
        ),
    ):
        materialize_v37a_meta_intent_module_catalog_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37a_evidence_fails_closed_on_missing_checkpoint_executor_binding(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    current_rel = _write_current_stop_gate_metrics_fixture(repo_root_path=repo_root_path)
    (repo_root_path / "apps/api/scripts/build_quality_dashboard.py").unlink()

    with pytest.raises(
        MetaTestingEvidenceError,
        match=(
            "modules\\[checkpoint_05_quality_dashboard_build\\]\\.executor_bindings"
            "\\[quality_dashboard_builder\\]\\.binding_ref does not exist"
        ),
    ):
        materialize_v37a_meta_intent_module_catalog_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37a_evidence_fails_closed_on_missing_dispatch_provenance_ref(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    current_rel = _write_current_stop_gate_metrics_fixture(repo_root_path=repo_root_path)
    (repo_root_path / "docs/DRAFT_RECURSIVE_COMPILATION_v0.md").unlink()

    with pytest.raises(
        MetaTestingEvidenceError,
        match=(
            "modules\\[reasoning_01_meta_intent_interpreter\\]\\.dispatch_provenance"
            "\\.template_version_ref does not exist"
        ),
    ):
        materialize_v37a_meta_intent_module_catalog_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37a_evidence_fails_closed_on_implicit_sequence_law(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    current_rel = _write_current_stop_gate_metrics_fixture(repo_root_path=repo_root_path)
    module_catalog = _load_json(repo_root_path, DEFAULT_META_MODULE_CATALOG_REFERENCE_PATH)
    modules = cast(list[dict[str, Any]], module_catalog["modules"])
    modules[0]["successor_module_ids"] = ["checkpoint_02_artifact_consistency_lint"]
    _write_json(repo_root_path / DEFAULT_META_MODULE_CATALOG_REFERENCE_PATH, module_catalog)

    with pytest.raises(
        MetaTestingEvidenceError,
        match="v37a scope boundary preserved requires implicit sequence law to remain absent",
    ):
        materialize_v37a_meta_intent_module_catalog_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37a_evidence_fails_closed_on_metric_key_continuity_drift(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    current_rel = _write_current_stop_gate_metrics_fixture(repo_root_path=repo_root_path)
    metrics_payload = _load_json(repo_root_path, current_rel)
    metrics = cast(dict[str, Any], metrics_payload["metrics"])
    metrics.pop(next(iter(metrics)))
    _write_json(repo_root_path / current_rel, metrics_payload)

    with pytest.raises(
        MetaTestingEvidenceError,
        match="metric key cardinality must remain frozen at 80",
    ):
        materialize_v37a_meta_intent_module_catalog_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37a_evidence_fails_closed_on_non_v65_baseline_metrics_path(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    current_rel = _write_current_stop_gate_metrics_fixture(repo_root_path=repo_root_path)

    with pytest.raises(
        MetaTestingEvidenceError,
        match="baseline_metrics_path must point to the frozen v65 closeout metrics artifact",
    ):
        materialize_v37a_meta_intent_module_catalog_evidence(
            repo_root=repo_root_path,
            baseline_metrics_path="artifacts/stop_gate/metrics_other_closeout.json",
            current_metrics_path=current_rel,
        )
