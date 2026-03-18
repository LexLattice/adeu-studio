from __future__ import annotations

import json
import shutil
from pathlib import Path
from typing import Any, cast

import adeu_core_ir.meta_testing_evidence as meta_testing_evidence_module
import pytest
from adeu_core_ir import (
    DEFAULT_META_CONTROL_UPDATE_CANDIDATE_REFERENCE_PATH,
    DEFAULT_META_CONTROL_UPDATE_CANDIDATE_SCHEMA_PATH,
    DEFAULT_META_CONTROL_UPDATE_MANIFEST_REFERENCE_PATH,
    DEFAULT_META_CONTROL_UPDATE_MANIFEST_SCHEMA_PATH,
    DEFAULT_META_LOOP_CHECKPOINT_RESULT_MANIFEST_REFERENCE_PATH,
    DEFAULT_META_LOOP_CHECKPOINT_RESULT_MANIFEST_SCHEMA_PATH,
    DEFAULT_META_LOOP_CONFORMANCE_REPORT_REFERENCE_PATH,
    DEFAULT_META_LOOP_CONFORMANCE_REPORT_SCHEMA_PATH,
    DEFAULT_META_LOOP_DRIFT_DIAGNOSTICS_REFERENCE_PATH,
    DEFAULT_META_LOOP_DRIFT_DIAGNOSTICS_SCHEMA_PATH,
    DEFAULT_META_LOOP_RUN_TRACE_REFERENCE_PATH,
    DEFAULT_META_LOOP_RUN_TRACE_SCHEMA_PATH,
    DEFAULT_META_LOOP_SEQUENCE_CONTRACT_REFERENCE_PATH,
    DEFAULT_META_LOOP_SEQUENCE_CONTRACT_SCHEMA_PATH,
    DEFAULT_META_MODULE_CATALOG_REFERENCE_PATH,
    DEFAULT_META_MODULE_CATALOG_SCHEMA_PATH,
    DEFAULT_META_TESTING_INTENT_PACKET_REFERENCE_PATH,
    DEFAULT_META_TESTING_INTENT_PACKET_SCHEMA_PATH,
    DEFAULT_V37A_META_INTENT_MODULE_CATALOG_EVIDENCE_PATH,
    DEFAULT_V37B_SEQUENCE_TRACE_EVIDENCE_PATH,
    DEFAULT_V37C_EXECUTED_META_LOOP_RUN_TRACE_REFERENCE_PATH,
    DEFAULT_V37C_REFERENCE_LOOP_EVIDENCE_PATH,
    DEFAULT_V65_BASELINE_METRICS_PATH,
    DEFAULT_V66_BASELINE_METRICS_PATH,
    DEFAULT_V67_BASELINE_METRICS_PATH,
    DEFAULT_V68_BASELINE_METRICS_PATH,
    DEFAULT_V69_BASELINE_METRICS_PATH,
    canonicalize_meta_loop_drift_diagnostics_payload,
    materialize_v37a_meta_intent_module_catalog_evidence,
    materialize_v37b_sequence_trace_evidence,
    materialize_v37c_reference_loop_evidence,
    materialize_v37d_drift_diagnostics_conformance_evidence,
    materialize_v37e_control_update_export_evidence,
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
        DEFAULT_META_CONTROL_UPDATE_CANDIDATE_SCHEMA_PATH,
        DEFAULT_META_CONTROL_UPDATE_MANIFEST_SCHEMA_PATH,
        DEFAULT_META_LOOP_CHECKPOINT_RESULT_MANIFEST_SCHEMA_PATH,
        DEFAULT_META_LOOP_CONFORMANCE_REPORT_SCHEMA_PATH,
        DEFAULT_META_LOOP_DRIFT_DIAGNOSTICS_SCHEMA_PATH,
        DEFAULT_META_LOOP_SEQUENCE_CONTRACT_SCHEMA_PATH,
        DEFAULT_META_LOOP_RUN_TRACE_SCHEMA_PATH,
        DEFAULT_META_TESTING_INTENT_PACKET_REFERENCE_PATH,
        DEFAULT_META_MODULE_CATALOG_REFERENCE_PATH,
        DEFAULT_META_CONTROL_UPDATE_CANDIDATE_REFERENCE_PATH,
        DEFAULT_META_CONTROL_UPDATE_MANIFEST_REFERENCE_PATH,
        DEFAULT_META_LOOP_SEQUENCE_CONTRACT_REFERENCE_PATH,
        DEFAULT_META_LOOP_RUN_TRACE_REFERENCE_PATH,
        DEFAULT_META_LOOP_CHECKPOINT_RESULT_MANIFEST_REFERENCE_PATH,
        DEFAULT_META_LOOP_CONFORMANCE_REPORT_REFERENCE_PATH,
        DEFAULT_META_LOOP_DRIFT_DIAGNOSTICS_REFERENCE_PATH,
        DEFAULT_V37C_EXECUTED_META_LOOP_RUN_TRACE_REFERENCE_PATH,
        DEFAULT_V37A_META_INTENT_MODULE_CATALOG_EVIDENCE_PATH,
        DEFAULT_V37B_SEQUENCE_TRACE_EVIDENCE_PATH,
        "artifacts/agent_harness/v65/evidence_inputs/metric_key_continuity_assertion_v65.json",
        "artifacts/agent_harness/v65/evidence_inputs/runtime_observability_comparison_v65.json",
        "artifacts/agent_harness/v65/evidence_inputs/v36e_surface_compiler_export_evidence_v65.json",
        "artifacts/agent_harness/v65/runtime/evidence/codex/copilot/v65-closeout-main-1/urm_events.ndjson",
        "artifacts/quality_dashboard_v65_closeout.json",
        DEFAULT_V66_BASELINE_METRICS_PATH,
        DEFAULT_V67_BASELINE_METRICS_PATH,
        DEFAULT_V68_BASELINE_METRICS_PATH,
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
    source_rel: str = DEFAULT_V65_BASELINE_METRICS_PATH,
    current_rel: str = "artifacts/stop_gate/metrics_v66_closeout.json",
) -> str:
    payload = _load_json(repo_root_path, source_rel)
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


def _materialize_v37b_evidence(*, repo_root_path: Path) -> dict[str, object]:
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        current_rel="artifacts/stop_gate/metrics_v67_closeout.json",
    )
    evidence = materialize_v37b_sequence_trace_evidence(
        repo_root=repo_root_path,
        current_metrics_path=current_rel,
    )
    return {
        "artifact": evidence,
        "payload": json.loads((repo_root_path / evidence.path).read_text(encoding="utf-8")),
    }


def _materialize_v37c_evidence(*, repo_root_path: Path) -> dict[str, object]:
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V67_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v68_closeout.json",
    )
    evidence = materialize_v37c_reference_loop_evidence(
        repo_root=repo_root_path,
        current_metrics_path=current_rel,
    )
    return {
        "artifact": evidence,
        "payload": json.loads((repo_root_path / evidence.path).read_text(encoding="utf-8")),
    }


def _materialize_v37d_evidence(*, repo_root_path: Path) -> dict[str, object]:
    _materialize_v37c_evidence(repo_root_path=repo_root_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V68_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v69_closeout.json",
    )
    evidence = materialize_v37d_drift_diagnostics_conformance_evidence(
        repo_root=repo_root_path,
        current_metrics_path=current_rel,
    )
    return {
        "artifact": evidence,
        "payload": json.loads((repo_root_path / evidence.path).read_text(encoding="utf-8")),
    }


def _materialize_v37e_evidence(*, repo_root_path: Path) -> dict[str, object]:
    _materialize_v37d_evidence(repo_root_path=repo_root_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V69_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v70_closeout.json",
    )
    evidence = materialize_v37e_control_update_export_evidence(
        repo_root=repo_root_path,
        current_metrics_path=current_rel,
    )
    return {
        "artifact": evidence,
        "payload": json.loads((repo_root_path / evidence.path).read_text(encoding="utf-8")),
    }


def _valid_v37d_warning_finding(
    *,
    rule_id: str = "intent_clause_unassessed_detectable",
    supporting_evidence_refs: list[str] | None = None,
) -> dict[str, object]:
    drift_class_by_rule = {
        "sequence_gap_detectable": "deontic_drift",
        "intent_clause_unassessed_detectable": "epistemic_drift",
        "unbound_reasoning_claim_detectable": "epistemic_drift",
        "checkpoint_bypass_detectable": "deontic_drift",
        "missing_artifact_evidence_detectable": "epistemic_drift",
        "prompt_substrate_mismatch_detectable": "epistemic_drift",
        "repeated_uncompiled_drift_detectable": "utility_drift",
        "operational_influence_accepted_compilation_collapse_detectable": "deontic_drift",
    }
    return {
        "finding_id": f"finding_{rule_id}",
        "rule_id": rule_id,
        "severity": "warning",
        "drift_class": drift_class_by_rule[rule_id],
        "module_refs": [
            f"{DEFAULT_META_MODULE_CATALOG_REFERENCE_PATH}#modules/checkpoint_01_bundle_lint"
        ],
        "intent_clause_refs": [f"{DEFAULT_META_TESTING_INTENT_PACKET_REFERENCE_PATH}#objective"],
        "reference_trace_refs": [
            f"{DEFAULT_META_LOOP_RUN_TRACE_REFERENCE_PATH}#steps/step_02_bundle_lint"
        ],
        "executed_trace_refs": [
            f"{DEFAULT_V37C_EXECUTED_META_LOOP_RUN_TRACE_REFERENCE_PATH}#steps/step_02_bundle_lint"
        ],
        "checkpoint_result_refs": [
            f"{DEFAULT_META_LOOP_CHECKPOINT_RESULT_MANIFEST_REFERENCE_PATH}#checkpoint_results/result_step_02_bundle_lint_attempt_01"
        ],
        "supporting_evidence_refs": supporting_evidence_refs
        or [DEFAULT_V37C_REFERENCE_LOOP_EVIDENCE_PATH],
        "conformance_impact": "needs_review",
    }


def _valid_v37d_advisory_finding(
    *,
    rule_id: str = "intent_clause_unassessed_detectable",
) -> dict[str, object]:
    finding = _valid_v37d_warning_finding(rule_id=rule_id)
    finding["finding_id"] = f"finding_advisory_{rule_id}"
    finding["severity"] = "advisory"
    finding["conformance_impact"] = "advisory_only"
    return finding


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


def test_materialize_v37b_sequence_trace_evidence_is_deterministic(tmp_path: Path) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)

    first = _materialize_v37b_evidence(repo_root_path=repo_root_path)
    second = _materialize_v37b_evidence(repo_root_path=repo_root_path)

    assert first["artifact"].hash == second["artifact"].hash
    assert first["payload"] == second["payload"]
    assert first["payload"]["schema"] == "v37b_sequence_trace_evidence@1"


def test_materialize_v37b_evidence_fails_closed_on_v37a_tuple_drift(tmp_path: Path) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        current_rel="artifacts/stop_gate/metrics_v67_closeout.json",
    )
    sequence_contract = _load_json(
        repo_root_path,
        DEFAULT_META_LOOP_SEQUENCE_CONTRACT_REFERENCE_PATH,
    )
    sequence_contract["intent_packet_id"] = "other_intent"  # type: ignore[index]
    _write_json(
        repo_root_path / DEFAULT_META_LOOP_SEQUENCE_CONTRACT_REFERENCE_PATH,
        sequence_contract,
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match="reference instance binding mismatch for intent_packet_id",
    ):
        materialize_v37b_sequence_trace_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37b_evidence_fails_closed_on_unaccepted_checkpoint_result_ref(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        current_rel="artifacts/stop_gate/metrics_v67_closeout.json",
    )
    run_trace = _load_json(repo_root_path, DEFAULT_META_LOOP_RUN_TRACE_REFERENCE_PATH)
    steps = cast(list[dict[str, Any]], run_trace["steps"])
    steps[1]["observed_checkpoint_result_refs"] = ["AGENTS.md"]
    _write_json(repo_root_path / DEFAULT_META_LOOP_RUN_TRACE_REFERENCE_PATH, run_trace)

    with pytest.raises(
        MetaTestingEvidenceError,
        match="observed_checkpoint_result_refs must stay under the 'artifacts/' subtree",
    ):
        materialize_v37b_sequence_trace_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37b_evidence_fails_closed_on_scope_boundary_bleed(tmp_path: Path) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        current_rel="artifacts/stop_gate/metrics_v67_closeout.json",
    )
    sequence_contract = _load_json(
        repo_root_path,
        DEFAULT_META_LOOP_SEQUENCE_CONTRACT_REFERENCE_PATH,
    )
    steps = cast(list[dict[str, Any]], sequence_contract["steps"])
    outputs = cast(list[str], steps[4]["expected_outputs"])
    outputs.append("meta_loop_checkpoint_result_manifest@1")
    outputs.sort()
    _write_json(
        repo_root_path / DEFAULT_META_LOOP_SEQUENCE_CONTRACT_REFERENCE_PATH,
        sequence_contract,
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match="v37b scope boundary preserved requires v37c/v37d/v37e surfaces to remain absent",
    ):
        materialize_v37b_sequence_trace_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37b_evidence_fails_closed_on_threshold_collapse(tmp_path: Path) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        current_rel="artifacts/stop_gate/metrics_v67_closeout.json",
    )
    run_trace = _load_json(repo_root_path, DEFAULT_META_LOOP_RUN_TRACE_REFERENCE_PATH)
    steps = cast(list[dict[str, Any]], run_trace["steps"])
    steps[0]["accepted_compilation_occurred"] = True
    _write_json(repo_root_path / DEFAULT_META_LOOP_RUN_TRACE_REFERENCE_PATH, run_trace)

    with pytest.raises(
        MetaTestingEvidenceError,
        match="reference_not_executed traces must keep accepted_compilation_occurred = false",
    ):
        materialize_v37b_sequence_trace_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37b_evidence_fails_closed_on_non_v66_baseline_metrics_path(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        current_rel="artifacts/stop_gate/metrics_v67_closeout.json",
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match="baseline_metrics_path must point to the frozen v66 closeout metrics artifact",
    ):
        materialize_v37b_sequence_trace_evidence(
            repo_root=repo_root_path,
            baseline_metrics_path="artifacts/stop_gate/metrics_other_closeout.json",
            current_metrics_path=current_rel,
        )


def test_materialize_v37b_evidence_fails_closed_on_metric_key_continuity_drift(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        current_rel="artifacts/stop_gate/metrics_v67_closeout.json",
    )
    metrics_payload = _load_json(repo_root_path, current_rel)
    metrics = cast(dict[str, Any], metrics_payload["metrics"])
    metrics["new_metric_key"] = 100.0
    _write_json(repo_root_path / current_rel, metrics_payload)

    with pytest.raises(
        MetaTestingEvidenceError,
        match="metric key cardinality must remain frozen at 80",
    ):
        materialize_v37b_sequence_trace_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37c_reference_loop_evidence_is_deterministic(tmp_path: Path) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)

    first = _materialize_v37c_evidence(repo_root_path=repo_root_path)
    second = _materialize_v37c_evidence(repo_root_path=repo_root_path)

    assert first["artifact"].hash == second["artifact"].hash
    assert first["payload"] == second["payload"]
    assert first["payload"]["schema"] == "v37c_reference_loop_evidence@1"


def test_materialize_v37c_evidence_fails_closed_on_non_v67_baseline_metrics_path(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V67_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v68_closeout.json",
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match="baseline_metrics_path must point to the frozen v67 closeout metrics artifact",
    ):
        materialize_v37c_reference_loop_evidence(
            repo_root=repo_root_path,
            baseline_metrics_path="artifacts/stop_gate/metrics_other_closeout.json",
            current_metrics_path=current_rel,
        )


def test_materialize_v37c_evidence_fails_closed_on_wrong_trace_mode(tmp_path: Path) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V67_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v68_closeout.json",
    )
    run_trace = _load_json(
        repo_root_path,
        DEFAULT_V37C_EXECUTED_META_LOOP_RUN_TRACE_REFERENCE_PATH,
    )
    run_trace["trace_mode"] = "reference_not_executed"
    _write_json(
        repo_root_path / DEFAULT_V37C_EXECUTED_META_LOOP_RUN_TRACE_REFERENCE_PATH,
        run_trace,
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match="executed_meta_loop_run_trace_reference_path must use 'executed_reference_run'",
    ):
        materialize_v37c_reference_loop_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37c_evidence_fails_closed_on_missing_bound_executor_in_repo(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V67_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v68_closeout.json",
    )
    (repo_root_path / "apps/api/scripts/build_stop_gate_metrics.py").unlink()

    with pytest.raises(
        MetaTestingEvidenceError,
        match=(
            "checkpoint_results\\[result_step_05_stop_gate_metrics_build_attempt_01\\]"
            "\\.executor_binding_ref does not exist"
        ),
    ):
        materialize_v37c_reference_loop_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37c_evidence_fails_closed_on_output_artifact_hash_drift(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V67_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v68_closeout.json",
    )
    manifest = _load_json(
        repo_root_path,
        DEFAULT_META_LOOP_CHECKPOINT_RESULT_MANIFEST_REFERENCE_PATH,
    )
    rows = cast(list[dict[str, Any]], manifest["checkpoint_results"])
    output_artifacts = cast(list[dict[str, Any]], rows[1]["output_artifacts"])
    output_artifacts[0]["artifact_sha256"] = "0" * 64
    _write_json(
        repo_root_path / DEFAULT_META_LOOP_CHECKPOINT_RESULT_MANIFEST_REFERENCE_PATH,
        manifest,
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match=(
            "output_artifacts\\[quality_dashboard_json\\]\\.artifact_sha256 must match "
            "repo file bytes"
        ),
    ):
        materialize_v37c_reference_loop_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37c_evidence_fails_closed_on_scope_boundary_bleed(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V67_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v68_closeout.json",
    )
    sequence_contract = _load_json(
        repo_root_path,
        DEFAULT_META_LOOP_SEQUENCE_CONTRACT_REFERENCE_PATH,
    )
    reference_run_trace = _load_json(repo_root_path, DEFAULT_META_LOOP_RUN_TRACE_REFERENCE_PATH)
    executed_run_trace = _load_json(
        repo_root_path,
        DEFAULT_V37C_EXECUTED_META_LOOP_RUN_TRACE_REFERENCE_PATH,
    )
    for payload in (sequence_contract, reference_run_trace, executed_run_trace):
        steps = cast(list[dict[str, Any]], payload["steps"])
        output_key = "expected_outputs" if payload is sequence_contract else "emitted_outputs"
        outputs = cast(list[str], steps[8][output_key])
        outputs.append("meta_loop_drift_diagnostics@1")
        outputs.sort()
    _write_json(
        repo_root_path / DEFAULT_META_LOOP_SEQUENCE_CONTRACT_REFERENCE_PATH,
        sequence_contract,
    )
    _write_json(repo_root_path / DEFAULT_META_LOOP_RUN_TRACE_REFERENCE_PATH, reference_run_trace)
    _write_json(
        repo_root_path / DEFAULT_V37C_EXECUTED_META_LOOP_RUN_TRACE_REFERENCE_PATH,
        executed_run_trace,
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match="v37c scope boundary preserved requires v37d/v37e surfaces to remain absent",
    ):
        materialize_v37c_reference_loop_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37c_evidence_fails_closed_on_missing_failed_attempt_row(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V67_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v68_closeout.json",
    )
    manifest = _load_json(
        repo_root_path,
        DEFAULT_META_LOOP_CHECKPOINT_RESULT_MANIFEST_REFERENCE_PATH,
    )
    rows = cast(list[dict[str, Any]], manifest["checkpoint_results"])
    rows[3]["attempt_status"] = "attempted_pass"
    _write_json(
        repo_root_path / DEFAULT_META_LOOP_CHECKPOINT_RESULT_MANIFEST_REFERENCE_PATH,
        manifest,
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match="must preserve at least one attempted_fail manifest row",
    ):
        materialize_v37c_reference_loop_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37d_drift_diagnostics_conformance_evidence_is_deterministic(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)

    first = _materialize_v37d_evidence(repo_root_path=repo_root_path)
    second = _materialize_v37d_evidence(repo_root_path=repo_root_path)

    assert first["artifact"].hash == second["artifact"].hash
    assert first["payload"] == second["payload"]
    assert first["payload"]["schema"] == "v37d_drift_diagnostics_conformance_evidence@1"


def test_materialize_v37d_evidence_fails_closed_on_non_v68_baseline_metrics_path(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v37c_evidence(repo_root_path=repo_root_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V68_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v69_closeout.json",
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match="baseline_metrics_path must point to the frozen v68 closeout metrics artifact",
    ):
        materialize_v37d_drift_diagnostics_conformance_evidence(
            repo_root=repo_root_path,
            baseline_metrics_path="artifacts/stop_gate/metrics_other_closeout.json",
            current_metrics_path=current_rel,
        )


def test_materialize_v37d_evidence_fails_closed_on_v37c_tuple_drift(tmp_path: Path) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v37c_evidence(repo_root_path=repo_root_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V68_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v69_closeout.json",
    )
    conformance_report = _load_json(
        repo_root_path,
        DEFAULT_META_LOOP_CONFORMANCE_REPORT_REFERENCE_PATH,
    )
    conformance_report["reference_instance_id"] = "other_reference"
    _write_json(
        repo_root_path / DEFAULT_META_LOOP_CONFORMANCE_REPORT_REFERENCE_PATH,
        conformance_report,
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match="reference instance binding mismatch for reference_instance_id",
    ):
        materialize_v37d_drift_diagnostics_conformance_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37d_evidence_fails_closed_on_diagnostics_derivation_drift(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v37c_evidence(repo_root_path=repo_root_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V68_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v69_closeout.json",
    )
    conformance_report = _load_json(
        repo_root_path,
        DEFAULT_META_LOOP_CONFORMANCE_REPORT_REFERENCE_PATH,
    )
    derivation_metadata = cast(dict[str, Any], conformance_report["derivation_metadata"])
    derivation_metadata["diagnostics_artifact_hash"] = "0" * 64
    _write_json(
        repo_root_path / DEFAULT_META_LOOP_CONFORMANCE_REPORT_REFERENCE_PATH,
        conformance_report,
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match=(
            "conformance report derivation_metadata\\.diagnostics_artifact_hash must match "
            "the accepted diagnostics artifact"
        ),
    ):
        materialize_v37d_drift_diagnostics_conformance_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37d_evidence_fails_closed_on_worker_or_event_truth_substitution(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v37c_evidence(repo_root_path=repo_root_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V68_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v69_closeout.json",
    )
    diagnostics = _load_json(
        repo_root_path,
        DEFAULT_META_LOOP_DRIFT_DIAGNOSTICS_REFERENCE_PATH,
    )
    findings = cast(list[dict[str, Any]], diagnostics["findings"])
    findings.append(
        _valid_v37d_warning_finding(
            supporting_evidence_refs=[
                "artifacts/agent_harness/v68/runtime/evidence/codex/copilot/"
                "v68-closeout-main-1/urm_events.ndjson"
            ]
        )
    )
    _write_json(
        repo_root_path / DEFAULT_META_LOOP_DRIFT_DIAGNOSTICS_REFERENCE_PATH,
        diagnostics,
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match="must not treat event streams or worker prose as authoritative truth",
    ):
        materialize_v37d_drift_diagnostics_conformance_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37d_evidence_fails_closed_on_scope_boundary_bleed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v37c_evidence(repo_root_path=repo_root_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V68_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v69_closeout.json",
    )
    diagnostics = _load_json(
        repo_root_path,
        DEFAULT_META_LOOP_DRIFT_DIAGNOSTICS_REFERENCE_PATH,
    )
    findings = cast(list[dict[str, Any]], diagnostics["findings"])
    findings.append(_valid_v37d_warning_finding())
    _write_json(
        repo_root_path / DEFAULT_META_LOOP_DRIFT_DIAGNOSTICS_REFERENCE_PATH,
        diagnostics,
    )
    canonical_diagnostics = canonicalize_meta_loop_drift_diagnostics_payload(diagnostics)
    conformance_report = _load_json(
        repo_root_path,
        DEFAULT_META_LOOP_CONFORMANCE_REPORT_REFERENCE_PATH,
    )
    conformance_report["overall_judgment"] = "needs_review"
    conformance_report["supporting_finding_ids"] = ["finding_intent_clause_unassessed_detectable"]
    conformance_report["severity_counts"] = {"error": 0, "warning": 1, "advisory": 0}
    conformance_report["warning_rule_families"] = ["intent_clause_unassessed_detectable"]
    derivation_metadata = cast(dict[str, Any], conformance_report["derivation_metadata"])
    derivation_metadata["diagnostics_artifact_hash"] = (
        meta_testing_evidence_module._sha256_canonical_json(canonical_diagnostics)
    )
    original_surface_id = meta_testing_evidence_module._supporting_evidence_surface_id

    def _forced_surface_id(ref: str) -> str | None:
        if ref == DEFAULT_V37C_REFERENCE_LOOP_EVIDENCE_PATH:
            return "meta_control_update_candidate@1"
        return original_surface_id(ref)

    _write_json(
        repo_root_path / DEFAULT_META_LOOP_CONFORMANCE_REPORT_REFERENCE_PATH,
        conformance_report,
    )
    monkeypatch.setattr(
        meta_testing_evidence_module,
        "_supporting_evidence_surface_id",
        _forced_surface_id,
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match="v37d scope boundary preserved requires v37e surfaces to remain absent",
    ):
        materialize_v37d_drift_diagnostics_conformance_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37d_evidence_fails_closed_on_repeated_drift_overclaim(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v37c_evidence(repo_root_path=repo_root_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V68_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v69_closeout.json",
    )
    diagnostics = _load_json(
        repo_root_path,
        DEFAULT_META_LOOP_DRIFT_DIAGNOSTICS_REFERENCE_PATH,
    )
    findings = cast(list[dict[str, Any]], diagnostics["findings"])
    findings.append(_valid_v37d_warning_finding(rule_id="repeated_uncompiled_drift_detectable"))
    _write_json(
        repo_root_path / DEFAULT_META_LOOP_DRIFT_DIAGNOSTICS_REFERENCE_PATH,
        diagnostics,
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match=(
            "repeated_uncompiled_drift_detectable requires >=2 accepted runs for a "
            "positive finding in the first v37d reference artifact"
        ),
    ):
        materialize_v37d_drift_diagnostics_conformance_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37e_control_update_export_evidence_is_deterministic(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)

    first = _materialize_v37e_evidence(repo_root_path=repo_root_path)
    second = _materialize_v37e_evidence(repo_root_path=repo_root_path)

    assert first["artifact"].hash == second["artifact"].hash
    assert first["payload"] == second["payload"]
    assert first["payload"]["schema"] == "v37e_control_update_export_evidence@1"


def test_materialize_v37e_evidence_fails_closed_on_non_v69_baseline_metrics_path(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v37d_evidence(repo_root_path=repo_root_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V69_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v70_closeout.json",
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match="baseline_metrics_path must point to the frozen v69 closeout metrics artifact",
    ):
        materialize_v37e_control_update_export_evidence(
            repo_root=repo_root_path,
            baseline_metrics_path="artifacts/stop_gate/metrics_other_closeout.json",
            current_metrics_path=current_rel,
        )


def test_materialize_v37e_evidence_fails_closed_on_v37d_tuple_drift(tmp_path: Path) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v37d_evidence(repo_root_path=repo_root_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V69_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v70_closeout.json",
    )
    candidate = _load_json(
        repo_root_path,
        DEFAULT_META_CONTROL_UPDATE_CANDIDATE_REFERENCE_PATH,
    )
    candidate["reference_instance_id"] = "other_reference"
    _write_json(
        repo_root_path / DEFAULT_META_CONTROL_UPDATE_CANDIDATE_REFERENCE_PATH,
        candidate,
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match="reference instance binding mismatch for reference_instance_id",
    ):
        materialize_v37e_control_update_export_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37e_evidence_fails_closed_on_manifest_cardinality_drift(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v37d_evidence(repo_root_path=repo_root_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V69_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v70_closeout.json",
    )
    manifest = _load_json(
        repo_root_path,
        DEFAULT_META_CONTROL_UPDATE_MANIFEST_REFERENCE_PATH,
    )
    manifest["emitted_candidate_count"] = 2
    _write_json(
        repo_root_path / DEFAULT_META_CONTROL_UPDATE_MANIFEST_REFERENCE_PATH,
        manifest,
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match="emitted_candidate_count must match the number of emitted_candidate_ids",
    ):
        materialize_v37e_control_update_export_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37e_evidence_fails_closed_on_advisory_bound_finding(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v37d_evidence(repo_root_path=repo_root_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V69_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v70_closeout.json",
    )
    diagnostics = _load_json(
        repo_root_path,
        DEFAULT_META_LOOP_DRIFT_DIAGNOSTICS_REFERENCE_PATH,
    )
    findings = cast(list[dict[str, Any]], diagnostics["findings"])
    advisory_finding = _valid_v37d_advisory_finding()
    findings.append(advisory_finding)
    _write_json(
        repo_root_path / DEFAULT_META_LOOP_DRIFT_DIAGNOSTICS_REFERENCE_PATH,
        diagnostics,
    )
    canonical_diagnostics = canonicalize_meta_loop_drift_diagnostics_payload(diagnostics)
    conformance_report = _load_json(
        repo_root_path,
        DEFAULT_META_LOOP_CONFORMANCE_REPORT_REFERENCE_PATH,
    )
    conformance_report["supporting_finding_ids"] = [advisory_finding["finding_id"]]
    conformance_report["severity_counts"] = {"error": 0, "warning": 0, "advisory": 1}
    derivation_metadata = cast(dict[str, Any], conformance_report["derivation_metadata"])
    derivation_metadata["diagnostics_artifact_hash"] = (
        meta_testing_evidence_module._sha256_canonical_json(canonical_diagnostics)
    )
    _write_json(
        repo_root_path / DEFAULT_META_LOOP_CONFORMANCE_REPORT_REFERENCE_PATH,
        conformance_report,
    )
    candidate = _load_json(
        repo_root_path,
        DEFAULT_META_CONTROL_UPDATE_CANDIDATE_REFERENCE_PATH,
    )
    candidate["bound_finding_ids"] = [advisory_finding["finding_id"]]
    _write_json(
        repo_root_path / DEFAULT_META_CONTROL_UPDATE_CANDIDATE_REFERENCE_PATH,
        candidate,
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match="bound_finding_ids must resolve only error/warning findings in v70",
    ):
        materialize_v37e_control_update_export_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37e_evidence_fails_closed_on_numeric_claim_drift(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v37d_evidence(repo_root_path=repo_root_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V69_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v70_closeout.json",
    )
    candidate = _load_json(
        repo_root_path,
        DEFAULT_META_CONTROL_UPDATE_CANDIDATE_REFERENCE_PATH,
    )
    candidate["expected_drift_reduction_claim"] = "Reduce repeated-drift ambiguity by 2 steps."
    _write_json(
        repo_root_path / DEFAULT_META_CONTROL_UPDATE_CANDIDATE_REFERENCE_PATH,
        candidate,
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match="expected_drift_reduction_claim must remain qualitative and non-numeric",
    ):
        materialize_v37e_control_update_export_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37e_evidence_fails_closed_on_friction_floor_drift(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v37d_evidence(repo_root_path=repo_root_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V69_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v70_closeout.json",
    )
    candidate = _load_json(
        repo_root_path,
        DEFAULT_META_CONTROL_UPDATE_CANDIDATE_REFERENCE_PATH,
    )
    candidate["application_friction_mode"] = "review_only"
    _write_json(
        repo_root_path / DEFAULT_META_CONTROL_UPDATE_CANDIDATE_REFERENCE_PATH,
        candidate,
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match="application_friction_mode must respect the frozen first-family minimum",
    ):
        materialize_v37e_control_update_export_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37e_evidence_fails_closed_on_raw_patch_payload_field(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v37d_evidence(repo_root_path=repo_root_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V69_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v70_closeout.json",
    )
    candidate = _load_json(
        repo_root_path,
        DEFAULT_META_CONTROL_UPDATE_CANDIDATE_REFERENCE_PATH,
    )
    candidate["raw_patch_payload"] = "diff --git a/x b/x"
    _write_json(
        repo_root_path / DEFAULT_META_CONTROL_UPDATE_CANDIDATE_REFERENCE_PATH,
        candidate,
    )

    with pytest.raises(
        MetaTestingEvidenceError,
        match=(
            "meta_control_update_candidate_reference_path must not carry raw patch "
            "or shell payload fields"
        ),
    ):
        materialize_v37e_control_update_export_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )


def test_materialize_v37e_evidence_fails_closed_on_metric_key_drift(
    tmp_path: Path,
) -> None:
    repo_root_path = _build_temp_repo_fixture_tree(tmp_path)
    _materialize_v37d_evidence(repo_root_path=repo_root_path)
    current_rel = _write_current_stop_gate_metrics_fixture(
        repo_root_path=repo_root_path,
        source_rel=DEFAULT_V69_BASELINE_METRICS_PATH,
        current_rel="artifacts/stop_gate/metrics_v70_closeout.json",
    )
    current_metrics = _load_json(repo_root_path, current_rel)
    metrics = cast(dict[str, Any], current_metrics["metrics"])
    metrics["meta_testing.synthetic_drift"] = 1
    _write_json(repo_root_path / current_rel, current_metrics)

    with pytest.raises(
        MetaTestingEvidenceError,
        match=(
            "metric key cardinality must remain frozen at "
            f"{meta_testing_evidence_module.EXPECTED_METRIC_KEY_CARDINALITY}"
        ),
    ):
        materialize_v37e_control_update_export_evidence(
            repo_root=repo_root_path,
            current_metrics_path=current_rel,
        )
