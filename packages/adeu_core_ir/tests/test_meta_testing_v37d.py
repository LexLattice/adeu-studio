from __future__ import annotations

import json
from pathlib import Path
from typing import Any, cast

import pytest
from adeu_core_ir import (
    META_LOOP_CONFORMANCE_REPORT_SCHEMA,
    META_LOOP_DRIFT_DIAGNOSTICS_SCHEMA,
    MetaLoopCheckpointResultManifest,
    MetaLoopConformanceReport,
    MetaLoopDriftDiagnostics,
    MetaLoopRunTrace,
    MetaLoopSequenceContract,
    MetaModuleCatalog,
    MetaTestingIntentPacket,
    assert_v37d_reference_bundle_consistent,
    canonicalize_meta_loop_conformance_report_payload,
    canonicalize_meta_loop_drift_diagnostics_payload,
)
from adeu_ir.repo import repo_root
from pydantic import ValidationError


def _fixtures_root(version: int) -> Path:
    root = repo_root(anchor=Path(__file__))
    return root / "apps" / "api" / "fixtures" / "meta_testing" / f"vnext_plus{version}"


def _load_json(root: Path, name: str) -> dict[str, object]:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _load_v66_intent_packet() -> MetaTestingIntentPacket:
    return MetaTestingIntentPacket.model_validate(
        _load_json(
            _fixtures_root(66),
            "meta_testing_intent_packet_arc_closeout_v65_reference.json",
        )
    )


def _load_v66_module_catalog() -> MetaModuleCatalog:
    return MetaModuleCatalog.model_validate(
        _load_json(
            _fixtures_root(66),
            "meta_module_catalog_arc_closeout_v65_reference.json",
        )
    )


def _load_v67_sequence_contract() -> MetaLoopSequenceContract:
    return MetaLoopSequenceContract.model_validate(
        _load_json(
            _fixtures_root(67),
            "meta_loop_sequence_contract_arc_closeout_v65_reference.json",
        )
    )


def _load_v67_reference_run_trace() -> MetaLoopRunTrace:
    return MetaLoopRunTrace.model_validate(
        _load_json(
            _fixtures_root(67),
            "meta_loop_run_trace_arc_closeout_v65_reference.json",
        )
    )


def _load_v68_checkpoint_result_manifest() -> MetaLoopCheckpointResultManifest:
    return MetaLoopCheckpointResultManifest.model_validate(
        _load_json(
            _fixtures_root(68),
            "meta_loop_checkpoint_result_manifest_arc_closeout_v65_reference.json",
        )
    )


def _load_v68_executed_run_trace() -> MetaLoopRunTrace:
    return MetaLoopRunTrace.model_validate(
        _load_json(
            _fixtures_root(68),
            "meta_loop_run_trace_arc_closeout_v65_executed_reference.json",
        )
    )


def _load_v69_drift_diagnostics() -> MetaLoopDriftDiagnostics:
    return MetaLoopDriftDiagnostics.model_validate(
        _load_json(
            _fixtures_root(69),
            "meta_loop_drift_diagnostics_arc_closeout_v65_reference.json",
        )
    )


def _load_v69_conformance_report() -> MetaLoopConformanceReport:
    return MetaLoopConformanceReport.model_validate(
        _load_json(
            _fixtures_root(69),
            "meta_loop_conformance_report_arc_closeout_v65_reference.json",
        )
    )


def _valid_warning_finding(
    *, rule_id: str = "intent_clause_unassessed_detectable"
) -> dict[str, Any]:
    return {
        "finding_id": "finding_01_reference_warning",
        "rule_id": rule_id,
        "severity": "warning",
        "drift_class": "epistemic_drift",
        "module_refs": [
            "apps/api/fixtures/meta_testing/vnext_plus66/"
            "meta_module_catalog_arc_closeout_v65_reference.json"
            "#modules/reasoning_01_meta_intent_interpreter"
        ],
        "intent_clause_refs": [
            "apps/api/fixtures/meta_testing/vnext_plus66/"
            "meta_testing_intent_packet_arc_closeout_v65_reference.json#success_condition"
        ],
        "reference_trace_refs": [
            "apps/api/fixtures/meta_testing/vnext_plus67/"
            "meta_loop_run_trace_arc_closeout_v65_reference.json"
            "#steps/step_01_meta_intent_interpretation"
        ],
        "executed_trace_refs": [
            "apps/api/fixtures/meta_testing/vnext_plus68/"
            "meta_loop_run_trace_arc_closeout_v65_executed_reference.json"
            "#steps/step_09_reference_bundle_guard"
        ],
        "checkpoint_result_refs": [
            "apps/api/fixtures/meta_testing/vnext_plus68/"
            "meta_loop_checkpoint_result_manifest_arc_closeout_v65_reference.json"
            "#checkpoint_results/result_step_09_reference_bundle_guard_attempt_01"
        ],
        "supporting_evidence_refs": [
            "artifacts/agent_harness/v68/evidence_inputs/v37c_reference_loop_evidence_v68.json"
        ],
        "conformance_impact": "needs_review",
    }


def test_v37d_reference_fixtures_validate_and_bind_to_v37a_v37b_v37c() -> None:
    assert_v37d_reference_bundle_consistent(
        intent_packet=_load_v66_intent_packet(),
        module_catalog=_load_v66_module_catalog(),
        sequence_contract=_load_v67_sequence_contract(),
        reference_run_trace=_load_v67_reference_run_trace(),
        executed_run_trace=_load_v68_executed_run_trace(),
        checkpoint_result_manifest=_load_v68_checkpoint_result_manifest(),
        drift_diagnostics=_load_v69_drift_diagnostics(),
        conformance_report=_load_v69_conformance_report(),
    )
    assert _load_v69_drift_diagnostics().schema == META_LOOP_DRIFT_DIAGNOSTICS_SCHEMA
    assert _load_v69_conformance_report().schema == META_LOOP_CONFORMANCE_REPORT_SCHEMA


def test_v37d_reference_pair_round_trips_without_drift() -> None:
    diagnostics_payload = _load_json(
        _fixtures_root(69),
        "meta_loop_drift_diagnostics_arc_closeout_v65_reference.json",
    )
    conformance_payload = _load_json(
        _fixtures_root(69),
        "meta_loop_conformance_report_arc_closeout_v65_reference.json",
    )

    assert (
        canonicalize_meta_loop_drift_diagnostics_payload(diagnostics_payload)
        == diagnostics_payload
    )
    assert (
        canonicalize_meta_loop_conformance_report_payload(conformance_payload)
        == conformance_payload
    )


def test_v37d_diagnostics_reject_missing_checkpoint_result_refs() -> None:
    payload = _load_json(
        _fixtures_root(69),
        "meta_loop_drift_diagnostics_arc_closeout_v65_reference.json",
    )
    findings = cast(list[dict[str, Any]], payload["findings"])
    finding = _valid_warning_finding()
    finding["checkpoint_result_refs"] = []
    findings.append(finding)

    with pytest.raises(ValidationError, match="checkpoint_result_refs"):
        MetaLoopDriftDiagnostics.model_validate(payload)


def test_v37d_bundle_rejects_conformance_aggregation_drift() -> None:
    diagnostics_payload = _load_json(
        _fixtures_root(69),
        "meta_loop_drift_diagnostics_arc_closeout_v65_reference.json",
    )
    cast(list[dict[str, Any]], diagnostics_payload["findings"]).append(_valid_warning_finding())
    drift_diagnostics = MetaLoopDriftDiagnostics.model_validate(diagnostics_payload)

    conformance_report = _load_v69_conformance_report()

    with pytest.raises(
        ValueError,
        match="overall_judgment",
    ):
        assert_v37d_reference_bundle_consistent(
            intent_packet=_load_v66_intent_packet(),
            module_catalog=_load_v66_module_catalog(),
            sequence_contract=_load_v67_sequence_contract(),
            reference_run_trace=_load_v67_reference_run_trace(),
            executed_run_trace=_load_v68_executed_run_trace(),
            checkpoint_result_manifest=_load_v68_checkpoint_result_manifest(),
            drift_diagnostics=drift_diagnostics,
            conformance_report=conformance_report,
        )


def test_v37d_bundle_rejects_positive_repeated_uncompiled_drift_in_single_run_window() -> None:
    diagnostics_payload = _load_json(
        _fixtures_root(69),
        "meta_loop_drift_diagnostics_arc_closeout_v65_reference.json",
    )
    finding = _valid_warning_finding(rule_id="repeated_uncompiled_drift_detectable")
    finding["finding_id"] = "finding_01_repeated_uncompiled_drift"
    finding["severity"] = "advisory"
    finding["conformance_impact"] = "advisory_only"
    finding["drift_class"] = "utility_drift"
    cast(list[dict[str, Any]], diagnostics_payload["findings"]).append(finding)
    drift_diagnostics = MetaLoopDriftDiagnostics.model_validate(diagnostics_payload)

    conformance_payload = _load_json(
        _fixtures_root(69),
        "meta_loop_conformance_report_arc_closeout_v65_reference.json",
    )
    conformance_payload["supporting_finding_ids"] = [
        "finding_01_repeated_uncompiled_drift"
    ]
    conformance_payload["severity_counts"] = {"error": 0, "warning": 0, "advisory": 1}
    conformance_report = MetaLoopConformanceReport.model_validate(conformance_payload)

    with pytest.raises(
        ValueError,
        match="requires >=2 accepted runs",
    ):
        assert_v37d_reference_bundle_consistent(
            intent_packet=_load_v66_intent_packet(),
            module_catalog=_load_v66_module_catalog(),
            sequence_contract=_load_v67_sequence_contract(),
            reference_run_trace=_load_v67_reference_run_trace(),
            executed_run_trace=_load_v68_executed_run_trace(),
            checkpoint_result_manifest=_load_v68_checkpoint_result_manifest(),
            drift_diagnostics=drift_diagnostics,
            conformance_report=conformance_report,
        )
