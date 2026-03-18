from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, cast

import pytest
from adeu_core_ir import (
    META_CONTROL_UPDATE_CANDIDATE_SCHEMA,
    META_CONTROL_UPDATE_MANIFEST_SCHEMA,
    MetaControlUpdateCandidate,
    MetaControlUpdateManifest,
    MetaLoopCheckpointResultManifest,
    MetaLoopConformanceReport,
    MetaLoopDriftDiagnostics,
    MetaLoopRunTrace,
    MetaLoopSequenceContract,
    MetaModuleCatalog,
    MetaTestingIntentPacket,
    assert_v37e_reference_bundle_consistent,
    canonicalize_meta_control_update_candidate_payload,
    canonicalize_meta_control_update_manifest_payload,
)
from adeu_core_ir.meta_testing import (
    V37D_RULE_DRIFT_CLASS_MAP,
    derive_v37d_overall_judgment,
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


def _load_v70_candidate() -> MetaControlUpdateCandidate:
    return MetaControlUpdateCandidate.model_validate(
        _load_json(
            _fixtures_root(70),
            "meta_control_update_candidate_arc_closeout_v65_reference.json",
        )
    )


def _load_v70_manifest() -> MetaControlUpdateManifest:
    return MetaControlUpdateManifest.model_validate(
        _load_json(
            _fixtures_root(70),
            "meta_control_update_manifest_arc_closeout_v65_reference.json",
        )
    )


def _valid_warning_finding(
    *, finding_id: str = "finding_01_reference_warning"
) -> dict[str, Any]:
    rule_id = "intent_clause_unassessed_detectable"
    return {
        "finding_id": finding_id,
        "rule_id": rule_id,
        "severity": "warning",
        "drift_class": V37D_RULE_DRIFT_CLASS_MAP[rule_id],
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


def test_v37e_reference_fixtures_validate_and_bind_to_v37a_v37b_v37c_v37d() -> None:
    assert_v37e_reference_bundle_consistent(
        intent_packet=_load_v66_intent_packet(),
        module_catalog=_load_v66_module_catalog(),
        sequence_contract=_load_v67_sequence_contract(),
        reference_run_trace=_load_v67_reference_run_trace(),
        executed_run_trace=_load_v68_executed_run_trace(),
        checkpoint_result_manifest=_load_v68_checkpoint_result_manifest(),
        drift_diagnostics=_load_v69_drift_diagnostics(),
        conformance_report=_load_v69_conformance_report(),
        control_update_candidate=_load_v70_candidate(),
        control_update_manifest=_load_v70_manifest(),
    )
    assert _load_v70_candidate().schema == META_CONTROL_UPDATE_CANDIDATE_SCHEMA
    assert _load_v70_manifest().schema == META_CONTROL_UPDATE_MANIFEST_SCHEMA


def test_v37e_reference_pair_round_trips_without_drift() -> None:
    candidate_payload = _load_json(
        _fixtures_root(70),
        "meta_control_update_candidate_arc_closeout_v65_reference.json",
    )
    manifest_payload = _load_json(
        _fixtures_root(70),
        "meta_control_update_manifest_arc_closeout_v65_reference.json",
    )

    assert (
        canonicalize_meta_control_update_candidate_payload(candidate_payload)
        == candidate_payload
    )
    assert (
        canonicalize_meta_control_update_manifest_payload(manifest_payload)
        == manifest_payload
    )


def test_v37e_candidate_rejects_non_canonical_target_surface_namespace() -> None:
    payload = _load_json(
        _fixtures_root(70),
        "meta_control_update_candidate_arc_closeout_v65_reference.json",
    )
    cast(dict[str, Any], payload)["target_surface_ref"] = (
        "lock_anchor_ref:artifacts/agent_harness/v69/evidence_inputs/"
        "v37d_drift_diagnostics_conformance_evidence_v69.json"
        "#repeated_uncompiled_drift_window_semantics_frozen"
    )

    with pytest.raises(ValidationError, match="target_surface_ref namespace"):
        MetaControlUpdateCandidate.model_validate(payload)


def test_v37e_candidate_rejects_application_friction_below_class_floor() -> None:
    payload = _load_json(
        _fixtures_root(70),
        "meta_control_update_candidate_arc_closeout_v65_reference.json",
    )
    cast(dict[str, Any], payload)["application_friction_mode"] = "review_only"

    with pytest.raises(ValidationError, match="application_friction_mode"):
        MetaControlUpdateCandidate.model_validate(payload)


def test_v37e_manifest_rejects_non_single_candidate_count() -> None:
    payload = _load_json(
        _fixtures_root(70),
        "meta_control_update_manifest_arc_closeout_v65_reference.json",
    )
    cast(list[str], payload["emitted_candidate_ids"]).append(
        "candidate_02_prompt_dispatch_lower_ranked"
    )
    cast(dict[str, Any], payload["candidate_class_counts"])["evidence_requirement"] = 2
    cast(dict[str, Any], payload)["emitted_candidate_count"] = 2

    with pytest.raises(ValidationError, match="exactly one candidate"):
        MetaControlUpdateManifest.model_validate(payload)


def test_v37e_bundle_rejects_bound_finding_ids_in_zero_finding_window() -> None:
    candidate_payload = _load_json(
        _fixtures_root(70),
        "meta_control_update_candidate_arc_closeout_v65_reference.json",
    )
    cast(dict[str, Any], candidate_payload)["bound_finding_ids"] = ["finding_01_reference_warning"]
    candidate = MetaControlUpdateCandidate.model_validate(candidate_payload)

    with pytest.raises(
        ValueError,
        match=(
            "bound_finding_ids must be empty when the accepted diagnostics artifact "
            "contains no findings"
        ),
    ):
        assert_v37e_reference_bundle_consistent(
            intent_packet=_load_v66_intent_packet(),
            module_catalog=_load_v66_module_catalog(),
            sequence_contract=_load_v67_sequence_contract(),
            reference_run_trace=_load_v67_reference_run_trace(),
            executed_run_trace=_load_v68_executed_run_trace(),
            checkpoint_result_manifest=_load_v68_checkpoint_result_manifest(),
            drift_diagnostics=_load_v69_drift_diagnostics(),
            conformance_report=_load_v69_conformance_report(),
            control_update_candidate=candidate,
            control_update_manifest=_load_v70_manifest(),
        )


def test_v37e_bundle_rejects_ineligible_bound_finding_severity() -> None:
    diagnostics_payload = _load_json(
        _fixtures_root(69),
        "meta_loop_drift_diagnostics_arc_closeout_v65_reference.json",
    )
    advisory_finding = _valid_warning_finding(finding_id="finding_02_reference_advisory")
    advisory_finding["severity"] = "advisory"
    advisory_finding["conformance_impact"] = "advisory_only"
    cast(list[dict[str, Any]], diagnostics_payload["findings"]).append(advisory_finding)
    drift_diagnostics = MetaLoopDriftDiagnostics.model_validate(diagnostics_payload)

    conformance_payload = _load_json(
        _fixtures_root(69),
        "meta_loop_conformance_report_arc_closeout_v65_reference.json",
    )
    cast(list[str], conformance_payload["supporting_finding_ids"]).append(
        advisory_finding["finding_id"]
    )
    cast(dict[str, Any], conformance_payload["severity_counts"])["advisory"] = 1
    conformance_payload["overall_judgment"] = derive_v37d_overall_judgment(
        drift_diagnostics.findings
    )
    cast(dict[str, Any], conformance_payload["derivation_metadata"])[
        "diagnostics_artifact_hash"
    ] = hashlib.sha256(
        json.dumps(
            drift_diagnostics.model_dump(mode="json", exclude_none=True),
            ensure_ascii=False,
            separators=(",", ":"),
            sort_keys=True,
        ).encode("utf-8")
    ).hexdigest()
    conformance_report = MetaLoopConformanceReport.model_validate(conformance_payload)

    candidate_payload = _load_json(
        _fixtures_root(70),
        "meta_control_update_candidate_arc_closeout_v65_reference.json",
    )
    cast(dict[str, Any], candidate_payload)["bound_finding_ids"] = [advisory_finding["finding_id"]]
    candidate = MetaControlUpdateCandidate.model_validate(candidate_payload)

    with pytest.raises(
        ValueError,
        match="bound_finding_ids must resolve only error/warning findings in v70",
    ):
        assert_v37e_reference_bundle_consistent(
            intent_packet=_load_v66_intent_packet(),
            module_catalog=_load_v66_module_catalog(),
            sequence_contract=_load_v67_sequence_contract(),
            reference_run_trace=_load_v67_reference_run_trace(),
            executed_run_trace=_load_v68_executed_run_trace(),
            checkpoint_result_manifest=_load_v68_checkpoint_result_manifest(),
            drift_diagnostics=drift_diagnostics,
            conformance_report=conformance_report,
            control_update_candidate=candidate,
            control_update_manifest=_load_v70_manifest(),
        )


def test_v37e_bundle_rejects_suppressed_lower_ranked_target_class_drift() -> None:
    manifest_payload = _load_json(
        _fixtures_root(70),
        "meta_control_update_manifest_arc_closeout_v65_reference.json",
    )
    cast(list[str], manifest_payload["suppressed_lower_ranked_target_classes"]).remove(
        "prompt_dispatch_convention"
    )
    manifest = MetaControlUpdateManifest.model_validate(manifest_payload)

    with pytest.raises(
        ValueError,
        match="suppressed_lower_ranked_target_classes",
    ):
        assert_v37e_reference_bundle_consistent(
            intent_packet=_load_v66_intent_packet(),
            module_catalog=_load_v66_module_catalog(),
            sequence_contract=_load_v67_sequence_contract(),
            reference_run_trace=_load_v67_reference_run_trace(),
            executed_run_trace=_load_v68_executed_run_trace(),
            checkpoint_result_manifest=_load_v68_checkpoint_result_manifest(),
            drift_diagnostics=_load_v69_drift_diagnostics(),
            conformance_report=_load_v69_conformance_report(),
            control_update_candidate=_load_v70_candidate(),
            control_update_manifest=manifest,
        )
