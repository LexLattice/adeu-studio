from __future__ import annotations

import json
from pathlib import Path
from typing import Any, cast

import pytest
from adeu_core_ir import (
    META_LOOP_CHECKPOINT_RESULT_MANIFEST_SCHEMA,
    META_LOOP_RUN_TRACE_SCHEMA,
    V37C_EXECUTED_TRACE_MODE,
    MetaLoopCheckpointResultManifest,
    MetaLoopRunTrace,
    MetaLoopSequenceContract,
    MetaModuleCatalog,
    MetaTestingIntentPacket,
    assert_v37c_reference_bundle_consistent,
    canonicalize_meta_loop_checkpoint_result_manifest_payload,
    canonicalize_meta_loop_run_trace_payload,
)
from adeu_ir.repo import repo_root
from pydantic import ValidationError


def _fixtures_root_v66() -> Path:
    root = repo_root(anchor=Path(__file__))
    return root / "apps" / "api" / "fixtures" / "meta_testing" / "vnext_plus66"


def _fixtures_root_v67() -> Path:
    root = repo_root(anchor=Path(__file__))
    return root / "apps" / "api" / "fixtures" / "meta_testing" / "vnext_plus67"


def _fixtures_root_v68() -> Path:
    root = repo_root(anchor=Path(__file__))
    return root / "apps" / "api" / "fixtures" / "meta_testing" / "vnext_plus68"


def _load_json(root: Path, name: str) -> dict[str, object]:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _load_v66_intent_packet() -> MetaTestingIntentPacket:
    return MetaTestingIntentPacket.model_validate(
        _load_json(
            _fixtures_root_v66(),
            "meta_testing_intent_packet_arc_closeout_v65_reference.json",
        )
    )


def _load_v66_module_catalog() -> MetaModuleCatalog:
    return MetaModuleCatalog.model_validate(
        _load_json(
            _fixtures_root_v66(),
            "meta_module_catalog_arc_closeout_v65_reference.json",
        )
    )


def _load_v67_sequence_contract() -> MetaLoopSequenceContract:
    return MetaLoopSequenceContract.model_validate(
        _load_json(
            _fixtures_root_v67(),
            "meta_loop_sequence_contract_arc_closeout_v65_reference.json",
        )
    )


def _load_v67_reference_run_trace() -> MetaLoopRunTrace:
    return MetaLoopRunTrace.model_validate(
        _load_json(
            _fixtures_root_v67(),
            "meta_loop_run_trace_arc_closeout_v65_reference.json",
        )
    )


def test_v37c_reference_fixtures_validate_and_bind_to_v37a_and_v37b() -> None:
    intent_packet = _load_v66_intent_packet()
    module_catalog = _load_v66_module_catalog()
    sequence_contract = _load_v67_sequence_contract()
    reference_run_trace = _load_v67_reference_run_trace()
    checkpoint_result_manifest = MetaLoopCheckpointResultManifest.model_validate(
        _load_json(
            _fixtures_root_v68(),
            "meta_loop_checkpoint_result_manifest_arc_closeout_v65_reference.json",
        )
    )
    executed_run_trace = MetaLoopRunTrace.model_validate(
        _load_json(
            _fixtures_root_v68(),
            "meta_loop_run_trace_arc_closeout_v65_executed_reference.json",
        )
    )

    assert_v37c_reference_bundle_consistent(
        intent_packet=intent_packet,
        module_catalog=module_catalog,
        sequence_contract=sequence_contract,
        reference_run_trace=reference_run_trace,
        executed_run_trace=executed_run_trace,
        checkpoint_result_manifest=checkpoint_result_manifest,
    )
    assert checkpoint_result_manifest.schema == META_LOOP_CHECKPOINT_RESULT_MANIFEST_SCHEMA
    assert executed_run_trace.schema == META_LOOP_RUN_TRACE_SCHEMA
    assert executed_run_trace.trace_mode == V37C_EXECUTED_TRACE_MODE


def test_v37c_reference_pair_round_trips_without_drift() -> None:
    manifest_payload = _load_json(
        _fixtures_root_v68(),
        "meta_loop_checkpoint_result_manifest_arc_closeout_v65_reference.json",
    )
    run_trace_payload = _load_json(
        _fixtures_root_v68(),
        "meta_loop_run_trace_arc_closeout_v65_executed_reference.json",
    )

    assert (
        canonicalize_meta_loop_checkpoint_result_manifest_payload(manifest_payload)
        == manifest_payload
    )
    assert canonicalize_meta_loop_run_trace_payload(run_trace_payload) == run_trace_payload


def test_v37c_run_trace_rejects_missing_manifest_ref() -> None:
    payload = _load_json(
        _fixtures_root_v68(),
        "meta_loop_run_trace_arc_closeout_v65_executed_reference.json",
    )
    payload.pop("checkpoint_result_manifest_ref")

    with pytest.raises(ValidationError, match="checkpoint_result_manifest_ref"):
        MetaLoopRunTrace.model_validate(payload)


def test_v37c_bundle_rejects_drift_from_intentional_executed_subset() -> None:
    intent_packet = _load_v66_intent_packet()
    module_catalog = _load_v66_module_catalog()
    sequence_contract = _load_v67_sequence_contract()
    reference_run_trace = _load_v67_reference_run_trace()
    checkpoint_result_manifest = MetaLoopCheckpointResultManifest.model_validate(
        _load_json(
            _fixtures_root_v68(),
            "meta_loop_checkpoint_result_manifest_arc_closeout_v65_reference.json",
        )
    )
    run_trace_payload = _load_json(
        _fixtures_root_v68(),
        "meta_loop_run_trace_arc_closeout_v65_executed_reference.json",
    )
    steps = cast(list[dict[str, Any]], run_trace_payload["steps"])
    steps[7]["step_status"] = "executed_skip"
    steps[7]["consumed_inputs"] = []
    steps[7]["emitted_outputs"] = []
    steps[7]["observed_checkpoint_result_refs"] = []
    steps[7].pop("actual_branch_outcome_ref")
    executed_run_trace = MetaLoopRunTrace.model_validate(run_trace_payload)

    with pytest.raises(
        ValueError,
        match="executed checkpoint capabilities must match the intentional v37c subset declaration",
    ):
        assert_v37c_reference_bundle_consistent(
            intent_packet=intent_packet,
            module_catalog=module_catalog,
            sequence_contract=sequence_contract,
            reference_run_trace=reference_run_trace,
            executed_run_trace=executed_run_trace,
            checkpoint_result_manifest=checkpoint_result_manifest,
        )


def test_v37c_bundle_rejects_stop_gate_executor_binding_drift() -> None:
    intent_packet = _load_v66_intent_packet()
    module_catalog = _load_v66_module_catalog()
    sequence_contract = _load_v67_sequence_contract()
    reference_run_trace = _load_v67_reference_run_trace()
    manifest_payload = _load_json(
        _fixtures_root_v68(),
        "meta_loop_checkpoint_result_manifest_arc_closeout_v65_reference.json",
    )
    rows = cast(list[dict[str, Any]], manifest_payload["checkpoint_results"])
    rows[2]["executor_binding_ref"] = "apps/api/scripts/build_quality_dashboard.py::main"
    checkpoint_result_manifest = MetaLoopCheckpointResultManifest.model_validate(manifest_payload)
    executed_run_trace = MetaLoopRunTrace.model_validate(
        _load_json(
            _fixtures_root_v68(),
            "meta_loop_run_trace_arc_closeout_v65_executed_reference.json",
        )
    )

    with pytest.raises(
        ValueError,
        match="authoritative stop-gate executor",
    ):
        assert_v37c_reference_bundle_consistent(
            intent_packet=intent_packet,
            module_catalog=module_catalog,
            sequence_contract=sequence_contract,
            reference_run_trace=reference_run_trace,
            executed_run_trace=executed_run_trace,
            checkpoint_result_manifest=checkpoint_result_manifest,
        )


def test_v37c_bundle_rejects_retried_step_without_attempted_fail_manifest_row() -> None:
    intent_packet = _load_v66_intent_packet()
    module_catalog = _load_v66_module_catalog()
    sequence_contract = _load_v67_sequence_contract()
    reference_run_trace = _load_v67_reference_run_trace()
    manifest_payload = _load_json(
        _fixtures_root_v68(),
        "meta_loop_checkpoint_result_manifest_arc_closeout_v65_reference.json",
    )
    rows = cast(list[dict[str, Any]], manifest_payload["checkpoint_results"])
    rows[3]["attempt_status"] = "attempted_pass"
    checkpoint_result_manifest = MetaLoopCheckpointResultManifest.model_validate(manifest_payload)
    executed_run_trace = MetaLoopRunTrace.model_validate(
        _load_json(
            _fixtures_root_v68(),
            "meta_loop_run_trace_arc_closeout_v65_executed_reference.json",
        )
    )

    with pytest.raises(
        ValueError,
        match="must preserve at least one attempted_fail manifest row",
    ):
        assert_v37c_reference_bundle_consistent(
            intent_packet=intent_packet,
            module_catalog=module_catalog,
            sequence_contract=sequence_contract,
            reference_run_trace=reference_run_trace,
            executed_run_trace=executed_run_trace,
            checkpoint_result_manifest=checkpoint_result_manifest,
        )


def test_v37c_bundle_rejects_missing_branch_outcome_for_executed_step() -> None:
    intent_packet = _load_v66_intent_packet()
    module_catalog = _load_v66_module_catalog()
    sequence_contract = _load_v67_sequence_contract()
    reference_run_trace = _load_v67_reference_run_trace()
    checkpoint_result_manifest = MetaLoopCheckpointResultManifest.model_validate(
        _load_json(
            _fixtures_root_v68(),
            "meta_loop_checkpoint_result_manifest_arc_closeout_v65_reference.json",
        )
    )
    run_trace_payload = _load_json(
        _fixtures_root_v68(),
        "meta_loop_run_trace_arc_closeout_v65_executed_reference.json",
    )
    steps = cast(list[dict[str, Any]], run_trace_payload["steps"])
    steps[1].pop("actual_branch_outcome_ref")
    executed_run_trace = MetaLoopRunTrace.model_validate(run_trace_payload)

    with pytest.raises(
        ValueError,
        match="must bind actual_branch_outcome_ref",
    ):
        assert_v37c_reference_bundle_consistent(
            intent_packet=intent_packet,
            module_catalog=module_catalog,
            sequence_contract=sequence_contract,
            reference_run_trace=reference_run_trace,
            executed_run_trace=executed_run_trace,
            checkpoint_result_manifest=checkpoint_result_manifest,
        )
