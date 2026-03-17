from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_core_ir import (
    META_LOOP_RUN_TRACE_SCHEMA,
    META_LOOP_SEQUENCE_CONTRACT_SCHEMA,
    V37B_REFERENCE_TRACE_MODE,
    MetaLoopRunTrace,
    MetaLoopSequenceContract,
    MetaModuleCatalog,
    MetaTestingIntentPacket,
    assert_v37b_reference_bundle_consistent,
    assert_v37b_reference_instance_binding,
    canonicalize_meta_loop_run_trace_payload,
    canonicalize_meta_loop_sequence_contract_payload,
)
from adeu_ir.repo import repo_root
from pydantic import ValidationError


def _fixtures_root_v66() -> Path:
    root = repo_root(anchor=Path(__file__))
    return root / "apps" / "api" / "fixtures" / "meta_testing" / "vnext_plus66"


def _fixtures_root_v67() -> Path:
    root = repo_root(anchor=Path(__file__))
    return root / "apps" / "api" / "fixtures" / "meta_testing" / "vnext_plus67"


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


def test_v37b_reference_pair_fixtures_validate_and_bind_to_v37a() -> None:
    intent_packet = _load_v66_intent_packet()
    module_catalog = _load_v66_module_catalog()
    sequence_contract = MetaLoopSequenceContract.model_validate(
        _load_json(
            _fixtures_root_v67(), "meta_loop_sequence_contract_arc_closeout_v65_reference.json"
        )
    )
    run_trace = MetaLoopRunTrace.model_validate(
        _load_json(_fixtures_root_v67(), "meta_loop_run_trace_arc_closeout_v65_reference.json")
    )

    assert_v37b_reference_bundle_consistent(
        intent_packet=intent_packet,
        module_catalog=module_catalog,
        sequence_contract=sequence_contract,
        run_trace=run_trace,
    )
    assert sequence_contract.schema == META_LOOP_SEQUENCE_CONTRACT_SCHEMA
    assert run_trace.schema == META_LOOP_RUN_TRACE_SCHEMA
    assert run_trace.trace_mode == V37B_REFERENCE_TRACE_MODE


def test_v37b_reference_pair_round_trips_without_drift() -> None:
    sequence_payload = _load_json(
        _fixtures_root_v67(), "meta_loop_sequence_contract_arc_closeout_v65_reference.json"
    )
    run_trace_payload = _load_json(
        _fixtures_root_v67(), "meta_loop_run_trace_arc_closeout_v65_reference.json"
    )

    assert canonicalize_meta_loop_sequence_contract_payload(sequence_payload) == sequence_payload
    assert canonicalize_meta_loop_run_trace_payload(run_trace_payload) == run_trace_payload


def test_v37b_reference_binding_rejects_mismatched_reference_instance_id() -> None:
    intent_packet = _load_v66_intent_packet()
    module_catalog = _load_v66_module_catalog()
    sequence_payload = _load_json(
        _fixtures_root_v67(), "meta_loop_sequence_contract_arc_closeout_v65_reference.json"
    )
    sequence_payload["reference_instance_id"] = "arc_closeout_other_reference"  # type: ignore[index]
    sequence_contract = MetaLoopSequenceContract.model_validate(sequence_payload)
    run_trace = MetaLoopRunTrace.model_validate(
        _load_json(_fixtures_root_v67(), "meta_loop_run_trace_arc_closeout_v65_reference.json")
    )

    with pytest.raises(
        ValueError, match="reference instance binding mismatch for reference_instance_id"
    ):
        assert_v37b_reference_instance_binding(
            intent_packet=intent_packet,
            module_catalog=module_catalog,
            sequence_contract=sequence_contract,
            run_trace=run_trace,
        )


def test_v37b_run_trace_rejects_missing_explicit_null_binding_field() -> None:
    payload = _load_json(
        _fixtures_root_v67(), "meta_loop_sequence_contract_arc_closeout_v65_reference.json"
    )
    payload["steps"][0].pop("checkpoint_binding_id")  # type: ignore[index]

    with pytest.raises(ValidationError, match="checkpoint_binding_id"):
        MetaLoopSequenceContract.model_validate(payload)


def test_v37b_sequence_contract_rejects_undocumented_retry_edge() -> None:
    payload = _load_json(
        _fixtures_root_v67(), "meta_loop_sequence_contract_arc_closeout_v65_reference.json"
    )
    payload["steps"][6]["retry_edge_ids"] = ["retry_99_hidden_retry"]  # type: ignore[index]

    with pytest.raises(
        ValidationError,
        match="retry_edge_ids must resolve declared retry edges",
    ):
        MetaLoopSequenceContract.model_validate(payload)


def test_v37b_bundle_rejects_hard_step_binding_drift_from_v37a_catalog() -> None:
    intent_packet = _load_v66_intent_packet()
    module_catalog = _load_v66_module_catalog()
    sequence_payload = _load_json(
        _fixtures_root_v67(), "meta_loop_sequence_contract_arc_closeout_v65_reference.json"
    )
    sequence_payload["steps"][1]["checkpoint_binding_id"] = "bundle_lint_cli"  # type: ignore[index]
    sequence_contract = MetaLoopSequenceContract.model_validate(sequence_payload)
    run_trace = MetaLoopRunTrace.model_validate(
        _load_json(_fixtures_root_v67(), "meta_loop_run_trace_arc_closeout_v65_reference.json")
    )

    with pytest.raises(
        ValueError,
        match="must bind an executor from the released v37a catalog",
    ):
        assert_v37b_reference_bundle_consistent(
            intent_packet=intent_packet,
            module_catalog=module_catalog,
            sequence_contract=sequence_contract,
            run_trace=run_trace,
        )


def test_v37b_run_trace_rejects_reference_trace_claiming_accepted_compilation() -> None:
    payload = _load_json(
        _fixtures_root_v67(), "meta_loop_run_trace_arc_closeout_v65_reference.json"
    )
    payload["steps"][0]["accepted_compilation_occurred"] = True  # type: ignore[index]

    with pytest.raises(
        ValidationError,
        match="accepted_compilation_occurred = false",
    ):
        MetaLoopRunTrace.model_validate(payload)


def test_v37b_run_trace_rejects_missing_checkpoint_result_ref_path() -> None:
    payload = _load_json(
        _fixtures_root_v67(), "meta_loop_run_trace_arc_closeout_v65_reference.json"
    )
    payload["steps"][1]["observed_checkpoint_result_refs"] = [  # type: ignore[index]
        "artifacts/agent_harness/v67/evidence_inputs/missing_checkpoint_result.json"
    ]

    with pytest.raises(ValidationError, match="must resolve to an existing repo file"):
        MetaLoopRunTrace.model_validate(payload)


def test_v37b_bundle_rejects_reasoning_step_without_downstream_gate_binding() -> None:
    intent_packet = _load_v66_intent_packet()
    module_catalog = _load_v66_module_catalog()
    sequence_payload = _load_json(
        _fixtures_root_v67(), "meta_loop_sequence_contract_arc_closeout_v65_reference.json"
    )
    sequence_payload["steps"][0]["downstream_gate_module_id"] = None  # type: ignore[index]
    sequence_contract = MetaLoopSequenceContract.model_validate(sequence_payload)
    run_trace = MetaLoopRunTrace.model_validate(
        _load_json(_fixtures_root_v67(), "meta_loop_run_trace_arc_closeout_v65_reference.json")
    )

    with pytest.raises(ValueError, match="must bind a downstream gate module"):
        assert_v37b_reference_bundle_consistent(
            intent_packet=intent_packet,
            module_catalog=module_catalog,
            sequence_contract=sequence_contract,
            run_trace=run_trace,
        )
