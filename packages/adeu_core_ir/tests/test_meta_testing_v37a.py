from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest
from adeu_core_ir import (
    META_MODULE_CATALOG_SCHEMA,
    META_TESTING_INTENT_PACKET_SCHEMA,
    MetaModuleCatalog,
    MetaTestingIntentPacket,
    assert_v37a_reference_bundle_consistent,
    assert_v37a_reference_instance_binding,
    canonicalize_meta_module_catalog_payload,
    canonicalize_meta_testing_intent_packet_payload,
)
from adeu_ir.repo import repo_root
from pydantic import ValidationError


def _fixtures_root() -> Path:
    root = repo_root(anchor=Path(__file__))
    return root / "apps" / "api" / "fixtures" / "meta_testing" / "vnext_plus66"


def _load_json(name: str) -> dict[str, object]:
    return json.loads((_fixtures_root() / name).read_text(encoding="utf-8"))


def test_v37a_reference_pair_fixtures_validate_and_bind() -> None:
    intent_packet = MetaTestingIntentPacket.model_validate(
        _load_json("meta_testing_intent_packet_arc_closeout_v65_reference.json")
    )
    module_catalog = MetaModuleCatalog.model_validate(
        _load_json("meta_module_catalog_arc_closeout_v65_reference.json")
    )

    assert_v37a_reference_bundle_consistent(
        intent_packet=intent_packet,
        module_catalog=module_catalog,
    )
    assert intent_packet.schema == META_TESTING_INTENT_PACKET_SCHEMA
    assert module_catalog.schema == META_MODULE_CATALOG_SCHEMA
    assert intent_packet.reference_instance_id == "arc_closeout_v65_reference"
    assert module_catalog.intent_packet_id == "v37a_arc_closeout_v65_intent"


def test_v37a_reference_pair_round_trips_without_drift() -> None:
    intent_payload = _load_json("meta_testing_intent_packet_arc_closeout_v65_reference.json")
    catalog_payload = _load_json("meta_module_catalog_arc_closeout_v65_reference.json")

    assert canonicalize_meta_testing_intent_packet_payload(intent_payload) == intent_payload
    assert canonicalize_meta_module_catalog_payload(catalog_payload) == catalog_payload


def test_v37a_reference_binding_rejects_mismatched_intent_packet_id() -> None:
    intent_packet = MetaTestingIntentPacket.model_validate(
        _load_json("meta_testing_intent_packet_arc_closeout_v65_reference.json")
    )
    catalog_payload = _load_json("meta_module_catalog_arc_closeout_v65_reference.json")
    catalog_payload["intent_packet_id"] = "v37a_other_intent"  # type: ignore[index]
    module_catalog = MetaModuleCatalog.model_validate(catalog_payload)

    with pytest.raises(
        ValueError, match="reference instance binding mismatch for intent_packet_id"
    ):
        assert_v37a_reference_instance_binding(
            intent_packet=intent_packet,
            module_catalog=module_catalog,
        )


def test_v37a_intent_packet_rejects_unresolved_authoritative_hash() -> None:
    payload = _load_json("meta_testing_intent_packet_arc_closeout_v65_reference.json")
    payload["authoritative_inputs"][0]["artifact_sha256"] = "0" * 64  # type: ignore[index]

    with pytest.raises(ValidationError, match="artifact_sha256 must match repo file bytes"):
        MetaTestingIntentPacket.model_validate(payload)


def test_v37a_module_catalog_rejects_non_frozen_drift_taxonomy() -> None:
    payload = _load_json("meta_module_catalog_arc_closeout_v65_reference.json")
    payload["drift_taxonomy"] = [  # type: ignore[index]
        "epistemic_drift",
        "ontology_drift",
        "deontic_drift",
        "utility_drift",
    ]

    with pytest.raises(ValidationError, match="drift_taxonomy must equal the frozen sequence"):
        MetaModuleCatalog.model_validate(payload)


def test_v37a_module_catalog_rejects_missing_dispatch_provenance_for_reasoning_module() -> None:
    payload = _load_json("meta_module_catalog_arc_closeout_v65_reference.json")
    payload["modules"][-1].pop("dispatch_provenance")  # type: ignore[index]

    with pytest.raises(
        ValidationError,
        match=(
            "reasoning module reasoning_01_meta_intent_interpreter must declare dispatch_provenance"
        ),
    ):
        MetaModuleCatalog.model_validate(payload)


def test_v37a_module_catalog_rejects_unknown_checkpoint_capability() -> None:
    payload = _load_json("meta_module_catalog_arc_closeout_v65_reference.json")
    payload["modules"][0]["capability_id"] = "closeout_lint_bundle"  # type: ignore[index]

    with pytest.raises(
        ValidationError,
        match=(
            "checkpoint module checkpoint_01_bundle_lint must bind a frozen checkpoint capability"
        ),
    ):
        MetaModuleCatalog.model_validate(payload)


def test_v37a_module_catalog_rejects_checkpoint_authority_status_drift() -> None:
    payload = _load_json("meta_module_catalog_arc_closeout_v65_reference.json")
    payload["modules"][0]["authority_status"] = "soft_influence_only"  # type: ignore[index]

    with pytest.raises(
        ValidationError,
        match="checkpoint module checkpoint_01_bundle_lint must remain hard_checkpoint_truth",
    ):
        MetaModuleCatalog.model_validate(payload)


def test_v37a_module_catalog_rejects_ambiguous_single_executor_granularity() -> None:
    payload = _load_json("meta_module_catalog_arc_closeout_v65_reference.json")
    extra_binding = copy.deepcopy(payload["modules"][0]["executor_bindings"][0])  # type: ignore[index]
    extra_binding["binding_id"] = "arc_bundle_closeout_lint_secondary"  # type: ignore[index]
    payload["modules"][0]["executor_bindings"].append(extra_binding)  # type: ignore[index]

    with pytest.raises(
        ValidationError,
        match="must bind exactly one executor for single_executor granularity",
    ):
        MetaModuleCatalog.model_validate(payload)


def test_v37a_module_catalog_rejects_untyped_soft_originated_checkpoint_slot() -> None:
    payload = _load_json("meta_module_catalog_arc_closeout_v65_reference.json")
    payload["modules"][0]["executor_bindings"][0]["parameter_policy"]["parameter_slots"].append(  # type: ignore[index]
        {
            "slot_name": "soft_prompt_output",
            "slot_type": "string_literal",
            "value_origin": "soft_originated_input",
        }
    )

    with pytest.raises(
        ValidationError,
        match="must reject soft-originated inputs when they are not allowed",
    ):
        MetaModuleCatalog.model_validate(payload)


def test_v37a_module_catalog_rejects_out_of_scope_sequence_surface() -> None:
    payload = _load_json("meta_module_catalog_arc_closeout_v65_reference.json")
    payload["modules"][-1]["output_contract"] = [  # type: ignore[index]
        "checkpoint_shape_expectation_summary",
        "drift_hypothesis_summary",
        "meta_loop_sequence_contract@1",
        "repair_candidate_summary",
    ]

    with pytest.raises(
        ValidationError,
        match="must not introduce out-of-scope v37b/v37c surfaces",
    ):
        MetaModuleCatalog.model_validate(payload)
