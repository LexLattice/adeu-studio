from __future__ import annotations

from pathlib import Path
from typing import Any

from adeu_agent_harness import AnmTaskpackBindingProfile, build_v48a_taskpack_binding_profile
from adeu_agent_harness.taskpack_binding import TaskpackBindingError

from .models import (
    SemanticSeedV48BridgeContract,
    TaskpackBindingSpecSeed,
    canonical_json,
)

ADEU_SEMANTIC_SEED_V48_BRIDGE_ERROR_SCHEMA = "adeu_semantic_seed_v48_bridge_error@1"

ASF6001_INPUT_INVALID = "ASF6001"
ASF6002_PROFILE_MISMATCH = "ASF6002"
ASF6003_ANCHOR_MISMATCH = "ASF6003"
ASF6004_FIXED_DEFAULT_CONFLICT = "ASF6004"
ASF6005_UNSUPPORTED_SEED = "ASF6005"
ASF6006_V48A_BUILDER_FAILURE = "ASF6006"
ASF6007_OUTPUT_REVALIDATION_FAILED = "ASF6007"

_RELEASED_V48A_DEFAULTS = {
    "lineage_resolution_posture": "fail_closed_on_unresolved_or_stale_lineage",
    "prompt_projection_posture": "projection_only_non_authoritative",
    "unsupported_mapping_posture": "fail_closed",
}


class SemanticFormsV48BridgeError(RuntimeError):
    def __init__(self, *, code: str, message: str, details: dict[str, Any] | None = None) -> None:
        self.code = code
        self.message = message
        self.details = details or {}
        payload = {
            "schema": ADEU_SEMANTIC_SEED_V48_BRIDGE_ERROR_SCHEMA,
            "code": code,
            "message": message,
            "details": self.details,
        }
        super().__init__(canonical_json(payload))


def _fail(
    *,
    code: str,
    message: str,
    details: dict[str, Any] | None = None,
) -> SemanticFormsV48BridgeError:
    raise SemanticFormsV48BridgeError(code=code, message=message, details=details)


def _contract_command_projection(
    bridge_contract: SemanticSeedV48BridgeContract,
) -> list[dict[str, Any]]:
    return [
        row.model_dump(mode="json", exclude_none=True)
        for row in bridge_contract.command_projection
    ]


def _contract_evidence_slot_projection(
    bridge_contract: SemanticSeedV48BridgeContract,
) -> list[dict[str, Any]]:
    return [
        row.model_dump(mode="json", exclude_none=True)
        for row in bridge_contract.evidence_slot_projection
    ]


def _contract_prompt_projection_inputs(
    bridge_contract: SemanticSeedV48BridgeContract,
) -> list[dict[str, Any]]:
    return [
        row.model_dump(mode="json", exclude_none=True)
        for row in bridge_contract.prompt_projection_inputs
    ]


def _validate_seed_defaults(
    *,
    seed: TaskpackBindingSpecSeed,
    bridge_contract: SemanticSeedV48BridgeContract,
) -> None:
    if set(seed.fixed_defaults) != set(_RELEASED_V48A_DEFAULTS):
        _fail(
            code=ASF6005_UNSUPPORTED_SEED,
            message="seed fixed_defaults must contain exactly the released V48-A posture keys",
            details={
                "observed_keys": sorted(seed.fixed_defaults),
                "expected_keys": sorted(_RELEASED_V48A_DEFAULTS),
            },
        )

    bridge_defaults = {
        "lineage_resolution_posture": bridge_contract.lineage_resolution_posture,
        "prompt_projection_posture": bridge_contract.prompt_projection_posture,
        "unsupported_mapping_posture": bridge_contract.unsupported_mapping_posture,
    }
    for key, expected_value in _RELEASED_V48A_DEFAULTS.items():
        seed_value = seed.fixed_defaults.get(key)
        bridge_value = bridge_defaults[key]
        if seed_value != expected_value or bridge_value != expected_value:
            _fail(
                code=ASF6004_FIXED_DEFAULT_CONFLICT,
                message="bridge defaults may only restate the released V48-A postures exactly",
                details={
                    "field": key,
                    "seed_value": seed_value,
                    "bridge_value": bridge_value,
                    "expected_value": expected_value,
                },
            )


def bridge_seed_to_v48a_taskpack_binding_profile(
    *,
    seed: TaskpackBindingSpecSeed,
    bridge_contract: SemanticSeedV48BridgeContract,
    repo_root_path: Path | None = None,
) -> AnmTaskpackBindingProfile:
    if seed.profile_id != bridge_contract.profile_id:
        _fail(
            code=ASF6002_PROFILE_MISMATCH,
            message="seed and bridge contract must share the same profile_id",
            details={
                "seed_profile_id": seed.profile_id,
                "bridge_contract_profile_id": bridge_contract.profile_id,
            },
        )

    anchor_pairs = (
        ("scope_anchor_ref", seed.scope_anchor_ref, bridge_contract.expected_scope_anchor_ref),
        ("policy_anchor_ref", seed.policy_anchor_ref, bridge_contract.expected_policy_anchor_ref),
        (
            "worker_subject_ref",
            seed.worker_subject_ref,
            bridge_contract.expected_worker_subject_ref,
        ),
    )
    for field_name, seed_value, expected_value in anchor_pairs:
        if seed_value != expected_value:
            _fail(
                code=ASF6003_ANCHOR_MISMATCH,
                message="bridge contract anchor expectations must match the released seed exactly",
                details={
                    "field": field_name,
                    "seed_value": seed_value,
                    "expected_value": expected_value,
                },
            )

    if seed.mutation_posture != "read_only":
        _fail(
            code=ASF6005_UNSUPPORTED_SEED,
            message="starter V49-D bridge supports only read_only mutation posture",
            details={"mutation_posture": seed.mutation_posture},
        )

    if seed.artifact_kinds != ["taskpack_binding_spec_seed"]:
        _fail(
            code=ASF6005_UNSUPPORTED_SEED,
            message="starter V49-D bridge supports only taskpack_binding_spec_seed artifact kind",
            details={"artifact_kinds": seed.artifact_kinds},
        )

    _validate_seed_defaults(seed=seed, bridge_contract=bridge_contract)

    try:
        binding_profile = build_v48a_taskpack_binding_profile(
            binding_profile_id=bridge_contract.binding_profile_id,
            snapshot_id=bridge_contract.snapshot_id,
            snapshot_sha256=bridge_contract.snapshot_sha256,
            binding_subject_ids=[bridge_contract.binding_subject_id],
            task_scope_summary=bridge_contract.task_scope_summary,
            policy_source_refs=[bridge_contract.policy_source_ref],
            scope_source_refs=[bridge_contract.scope_source_ref],
            scope_binding_entry_refs=[bridge_contract.scope_binding_entry_ref],
            worker_subject_refs=[seed.worker_subject_ref],
            allowlist_projection=list(seed.allow_paths),
            forbidden_projection={
                "forbidden_paths": list(seed.forbid_paths),
                "forbidden_effects": list(seed.forbid_effects),
            },
            command_projection=_contract_command_projection(bridge_contract),
            evidence_slot_projection=_contract_evidence_slot_projection(bridge_contract),
            prompt_projection_inputs=_contract_prompt_projection_inputs(bridge_contract),
            repo_root_path=repo_root_path,
        )
    except TaskpackBindingError as exc:
        _fail(
            code=ASF6006_V48A_BUILDER_FAILURE,
            message="released V48-A builder rejected the bridge inputs",
            details={
                "upstream_code": exc.code,
                "upstream_message": exc.message,
                "upstream_details": exc.details,
            },
        )

    revalidated = AnmTaskpackBindingProfile.model_validate(
        binding_profile.model_dump(mode="json", exclude_none=True)
    )
    if revalidated.semantic_hash != binding_profile.semantic_hash:
        _fail(
            code=ASF6007_OUTPUT_REVALIDATION_FAILED,
            message=(
                "revalidated binding profile semantic_hash does not match emitted "
                "semantic_hash"
            ),
            details={
                "emitted_semantic_hash": binding_profile.semantic_hash,
                "revalidated_semantic_hash": revalidated.semantic_hash,
            },
        )
    return binding_profile
