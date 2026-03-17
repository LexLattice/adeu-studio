from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path
from typing import Any, TypeVar

from pydantic import BaseModel, ConfigDict, Field, ValidationError

from .meta_testing import (
    FROZEN_V37A_AUTHORITATIVE_INPUT_IDS,
    FROZEN_V37A_DRIFT_TAXONOMY,
    FROZEN_V37A_MODULE_CLASSES,
    FROZEN_V37A_OUT_OF_SCOPE_SURFACES,
    META_LOOP_CHECKPOINT_RESULT_MANIFEST_SCHEMA,
    V37A_OPERATOR_SURFACE,
    V37A_REFERENCE_PHASE,
    V37B_REFERENCE_TRACE_MODE,
    V37C_EXECUTED_TRACE_MODE,
    MetaExecutorBinding,
    MetaExecutorParameterPolicy,
    MetaExecutorParameterSlot,
    MetaLoopCheckpointResultManifest,
    MetaLoopRunTrace,
    MetaLoopSequenceContract,
    MetaModuleCatalog,
    MetaModuleDescriptor,
    MetaReasoningDispatchProvenance,
    MetaTestingIntentPacket,
    assert_v37a_reference_bundle_consistent,
    assert_v37b_reference_bundle_consistent,
    assert_v37c_reference_bundle_consistent,
)

V37A_META_INTENT_MODULE_CATALOG_EVIDENCE_SCHEMA = (
    "v37a_meta_intent_module_catalog_evidence@1"
)
V37A_META_INTENT_MODULE_CATALOG_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS66.md#v37a_meta_intent_module_catalog_contract@1"
)
STOP_GATE_METRICS_SCHEMA = "stop_gate_metrics@1"
EXPECTED_METRIC_KEY_CARDINALITY = 80
DEFAULT_V65_BASELINE_METRICS_PATH = "artifacts/stop_gate/metrics_v65_closeout.json"
DEFAULT_META_TESTING_INTENT_PACKET_SCHEMA_PATH = (
    "packages/adeu_core_ir/schema/meta_testing_intent_packet.v1.json"
)
DEFAULT_META_MODULE_CATALOG_SCHEMA_PATH = (
    "packages/adeu_core_ir/schema/meta_module_catalog.v1.json"
)
DEFAULT_META_TESTING_INTENT_PACKET_REFERENCE_PATH = (
    "apps/api/fixtures/meta_testing/vnext_plus66/"
    "meta_testing_intent_packet_arc_closeout_v65_reference.json"
)
DEFAULT_META_MODULE_CATALOG_REFERENCE_PATH = (
    "apps/api/fixtures/meta_testing/vnext_plus66/"
    "meta_module_catalog_arc_closeout_v65_reference.json"
)
DEFAULT_V37A_META_INTENT_MODULE_CATALOG_EVIDENCE_PATH = (
    "artifacts/agent_harness/v66/evidence_inputs/"
    "v37a_meta_intent_module_catalog_evidence_v66.json"
)
V37B_SEQUENCE_TRACE_EVIDENCE_SCHEMA = "v37b_sequence_trace_evidence@1"
V37B_SEQUENCE_TRACE_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS67.md#v37b_sequence_trace_contract@1"
)
DEFAULT_V66_BASELINE_METRICS_PATH = "artifacts/stop_gate/metrics_v66_closeout.json"
DEFAULT_META_LOOP_SEQUENCE_CONTRACT_SCHEMA_PATH = (
    "packages/adeu_core_ir/schema/meta_loop_sequence_contract.v1.json"
)
DEFAULT_META_LOOP_RUN_TRACE_SCHEMA_PATH = (
    "packages/adeu_core_ir/schema/meta_loop_run_trace.v1.json"
)
DEFAULT_META_LOOP_SEQUENCE_CONTRACT_REFERENCE_PATH = (
    "apps/api/fixtures/meta_testing/vnext_plus67/"
    "meta_loop_sequence_contract_arc_closeout_v65_reference.json"
)
DEFAULT_META_LOOP_RUN_TRACE_REFERENCE_PATH = (
    "apps/api/fixtures/meta_testing/vnext_plus67/"
    "meta_loop_run_trace_arc_closeout_v65_reference.json"
)
DEFAULT_V37B_SEQUENCE_TRACE_EVIDENCE_PATH = (
    "artifacts/agent_harness/v67/evidence_inputs/v37b_sequence_trace_evidence_v67.json"
)
V37C_REFERENCE_LOOP_EVIDENCE_SCHEMA = "v37c_reference_loop_evidence@1"
V37C_REFERENCE_LOOP_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS68.md#v37c_executable_reference_loop_contract@1"
)
DEFAULT_V67_BASELINE_METRICS_PATH = "artifacts/stop_gate/metrics_v67_closeout.json"
DEFAULT_META_LOOP_CHECKPOINT_RESULT_MANIFEST_SCHEMA_PATH = (
    "packages/adeu_core_ir/schema/meta_loop_checkpoint_result_manifest.v1.json"
)
DEFAULT_META_LOOP_CHECKPOINT_RESULT_MANIFEST_REFERENCE_PATH = (
    "apps/api/fixtures/meta_testing/vnext_plus68/"
    "meta_loop_checkpoint_result_manifest_arc_closeout_v65_reference.json"
)
DEFAULT_V37C_EXECUTED_META_LOOP_RUN_TRACE_REFERENCE_PATH = (
    "apps/api/fixtures/meta_testing/vnext_plus68/"
    "meta_loop_run_trace_arc_closeout_v65_executed_reference.json"
)
DEFAULT_V37C_REFERENCE_LOOP_EVIDENCE_PATH = (
    "artifacts/agent_harness/v68/evidence_inputs/v37c_reference_loop_evidence_v68.json"
)
FROZEN_V37B_OUT_OF_SCOPE_SURFACES: tuple[str, ...] = (
    "meta_control_update_candidate@1",
    "meta_control_update_manifest@1",
    "meta_loop_checkpoint_result_manifest@1",
    "meta_loop_conformance_report@1",
    "meta_loop_drift_diagnostics@1",
)
FROZEN_V37C_OUT_OF_SCOPE_SURFACES: tuple[str, ...] = (
    "meta_control_update_candidate@1",
    "meta_control_update_manifest@1",
    "meta_loop_conformance_report@1",
    "meta_loop_drift_diagnostics@1",
)

ModelT = TypeVar("ModelT", bound=BaseModel)


class MetaTestingEvidenceError(ValueError):
    pass


class MaterializedMetaTestingEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid")

    path: str = Field(min_length=1)
    hash: str = Field(min_length=64, max_length=64)
    payload: dict[str, Any]


class V37AMetaIntentModuleCatalogEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: str = Field(
        default=V37A_META_INTENT_MODULE_CATALOG_EVIDENCE_SCHEMA,
        alias="schema",
    )
    contract_source: str = V37A_META_INTENT_MODULE_CATALOG_CONTRACT_SOURCE
    evidence_input_path: str = Field(min_length=1)
    meta_testing_intent_packet_schema_path: str = Field(min_length=1)
    meta_testing_intent_packet_schema_hash: str = Field(min_length=64, max_length=64)
    meta_module_catalog_schema_path: str = Field(min_length=1)
    meta_module_catalog_schema_hash: str = Field(min_length=64, max_length=64)
    meta_testing_intent_packet_reference_path: str = Field(min_length=1)
    meta_testing_intent_packet_reference_hash: str = Field(min_length=64, max_length=64)
    meta_module_catalog_reference_path: str = Field(min_length=1)
    meta_module_catalog_reference_hash: str = Field(min_length=64, max_length=64)
    module_class_enum_frozen: bool
    drift_taxonomy_enum_frozen: bool
    reference_instance_pair_binding_verified: bool
    authoritative_input_refs_and_hashes_verified: bool
    checkpoint_executor_bindings_verified: bool
    capability_to_executor_granularity_verified: bool
    checkpoint_parameter_safety_verified: bool
    reasoning_dispatch_provenance_verified: bool
    hard_checkpoint_truth_boundary_preserved: bool
    v37a_scope_boundary_preserved: bool
    verification_passed: bool
    metric_key_cardinality: int = Field(ge=0)
    metric_key_exact_set_equal_v65: bool
    notes: str = Field(min_length=1)


class V37BSequenceTraceEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: str = Field(
        default=V37B_SEQUENCE_TRACE_EVIDENCE_SCHEMA,
        alias="schema",
    )
    contract_source: str = V37B_SEQUENCE_TRACE_CONTRACT_SOURCE
    evidence_input_path: str = Field(min_length=1)
    meta_testing_intent_packet_schema_path: str = Field(min_length=1)
    meta_testing_intent_packet_schema_hash: str = Field(min_length=64, max_length=64)
    meta_module_catalog_schema_path: str = Field(min_length=1)
    meta_module_catalog_schema_hash: str = Field(min_length=64, max_length=64)
    meta_loop_sequence_contract_schema_path: str = Field(min_length=1)
    meta_loop_sequence_contract_schema_hash: str = Field(min_length=64, max_length=64)
    meta_loop_run_trace_schema_path: str = Field(min_length=1)
    meta_loop_run_trace_schema_hash: str = Field(min_length=64, max_length=64)
    meta_testing_intent_packet_reference_path: str = Field(min_length=1)
    meta_testing_intent_packet_reference_hash: str = Field(min_length=64, max_length=64)
    meta_module_catalog_reference_path: str = Field(min_length=1)
    meta_module_catalog_reference_hash: str = Field(min_length=64, max_length=64)
    meta_loop_sequence_contract_reference_path: str = Field(min_length=1)
    meta_loop_sequence_contract_reference_hash: str = Field(min_length=64, max_length=64)
    meta_loop_run_trace_reference_path: str = Field(min_length=1)
    meta_loop_run_trace_reference_hash: str = Field(min_length=64, max_length=64)
    v37a_meta_intent_module_catalog_evidence_path: str = Field(min_length=1)
    v37a_meta_intent_module_catalog_evidence_hash: str = Field(min_length=64, max_length=64)
    v37a_reference_tuple_consumed_without_drift: bool
    sequence_trace_reference_pair_binding_verified: bool
    reference_trace_mode_not_executed_verified: bool
    step_order_and_phase_boundary_verified: bool
    step_binding_nullability_explicit: bool
    retry_representation_explicit: bool
    checkpoint_bindings_resolved_via_v37a_catalog: bool
    reasoning_dispatch_bindings_resolved_per_step: bool
    operator_gate_surfaces_verified: bool
    reasoning_claims_bound_to_downstream_gates: bool
    operational_influence_distinct_from_accepted_compilation: bool
    observed_checkpoint_result_refs_preaccepted_only: bool
    v37b_scope_boundary_preserved: bool
    verification_passed: bool
    metric_key_cardinality: int = Field(ge=0)
    metric_key_exact_set_equal_v66: bool
    notes: str = Field(min_length=1)


class V37CReferenceLoopEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: str = Field(
        default=V37C_REFERENCE_LOOP_EVIDENCE_SCHEMA,
        alias="schema",
    )
    contract_source: str = V37C_REFERENCE_LOOP_CONTRACT_SOURCE
    evidence_input_path: str = Field(min_length=1)
    meta_testing_intent_packet_schema_path: str = Field(min_length=1)
    meta_testing_intent_packet_schema_hash: str = Field(min_length=64, max_length=64)
    meta_module_catalog_schema_path: str = Field(min_length=1)
    meta_module_catalog_schema_hash: str = Field(min_length=64, max_length=64)
    meta_loop_sequence_contract_schema_path: str = Field(min_length=1)
    meta_loop_sequence_contract_schema_hash: str = Field(min_length=64, max_length=64)
    meta_loop_run_trace_schema_path: str = Field(min_length=1)
    meta_loop_run_trace_schema_hash: str = Field(min_length=64, max_length=64)
    meta_loop_checkpoint_result_manifest_schema_path: str = Field(min_length=1)
    meta_loop_checkpoint_result_manifest_schema_hash: str = Field(
        min_length=64, max_length=64
    )
    meta_testing_intent_packet_reference_path: str = Field(min_length=1)
    meta_testing_intent_packet_reference_hash: str = Field(min_length=64, max_length=64)
    meta_module_catalog_reference_path: str = Field(min_length=1)
    meta_module_catalog_reference_hash: str = Field(min_length=64, max_length=64)
    meta_loop_sequence_contract_reference_path: str = Field(min_length=1)
    meta_loop_sequence_contract_reference_hash: str = Field(min_length=64, max_length=64)
    meta_loop_run_trace_reference_path: str = Field(min_length=1)
    meta_loop_run_trace_reference_hash: str = Field(min_length=64, max_length=64)
    meta_loop_checkpoint_result_manifest_reference_path: str = Field(min_length=1)
    meta_loop_checkpoint_result_manifest_reference_hash: str = Field(
        min_length=64, max_length=64
    )
    executed_meta_loop_run_trace_reference_path: str = Field(min_length=1)
    executed_meta_loop_run_trace_reference_hash: str = Field(min_length=64, max_length=64)
    v37a_meta_intent_module_catalog_evidence_path: str = Field(min_length=1)
    v37a_meta_intent_module_catalog_evidence_hash: str = Field(min_length=64, max_length=64)
    v37b_sequence_trace_evidence_path: str = Field(min_length=1)
    v37b_sequence_trace_evidence_hash: str = Field(min_length=64, max_length=64)
    v37a_reference_tuple_consumed_without_drift: bool
    v37b_reference_tuple_consumed_without_drift: bool
    executed_reference_run_emitted: bool
    checkpoint_result_manifest_emitted_and_hash_bound: bool
    executed_run_trace_artifact_distinct_from_v67_reference_trace: bool
    executed_run_trace_mode_verified: bool
    hard_checkpoint_results_captured_from_actual_executors: bool
    executed_capability_subset_declared_intentionally: bool
    authoritative_stop_gate_executor_binding_verified: bool
    actual_branch_and_retry_outcomes_verified: bool
    failed_checkpoint_attempts_still_emit_normalized_result_rows: bool
    output_artifact_refs_and_hashes_verified: bool
    reasoning_vs_checkpoint_truth_boundary_preserved: bool
    executed_step_order_matches_v37b_contract: bool
    v37c_scope_boundary_preserved: bool
    verification_passed: bool
    metric_key_cardinality: int = Field(ge=0)
    metric_key_exact_set_equal_v67: bool
    notes: str = Field(min_length=1)


def _canonical_json_text(value: object) -> str:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def _sha256_canonical_json(value: object) -> str:
    return hashlib.sha256(_canonical_json_text(value).encode("utf-8")).hexdigest()


def _pretty_canonical_json(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def _resolve_repo_relative_path(
    *,
    root: Path,
    path_text: str,
    field_name: str,
    required_prefix: str | None = None,
) -> Path:
    if not path_text:
        raise MetaTestingEvidenceError(f"{field_name} must not be empty")
    relative = Path(path_text)
    if relative.is_absolute():
        raise MetaTestingEvidenceError(f"{field_name} must be repo-relative")
    if required_prefix is not None and not path_text.startswith(required_prefix):
        raise MetaTestingEvidenceError(
            f"{field_name} must stay under the {required_prefix!r} subtree"
        )
    if any(part in {"", ".", ".."} for part in relative.parts):
        raise MetaTestingEvidenceError(f"{field_name} contains invalid path components")
    resolved = (root / relative).resolve()
    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise MetaTestingEvidenceError(f"{field_name} must stay within repository root") from exc
    return resolved


def _resolve_existing_repo_file(
    *,
    root: Path,
    path_text: str,
    field_name: str,
    required_prefix: str | None = None,
) -> Path:
    resolved = _resolve_repo_relative_path(
        root=root,
        path_text=path_text,
        field_name=field_name,
        required_prefix=required_prefix,
    )
    if not resolved.is_file():
        raise MetaTestingEvidenceError(f"{field_name} does not exist")
    return resolved


def _load_json_dict(*, path: Path, field_name: str) -> tuple[str, dict[str, Any]]:
    if not path.is_file():
        raise MetaTestingEvidenceError(f"{field_name} does not exist")
    text = path.read_text(encoding="utf-8")
    try:
        payload = json.loads(text)
    except json.JSONDecodeError as exc:
        raise MetaTestingEvidenceError(f"{field_name} is not valid JSON") from exc
    if not isinstance(payload, dict):
        raise MetaTestingEvidenceError(f"{field_name} must contain a JSON object")
    return text, payload


def _load_stop_gate_metrics(*, path: Path, field_name: str) -> dict[str, Any]:
    _text, payload = _load_json_dict(path=path, field_name=field_name)
    if payload.get("schema") != STOP_GATE_METRICS_SCHEMA:
        raise MetaTestingEvidenceError(f"{field_name} must use {STOP_GATE_METRICS_SCHEMA}")
    metrics = payload.get("metrics")
    if not isinstance(metrics, dict) or not all(isinstance(key, str) for key in metrics):
        raise MetaTestingEvidenceError(f"{field_name} metrics must be an object with string keys")
    return payload


def _load_validated_model(
    *,
    path: Path,
    field_name: str,
    model_type: type[ModelT],
    exclude_none: bool = True,
    by_alias: bool = False,
) -> tuple[dict[str, Any], ModelT]:
    _text, payload = _load_json_dict(path=path, field_name=field_name)
    try:
        model = model_type.model_validate(payload)
    except ValidationError as exc:
        raise MetaTestingEvidenceError(str(exc)) from exc
    if payload != model.model_dump(mode="json", exclude_none=exclude_none, by_alias=by_alias):
        raise MetaTestingEvidenceError(
            f"{field_name} must remain structurally canonical under the frozen model"
        )
    return payload, model


def _load_frozen_schema(
    *,
    path: Path,
    field_name: str,
    model_type: type[BaseModel],
) -> dict[str, Any]:
    _text, payload = _load_json_dict(path=path, field_name=field_name)
    expected = model_type.model_json_schema(by_alias=True)
    if payload != expected:
        raise MetaTestingEvidenceError(f"{field_name} does not match the frozen exported schema")
    return payload


def _sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _assert_python_symbol_exists_in_repo(
    *,
    repo_root: Path,
    binding_ref: str,
    field_name: str,
) -> None:
    if "::" not in binding_ref:
        raise MetaTestingEvidenceError(f"{field_name} must use repo_path::symbol")
    repo_path, symbol = binding_ref.split("::", 1)
    if not symbol:
        raise MetaTestingEvidenceError(f"{field_name} must include a symbol")
    path = _resolve_existing_repo_file(
        root=repo_root,
        path_text=repo_path,
        field_name=field_name,
    )
    tree = ast.parse(path.read_text(encoding="utf-8"))
    for node in tree.body:
        if (
            isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
            and node.name == symbol
        ):
            return
    raise MetaTestingEvidenceError(f"{field_name} must resolve to an existing python symbol")


def _validate_authoritative_inputs_in_repo(
    *,
    repo_root: Path,
    intent_packet: MetaTestingIntentPacket,
) -> None:
    if [entry.input_id for entry in intent_packet.authoritative_inputs] != list(
        FROZEN_V37A_AUTHORITATIVE_INPUT_IDS
    ):
        raise MetaTestingEvidenceError("authoritative input ids must remain frozen")
    for entry in intent_packet.authoritative_inputs:
        if not entry.artifact_ref.startswith(("artifacts/", "docs/")):
            raise MetaTestingEvidenceError(
                "authoritative_inputs"
                f"[{entry.input_id}].artifact_ref must remain under docs/ or artifacts/"
            )
        path = _resolve_existing_repo_file(
            root=repo_root,
            path_text=entry.artifact_ref,
            field_name=f"authoritative_inputs[{entry.input_id}].artifact_ref",
        )
        actual_hash = _sha256_file(path)
        if actual_hash != entry.artifact_sha256:
            raise MetaTestingEvidenceError(
                f"authoritative_inputs[{entry.input_id}].artifact_sha256 must match repo file bytes"
            )


def _validate_parameter_slot_literal(
    *,
    repo_root: Path,
    slot: MetaExecutorParameterSlot,
    module: MetaModuleDescriptor,
    binding: MetaExecutorBinding,
) -> None:
    field_name = (
        f"modules[{module.module_id}].executor_bindings[{binding.binding_id}]."
        f"parameter_slots[{slot.slot_name}]"
    )
    if slot.value_origin == "soft_originated_input":
        if not binding.parameter_policy.soft_originated_inputs_allowed:
            raise MetaTestingEvidenceError(
                "checkpoint parameter policies must reject soft-originated inputs "
                "when they are not allowed"
            )
        return
    literal_value = slot.literal_value
    if literal_value is None:
        raise MetaTestingEvidenceError(f"{field_name}.literal_value must not be empty")
    if slot.slot_type == "boolean_literal":
        if literal_value not in {"true", "false"}:
            raise MetaTestingEvidenceError(f"{field_name}.literal_value must be true or false")
    elif slot.slot_type == "integer_literal":
        try:
            int(literal_value)
        except ValueError as exc:
            raise MetaTestingEvidenceError(
                f"{field_name}.literal_value must parse as an integer"
            ) from exc
    elif slot.slot_type == "phase_literal":
        if literal_value != V37A_REFERENCE_PHASE:
            raise MetaTestingEvidenceError(
                f"{field_name}.literal_value must equal {V37A_REFERENCE_PHASE!r}"
            )
    elif slot.slot_type in {"path_literal", "repo_root_literal"}:
        _resolve_existing_repo_file(
            root=repo_root,
            path_text=literal_value,
            field_name=f"{field_name}.literal_value",
        )


def _validate_parameter_policy_in_repo(
    *,
    repo_root: Path,
    module: MetaModuleDescriptor,
    binding: MetaExecutorBinding,
    policy: MetaExecutorParameterPolicy,
) -> None:
    if not policy.requires_typed_slots:
        raise MetaTestingEvidenceError("checkpoint parameter policies must require typed slots")
    if not policy.unchecked_shell_interpolation_forbidden:
        raise MetaTestingEvidenceError(
            "checkpoint parameter policies must forbid unchecked shell interpolation"
        )
    if "typed_slots_only" not in policy.validation_rules:
        raise MetaTestingEvidenceError(
            "checkpoint parameter policies must include typed_slots_only validation"
        )
    if "no_unchecked_shell_interpolation" not in policy.validation_rules:
        raise MetaTestingEvidenceError(
            "checkpoint parameter policies must include no_unchecked_shell_interpolation validation"
        )
    for slot in policy.parameter_slots:
        _validate_parameter_slot_literal(
            repo_root=repo_root,
            slot=slot,
            module=module,
            binding=binding,
        )


def _validate_dispatch_provenance_in_repo(
    *,
    repo_root: Path,
    dispatch_provenance: MetaReasoningDispatchProvenance,
    module: MetaModuleDescriptor,
) -> None:
    _resolve_existing_repo_file(
        root=repo_root,
        path_text=dispatch_provenance.prompt_surface_ref,
        field_name=f"modules[{module.module_id}].dispatch_provenance.prompt_surface_ref",
    )
    _resolve_existing_repo_file(
        root=repo_root,
        path_text=dispatch_provenance.template_version_ref,
        field_name=f"modules[{module.module_id}].dispatch_provenance.template_version_ref",
    )


def _validate_module_catalog_against_repo(
    *,
    repo_root: Path,
    module_catalog: MetaModuleCatalog,
) -> None:
    if module_catalog.drift_taxonomy != list(FROZEN_V37A_DRIFT_TAXONOMY):
        raise MetaTestingEvidenceError("drift taxonomy must remain frozen")
    if not module_catalog.hard_checkpoint_truth_boundary_preserved:
        raise MetaTestingEvidenceError("hard checkpoint truth boundary must remain preserved")
    if not module_catalog.no_hidden_prompt_only_module_authority:
        raise MetaTestingEvidenceError("hidden prompt-only module authority is not allowed")
    if not module_catalog.capability_to_executor_granularity_explicit:
        raise MetaTestingEvidenceError(
            "capability-to-executor granularity must remain explicit"
        )
    present_classes = {module.module_class for module in module_catalog.modules}
    if present_classes != set(FROZEN_V37A_MODULE_CLASSES):
        raise MetaTestingEvidenceError("module class coverage must remain frozen")

    for module in module_catalog.modules:
        for evidence_ref in module.expected_evidence_refs:
            _resolve_existing_repo_file(
                root=repo_root,
                path_text=evidence_ref,
                field_name=f"modules[{module.module_id}].expected_evidence_refs",
            )
        if module.predecessor_module_ids or module.successor_module_ids:
            raise MetaTestingEvidenceError(
                "v37a scope boundary preserved requires implicit sequence law to remain absent"
            )
        if module.module_class == "reasoning_module":
            if module.dispatch_provenance is None:
                raise MetaTestingEvidenceError(
                    f"reasoning module {module.module_id} must declare dispatch_provenance"
                )
            _validate_dispatch_provenance_in_repo(
                repo_root=repo_root,
                dispatch_provenance=module.dispatch_provenance,
                module=module,
            )
            continue

        if not module.executor_bindings:
            raise MetaTestingEvidenceError(
                f"hard module {module.module_id} must declare executor_bindings"
            )
        for binding in module.executor_bindings:
            if binding.binding_kind == "python_function_entrypoint":
                _assert_python_symbol_exists_in_repo(
                    repo_root=repo_root,
                    binding_ref=binding.binding_ref,
                    field_name=(
                        f"modules[{module.module_id}].executor_bindings[{binding.binding_id}].binding_ref"
                    ),
                )
            elif binding.binding_ref != V37A_OPERATOR_SURFACE:
                raise MetaTestingEvidenceError(
                    f"modules[{module.module_id}].executor_bindings"
                    f"[{binding.binding_id}].binding_ref "
                    "must remain the explicit operator acceptance boundary"
                )
            _validate_parameter_policy_in_repo(
                repo_root=repo_root,
                module=module,
                binding=binding,
                policy=binding.parameter_policy,
            )


def _assert_v37a_scope_boundary(
    *,
    module_catalog: MetaModuleCatalog,
) -> None:
    out_of_scope = set(FROZEN_V37A_OUT_OF_SCOPE_SURFACES)
    for module in module_catalog.modules:
        if out_of_scope.intersection(module.input_contract) or out_of_scope.intersection(
            module.output_contract
        ):
            raise MetaTestingEvidenceError(
                "v37a scope boundary preserved requires v37b/v37c surfaces to remain absent"
            )


def _assert_v37b_scope_boundary(
    *,
    sequence_contract: MetaLoopSequenceContract,
    run_trace: MetaLoopRunTrace,
) -> None:
    out_of_scope = set(FROZEN_V37B_OUT_OF_SCOPE_SURFACES)
    for step in sequence_contract.steps:
        if out_of_scope.intersection(step.required_inputs) or out_of_scope.intersection(
            step.expected_outputs
        ):
            raise MetaTestingEvidenceError(
                "v37b scope boundary preserved requires v37c/v37d/v37e surfaces to remain absent"
            )
    for step in run_trace.steps:
        if out_of_scope.intersection(step.consumed_inputs) or out_of_scope.intersection(
            step.emitted_outputs
        ):
            raise MetaTestingEvidenceError(
                "v37b scope boundary preserved requires v37c/v37d/v37e surfaces to remain absent"
            )


def _validate_v37b_observed_checkpoint_refs(
    *,
    repo_root: Path,
    run_trace: MetaLoopRunTrace,
) -> None:
    for step in run_trace.steps:
        for ref in step.observed_checkpoint_result_refs:
            _resolve_existing_repo_file(
                root=repo_root,
                path_text=ref,
                field_name=(
                    "run_trace.steps"
                    f"[{step.planned_step_id}].observed_checkpoint_result_refs"
                ),
                required_prefix="artifacts/",
            )


def _validate_v37c_manifest_against_repo(
    *,
    repo_root: Path,
    checkpoint_result_manifest: MetaLoopCheckpointResultManifest,
) -> None:
    for row in checkpoint_result_manifest.checkpoint_results:
        if row.executor_binding_ref != V37A_OPERATOR_SURFACE:
            _assert_python_symbol_exists_in_repo(
                repo_root=repo_root,
                binding_ref=row.executor_binding_ref,
                field_name=(
                    "checkpoint_results"
                    f"[{row.result_row_id}].executor_binding_ref"
                ),
            )
        for artifact in row.output_artifacts:
            artifact_path = _resolve_existing_repo_file(
                root=repo_root,
                path_text=artifact.artifact_ref,
                field_name=(
                    "checkpoint_results"
                    f"[{row.result_row_id}].output_artifacts[{artifact.artifact_role}]"
                    ".artifact_ref"
                ),
                required_prefix="artifacts/",
            )
            actual_hash = _sha256_file(artifact_path)
            if artifact.artifact_sha256 != actual_hash:
                raise MetaTestingEvidenceError(
                    "checkpoint_results"
                    f"[{row.result_row_id}].output_artifacts[{artifact.artifact_role}]"
                    ".artifact_sha256 must match repo file bytes"
                )


def _assert_v37c_scope_boundary(
    *,
    checkpoint_result_manifest: MetaLoopCheckpointResultManifest,
    executed_run_trace: MetaLoopRunTrace,
) -> None:
    out_of_scope = set(FROZEN_V37C_OUT_OF_SCOPE_SURFACES)
    for step in executed_run_trace.steps:
        if out_of_scope.intersection(step.consumed_inputs) or out_of_scope.intersection(
            step.emitted_outputs
        ):
            raise MetaTestingEvidenceError(
                "v37c scope boundary preserved requires v37d/v37e surfaces to remain absent"
            )
    for row in checkpoint_result_manifest.checkpoint_results:
        if out_of_scope.intersection(
            artifact.artifact_role for artifact in row.output_artifacts
        ):
            raise MetaTestingEvidenceError(
                "v37c scope boundary preserved requires v37d/v37e surfaces to remain absent"
            )


def materialize_v37a_meta_intent_module_catalog_evidence(
    *,
    repo_root: Path,
    output_path: str = DEFAULT_V37A_META_INTENT_MODULE_CATALOG_EVIDENCE_PATH,
    baseline_metrics_path: str = DEFAULT_V65_BASELINE_METRICS_PATH,
    current_metrics_path: str,
    meta_testing_intent_packet_schema_path: str = DEFAULT_META_TESTING_INTENT_PACKET_SCHEMA_PATH,
    meta_module_catalog_schema_path: str = DEFAULT_META_MODULE_CATALOG_SCHEMA_PATH,
    meta_testing_intent_packet_reference_path: str = (
        DEFAULT_META_TESTING_INTENT_PACKET_REFERENCE_PATH
    ),
    meta_module_catalog_reference_path: str = DEFAULT_META_MODULE_CATALOG_REFERENCE_PATH,
) -> MaterializedMetaTestingEvidence:
    repo_root = repo_root.resolve()
    if not repo_root.is_dir():
        raise MetaTestingEvidenceError("repository root does not exist")
    if baseline_metrics_path != DEFAULT_V65_BASELINE_METRICS_PATH:
        raise MetaTestingEvidenceError(
            "baseline_metrics_path must point to the frozen v65 closeout metrics artifact"
        )

    output_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=output_path,
        field_name="output_path",
        required_prefix="artifacts/",
    )
    baseline_metrics_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=baseline_metrics_path,
        field_name="baseline_metrics_path",
        required_prefix="artifacts/",
    )
    current_metrics_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=current_metrics_path,
        field_name="current_metrics_path",
        required_prefix="artifacts/",
    )
    intent_schema_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_testing_intent_packet_schema_path,
        field_name="meta_testing_intent_packet_schema_path",
        required_prefix="packages/",
    )
    module_catalog_schema_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_module_catalog_schema_path,
        field_name="meta_module_catalog_schema_path",
        required_prefix="packages/",
    )
    intent_reference_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_testing_intent_packet_reference_path,
        field_name="meta_testing_intent_packet_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    module_catalog_reference_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_module_catalog_reference_path,
        field_name="meta_module_catalog_reference_path",
        required_prefix="apps/api/fixtures/",
    )

    baseline_metrics = _load_stop_gate_metrics(
        path=baseline_metrics_file,
        field_name="baseline_metrics_path",
    )
    current_metrics = _load_stop_gate_metrics(
        path=current_metrics_file,
        field_name="current_metrics_path",
    )
    baseline_metric_keys = set(baseline_metrics["metrics"].keys())
    current_metric_keys = set(current_metrics["metrics"].keys())
    if len(current_metric_keys) != EXPECTED_METRIC_KEY_CARDINALITY:
        raise MetaTestingEvidenceError(
            "metric key cardinality must remain frozen at "
            f"{EXPECTED_METRIC_KEY_CARDINALITY}"
        )
    if baseline_metric_keys != current_metric_keys:
        raise MetaTestingEvidenceError("metric key set must remain exactly equal to v65")

    intent_schema_payload = _load_frozen_schema(
        path=intent_schema_file,
        field_name="meta_testing_intent_packet_schema_path",
        model_type=MetaTestingIntentPacket,
    )
    module_catalog_schema_payload = _load_frozen_schema(
        path=module_catalog_schema_file,
        field_name="meta_module_catalog_schema_path",
        model_type=MetaModuleCatalog,
    )
    intent_payload, intent_packet = _load_validated_model(
        path=intent_reference_file,
        field_name="meta_testing_intent_packet_reference_path",
        model_type=MetaTestingIntentPacket,
    )
    module_catalog_payload, module_catalog = _load_validated_model(
        path=module_catalog_reference_file,
        field_name="meta_module_catalog_reference_path",
        model_type=MetaModuleCatalog,
    )

    try:
        assert_v37a_reference_bundle_consistent(
            intent_packet=intent_packet,
            module_catalog=module_catalog,
        )
        _validate_authoritative_inputs_in_repo(
            repo_root=repo_root,
            intent_packet=intent_packet,
        )
        _validate_module_catalog_against_repo(
            repo_root=repo_root,
            module_catalog=module_catalog,
        )
        _assert_v37a_scope_boundary(module_catalog=module_catalog)
    except ValueError as exc:
        raise MetaTestingEvidenceError(str(exc)) from exc

    evidence = V37AMetaIntentModuleCatalogEvidence(
        evidence_input_path=output_path,
        meta_testing_intent_packet_schema_path=meta_testing_intent_packet_schema_path,
        meta_testing_intent_packet_schema_hash=_sha256_canonical_json(intent_schema_payload),
        meta_module_catalog_schema_path=meta_module_catalog_schema_path,
        meta_module_catalog_schema_hash=_sha256_canonical_json(module_catalog_schema_payload),
        meta_testing_intent_packet_reference_path=meta_testing_intent_packet_reference_path,
        meta_testing_intent_packet_reference_hash=_sha256_canonical_json(intent_payload),
        meta_module_catalog_reference_path=meta_module_catalog_reference_path,
        meta_module_catalog_reference_hash=_sha256_canonical_json(module_catalog_payload),
        module_class_enum_frozen=True,
        drift_taxonomy_enum_frozen=True,
        reference_instance_pair_binding_verified=True,
        authoritative_input_refs_and_hashes_verified=True,
        checkpoint_executor_bindings_verified=True,
        capability_to_executor_granularity_verified=True,
        checkpoint_parameter_safety_verified=True,
        reasoning_dispatch_provenance_verified=True,
        hard_checkpoint_truth_boundary_preserved=True,
        v37a_scope_boundary_preserved=True,
        verification_passed=True,
        metric_key_cardinality=len(current_metric_keys),
        metric_key_exact_set_equal_v65=True,
        notes=(
            "v66 closeout evidence remains pre-sequence, pre-run-trace, pre-diagnostics, "
            "and pre-control-update; it verifies the typed meta intent and module "
            "ontology substrate only."
        ),
    )
    payload = evidence.model_dump(mode="json", by_alias=True)
    output_file.parent.mkdir(parents=True, exist_ok=True)
    output_file.write_text(_pretty_canonical_json(payload), encoding="utf-8")
    return MaterializedMetaTestingEvidence(
        path=output_path,
        hash=_sha256_canonical_json(payload),
        payload=payload,
    )


def materialize_v37b_sequence_trace_evidence(
    *,
    repo_root: Path,
    output_path: str = DEFAULT_V37B_SEQUENCE_TRACE_EVIDENCE_PATH,
    baseline_metrics_path: str = DEFAULT_V66_BASELINE_METRICS_PATH,
    current_metrics_path: str,
    meta_testing_intent_packet_schema_path: str = DEFAULT_META_TESTING_INTENT_PACKET_SCHEMA_PATH,
    meta_module_catalog_schema_path: str = DEFAULT_META_MODULE_CATALOG_SCHEMA_PATH,
    meta_loop_sequence_contract_schema_path: str = (
        DEFAULT_META_LOOP_SEQUENCE_CONTRACT_SCHEMA_PATH
    ),
    meta_loop_run_trace_schema_path: str = DEFAULT_META_LOOP_RUN_TRACE_SCHEMA_PATH,
    meta_testing_intent_packet_reference_path: str = (
        DEFAULT_META_TESTING_INTENT_PACKET_REFERENCE_PATH
    ),
    meta_module_catalog_reference_path: str = DEFAULT_META_MODULE_CATALOG_REFERENCE_PATH,
    meta_loop_sequence_contract_reference_path: str = (
        DEFAULT_META_LOOP_SEQUENCE_CONTRACT_REFERENCE_PATH
    ),
    meta_loop_run_trace_reference_path: str = DEFAULT_META_LOOP_RUN_TRACE_REFERENCE_PATH,
    v37a_meta_intent_module_catalog_evidence_path: str = (
        DEFAULT_V37A_META_INTENT_MODULE_CATALOG_EVIDENCE_PATH
    ),
) -> MaterializedMetaTestingEvidence:
    repo_root = repo_root.resolve()
    if not repo_root.is_dir():
        raise MetaTestingEvidenceError("repository root does not exist")
    if baseline_metrics_path != DEFAULT_V66_BASELINE_METRICS_PATH:
        raise MetaTestingEvidenceError(
            "baseline_metrics_path must point to the frozen v66 closeout metrics artifact"
        )

    output_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=output_path,
        field_name="output_path",
        required_prefix="artifacts/",
    )
    baseline_metrics_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=baseline_metrics_path,
        field_name="baseline_metrics_path",
        required_prefix="artifacts/",
    )
    current_metrics_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=current_metrics_path,
        field_name="current_metrics_path",
        required_prefix="artifacts/",
    )
    intent_schema_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_testing_intent_packet_schema_path,
        field_name="meta_testing_intent_packet_schema_path",
        required_prefix="packages/",
    )
    module_catalog_schema_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_module_catalog_schema_path,
        field_name="meta_module_catalog_schema_path",
        required_prefix="packages/",
    )
    sequence_schema_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_loop_sequence_contract_schema_path,
        field_name="meta_loop_sequence_contract_schema_path",
        required_prefix="packages/",
    )
    run_trace_schema_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_loop_run_trace_schema_path,
        field_name="meta_loop_run_trace_schema_path",
        required_prefix="packages/",
    )
    intent_reference_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_testing_intent_packet_reference_path,
        field_name="meta_testing_intent_packet_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    module_catalog_reference_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_module_catalog_reference_path,
        field_name="meta_module_catalog_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    sequence_reference_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_loop_sequence_contract_reference_path,
        field_name="meta_loop_sequence_contract_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    run_trace_reference_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_loop_run_trace_reference_path,
        field_name="meta_loop_run_trace_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    v37a_evidence_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=v37a_meta_intent_module_catalog_evidence_path,
        field_name="v37a_meta_intent_module_catalog_evidence_path",
        required_prefix="artifacts/",
    )

    baseline_metrics = _load_stop_gate_metrics(
        path=baseline_metrics_file,
        field_name="baseline_metrics_path",
    )
    current_metrics = _load_stop_gate_metrics(
        path=current_metrics_file,
        field_name="current_metrics_path",
    )
    baseline_metric_keys = set(baseline_metrics["metrics"].keys())
    current_metric_keys = set(current_metrics["metrics"].keys())
    if len(current_metric_keys) != EXPECTED_METRIC_KEY_CARDINALITY:
        raise MetaTestingEvidenceError("metric key cardinality must remain frozen at 80")
    if baseline_metric_keys != current_metric_keys:
        raise MetaTestingEvidenceError("metric key set must remain exactly equal to v66")

    intent_schema_payload = _load_frozen_schema(
        path=intent_schema_file,
        field_name="meta_testing_intent_packet_schema_path",
        model_type=MetaTestingIntentPacket,
    )
    module_catalog_schema_payload = _load_frozen_schema(
        path=module_catalog_schema_file,
        field_name="meta_module_catalog_schema_path",
        model_type=MetaModuleCatalog,
    )
    sequence_schema_payload = _load_frozen_schema(
        path=sequence_schema_file,
        field_name="meta_loop_sequence_contract_schema_path",
        model_type=MetaLoopSequenceContract,
    )
    run_trace_schema_payload = _load_frozen_schema(
        path=run_trace_schema_file,
        field_name="meta_loop_run_trace_schema_path",
        model_type=MetaLoopRunTrace,
    )
    intent_payload, intent_packet = _load_validated_model(
        path=intent_reference_file,
        field_name="meta_testing_intent_packet_reference_path",
        model_type=MetaTestingIntentPacket,
    )
    module_catalog_payload, module_catalog = _load_validated_model(
        path=module_catalog_reference_file,
        field_name="meta_module_catalog_reference_path",
        model_type=MetaModuleCatalog,
    )
    sequence_payload, sequence_contract = _load_validated_model(
        path=sequence_reference_file,
        field_name="meta_loop_sequence_contract_reference_path",
        model_type=MetaLoopSequenceContract,
        exclude_none=False,
    )
    run_trace_payload, run_trace = _load_validated_model(
        path=run_trace_reference_file,
        field_name="meta_loop_run_trace_reference_path",
        model_type=MetaLoopRunTrace,
        exclude_none=True,
    )
    v37a_evidence_payload, v37a_evidence = _load_validated_model(
        path=v37a_evidence_file,
        field_name="v37a_meta_intent_module_catalog_evidence_path",
        model_type=V37AMetaIntentModuleCatalogEvidence,
        by_alias=True,
    )
    if not v37a_evidence.verification_passed:
        raise MetaTestingEvidenceError(
            "v37a_meta_intent_module_catalog_evidence_path must be a passed v37a evidence artifact"
        )

    try:
        assert_v37b_reference_bundle_consistent(
            intent_packet=intent_packet,
            module_catalog=module_catalog,
            sequence_contract=sequence_contract,
            run_trace=run_trace,
        )
        _validate_v37b_observed_checkpoint_refs(
            repo_root=repo_root,
            run_trace=run_trace,
        )
        _assert_v37b_scope_boundary(
            sequence_contract=sequence_contract,
            run_trace=run_trace,
        )
    except ValueError as exc:
        raise MetaTestingEvidenceError(str(exc)) from exc

    if run_trace.trace_mode != V37B_REFERENCE_TRACE_MODE:
        raise MetaTestingEvidenceError(
            f"meta_loop_run_trace_reference_path must use {V37B_REFERENCE_TRACE_MODE!r}"
        )

    evidence = V37BSequenceTraceEvidence(
        evidence_input_path=output_path,
        meta_testing_intent_packet_schema_path=meta_testing_intent_packet_schema_path,
        meta_testing_intent_packet_schema_hash=_sha256_canonical_json(intent_schema_payload),
        meta_module_catalog_schema_path=meta_module_catalog_schema_path,
        meta_module_catalog_schema_hash=_sha256_canonical_json(module_catalog_schema_payload),
        meta_loop_sequence_contract_schema_path=meta_loop_sequence_contract_schema_path,
        meta_loop_sequence_contract_schema_hash=_sha256_canonical_json(sequence_schema_payload),
        meta_loop_run_trace_schema_path=meta_loop_run_trace_schema_path,
        meta_loop_run_trace_schema_hash=_sha256_canonical_json(run_trace_schema_payload),
        meta_testing_intent_packet_reference_path=meta_testing_intent_packet_reference_path,
        meta_testing_intent_packet_reference_hash=_sha256_canonical_json(intent_payload),
        meta_module_catalog_reference_path=meta_module_catalog_reference_path,
        meta_module_catalog_reference_hash=_sha256_canonical_json(module_catalog_payload),
        meta_loop_sequence_contract_reference_path=meta_loop_sequence_contract_reference_path,
        meta_loop_sequence_contract_reference_hash=_sha256_canonical_json(sequence_payload),
        meta_loop_run_trace_reference_path=meta_loop_run_trace_reference_path,
        meta_loop_run_trace_reference_hash=_sha256_canonical_json(run_trace_payload),
        v37a_meta_intent_module_catalog_evidence_path=v37a_meta_intent_module_catalog_evidence_path,
        v37a_meta_intent_module_catalog_evidence_hash=_sha256_canonical_json(v37a_evidence_payload),
        v37a_reference_tuple_consumed_without_drift=True,
        sequence_trace_reference_pair_binding_verified=True,
        reference_trace_mode_not_executed_verified=True,
        step_order_and_phase_boundary_verified=True,
        step_binding_nullability_explicit=True,
        retry_representation_explicit=True,
        checkpoint_bindings_resolved_via_v37a_catalog=True,
        reasoning_dispatch_bindings_resolved_per_step=True,
        operator_gate_surfaces_verified=True,
        reasoning_claims_bound_to_downstream_gates=True,
        operational_influence_distinct_from_accepted_compilation=True,
        observed_checkpoint_result_refs_preaccepted_only=True,
        v37b_scope_boundary_preserved=True,
        verification_passed=True,
        metric_key_cardinality=len(current_metric_keys),
        metric_key_exact_set_equal_v66=True,
        notes=(
            "v67 closeout evidence remains pre-execution, pre-checkpoint-result-manifest, "
            "pre-diagnostics, and pre-control-update; it verifies typed sequence law and "
            "reference trace law only."
        ),
    )
    payload = evidence.model_dump(mode="json", by_alias=True)
    output_file.parent.mkdir(parents=True, exist_ok=True)
    output_file.write_text(_pretty_canonical_json(payload), encoding="utf-8")
    return MaterializedMetaTestingEvidence(
        path=output_path,
        hash=_sha256_canonical_json(payload),
        payload=payload,
    )


def materialize_v37c_reference_loop_evidence(
    *,
    repo_root: Path,
    output_path: str = DEFAULT_V37C_REFERENCE_LOOP_EVIDENCE_PATH,
    baseline_metrics_path: str = DEFAULT_V67_BASELINE_METRICS_PATH,
    current_metrics_path: str,
    meta_testing_intent_packet_schema_path: str = DEFAULT_META_TESTING_INTENT_PACKET_SCHEMA_PATH,
    meta_module_catalog_schema_path: str = DEFAULT_META_MODULE_CATALOG_SCHEMA_PATH,
    meta_loop_sequence_contract_schema_path: str = (
        DEFAULT_META_LOOP_SEQUENCE_CONTRACT_SCHEMA_PATH
    ),
    meta_loop_run_trace_schema_path: str = DEFAULT_META_LOOP_RUN_TRACE_SCHEMA_PATH,
    meta_loop_checkpoint_result_manifest_schema_path: str = (
        DEFAULT_META_LOOP_CHECKPOINT_RESULT_MANIFEST_SCHEMA_PATH
    ),
    meta_testing_intent_packet_reference_path: str = (
        DEFAULT_META_TESTING_INTENT_PACKET_REFERENCE_PATH
    ),
    meta_module_catalog_reference_path: str = DEFAULT_META_MODULE_CATALOG_REFERENCE_PATH,
    meta_loop_sequence_contract_reference_path: str = (
        DEFAULT_META_LOOP_SEQUENCE_CONTRACT_REFERENCE_PATH
    ),
    meta_loop_run_trace_reference_path: str = DEFAULT_META_LOOP_RUN_TRACE_REFERENCE_PATH,
    meta_loop_checkpoint_result_manifest_reference_path: str = (
        DEFAULT_META_LOOP_CHECKPOINT_RESULT_MANIFEST_REFERENCE_PATH
    ),
    executed_meta_loop_run_trace_reference_path: str = (
        DEFAULT_V37C_EXECUTED_META_LOOP_RUN_TRACE_REFERENCE_PATH
    ),
    v37a_meta_intent_module_catalog_evidence_path: str = (
        DEFAULT_V37A_META_INTENT_MODULE_CATALOG_EVIDENCE_PATH
    ),
    v37b_sequence_trace_evidence_path: str = DEFAULT_V37B_SEQUENCE_TRACE_EVIDENCE_PATH,
) -> MaterializedMetaTestingEvidence:
    repo_root = repo_root.resolve()
    if not repo_root.is_dir():
        raise MetaTestingEvidenceError("repository root does not exist")
    if baseline_metrics_path != DEFAULT_V67_BASELINE_METRICS_PATH:
        raise MetaTestingEvidenceError(
            "baseline_metrics_path must point to the frozen v67 closeout metrics artifact"
        )
    if executed_meta_loop_run_trace_reference_path == meta_loop_run_trace_reference_path:
        raise MetaTestingEvidenceError(
            "executed_meta_loop_run_trace_reference_path must remain distinct from the "
            "frozen v67 reference trace"
        )

    output_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=output_path,
        field_name="output_path",
        required_prefix="artifacts/",
    )
    baseline_metrics_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=baseline_metrics_path,
        field_name="baseline_metrics_path",
        required_prefix="artifacts/",
    )
    current_metrics_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=current_metrics_path,
        field_name="current_metrics_path",
        required_prefix="artifacts/",
    )
    intent_schema_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_testing_intent_packet_schema_path,
        field_name="meta_testing_intent_packet_schema_path",
        required_prefix="packages/",
    )
    module_catalog_schema_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_module_catalog_schema_path,
        field_name="meta_module_catalog_schema_path",
        required_prefix="packages/",
    )
    sequence_schema_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_loop_sequence_contract_schema_path,
        field_name="meta_loop_sequence_contract_schema_path",
        required_prefix="packages/",
    )
    run_trace_schema_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_loop_run_trace_schema_path,
        field_name="meta_loop_run_trace_schema_path",
        required_prefix="packages/",
    )
    manifest_schema_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_loop_checkpoint_result_manifest_schema_path,
        field_name="meta_loop_checkpoint_result_manifest_schema_path",
        required_prefix="packages/",
    )
    intent_reference_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_testing_intent_packet_reference_path,
        field_name="meta_testing_intent_packet_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    module_catalog_reference_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_module_catalog_reference_path,
        field_name="meta_module_catalog_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    sequence_reference_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_loop_sequence_contract_reference_path,
        field_name="meta_loop_sequence_contract_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    run_trace_reference_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_loop_run_trace_reference_path,
        field_name="meta_loop_run_trace_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    manifest_reference_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=meta_loop_checkpoint_result_manifest_reference_path,
        field_name="meta_loop_checkpoint_result_manifest_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    executed_run_trace_reference_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=executed_meta_loop_run_trace_reference_path,
        field_name="executed_meta_loop_run_trace_reference_path",
        required_prefix="apps/api/fixtures/",
    )
    v37a_evidence_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=v37a_meta_intent_module_catalog_evidence_path,
        field_name="v37a_meta_intent_module_catalog_evidence_path",
        required_prefix="artifacts/",
    )
    v37b_evidence_file = _resolve_existing_repo_file(
        root=repo_root,
        path_text=v37b_sequence_trace_evidence_path,
        field_name="v37b_sequence_trace_evidence_path",
        required_prefix="artifacts/",
    )

    baseline_metrics = _load_stop_gate_metrics(
        path=baseline_metrics_file,
        field_name="baseline_metrics_path",
    )
    current_metrics = _load_stop_gate_metrics(
        path=current_metrics_file,
        field_name="current_metrics_path",
    )
    baseline_metric_keys = set(baseline_metrics["metrics"].keys())
    current_metric_keys = set(current_metrics["metrics"].keys())
    if len(current_metric_keys) != EXPECTED_METRIC_KEY_CARDINALITY:
        raise MetaTestingEvidenceError(
            "metric key cardinality must remain frozen at "
            f"{EXPECTED_METRIC_KEY_CARDINALITY}"
        )
    if baseline_metric_keys != current_metric_keys:
        raise MetaTestingEvidenceError("metric key set must remain exactly equal to v67")

    intent_schema_payload = _load_frozen_schema(
        path=intent_schema_file,
        field_name="meta_testing_intent_packet_schema_path",
        model_type=MetaTestingIntentPacket,
    )
    module_catalog_schema_payload = _load_frozen_schema(
        path=module_catalog_schema_file,
        field_name="meta_module_catalog_schema_path",
        model_type=MetaModuleCatalog,
    )
    sequence_schema_payload = _load_frozen_schema(
        path=sequence_schema_file,
        field_name="meta_loop_sequence_contract_schema_path",
        model_type=MetaLoopSequenceContract,
    )
    run_trace_schema_payload = _load_frozen_schema(
        path=run_trace_schema_file,
        field_name="meta_loop_run_trace_schema_path",
        model_type=MetaLoopRunTrace,
    )
    manifest_schema_payload = _load_frozen_schema(
        path=manifest_schema_file,
        field_name="meta_loop_checkpoint_result_manifest_schema_path",
        model_type=MetaLoopCheckpointResultManifest,
    )
    intent_payload, intent_packet = _load_validated_model(
        path=intent_reference_file,
        field_name="meta_testing_intent_packet_reference_path",
        model_type=MetaTestingIntentPacket,
    )
    module_catalog_payload, module_catalog = _load_validated_model(
        path=module_catalog_reference_file,
        field_name="meta_module_catalog_reference_path",
        model_type=MetaModuleCatalog,
    )
    sequence_payload, sequence_contract = _load_validated_model(
        path=sequence_reference_file,
        field_name="meta_loop_sequence_contract_reference_path",
        model_type=MetaLoopSequenceContract,
        exclude_none=False,
    )
    reference_run_trace_payload, reference_run_trace = _load_validated_model(
        path=run_trace_reference_file,
        field_name="meta_loop_run_trace_reference_path",
        model_type=MetaLoopRunTrace,
        exclude_none=True,
    )
    manifest_payload, checkpoint_result_manifest = _load_validated_model(
        path=manifest_reference_file,
        field_name="meta_loop_checkpoint_result_manifest_reference_path",
        model_type=MetaLoopCheckpointResultManifest,
        exclude_none=False,
    )
    _, executed_run_trace_raw_payload = _load_json_dict(
        path=executed_run_trace_reference_file,
        field_name="executed_meta_loop_run_trace_reference_path",
    )
    if executed_run_trace_raw_payload.get("trace_mode") != V37C_EXECUTED_TRACE_MODE:
        raise MetaTestingEvidenceError(
            "executed_meta_loop_run_trace_reference_path must use "
            f"{V37C_EXECUTED_TRACE_MODE!r}"
        )
    executed_run_trace_payload, executed_run_trace = _load_validated_model(
        path=executed_run_trace_reference_file,
        field_name="executed_meta_loop_run_trace_reference_path",
        model_type=MetaLoopRunTrace,
        exclude_none=True,
    )
    v37a_evidence_payload, v37a_evidence = _load_validated_model(
        path=v37a_evidence_file,
        field_name="v37a_meta_intent_module_catalog_evidence_path",
        model_type=V37AMetaIntentModuleCatalogEvidence,
        by_alias=True,
    )
    v37b_evidence_payload, v37b_evidence = _load_validated_model(
        path=v37b_evidence_file,
        field_name="v37b_sequence_trace_evidence_path",
        model_type=V37BSequenceTraceEvidence,
        by_alias=True,
    )
    if not v37a_evidence.verification_passed:
        raise MetaTestingEvidenceError(
            "v37a_meta_intent_module_catalog_evidence_path must be a passed v37a evidence artifact"
        )
    if not v37b_evidence.verification_passed:
        raise MetaTestingEvidenceError(
            "v37b_sequence_trace_evidence_path must be a passed v37b evidence artifact"
        )

    if checkpoint_result_manifest.schema != META_LOOP_CHECKPOINT_RESULT_MANIFEST_SCHEMA:
        raise MetaTestingEvidenceError(
            "meta_loop_checkpoint_result_manifest_reference_path must use "
            f"{META_LOOP_CHECKPOINT_RESULT_MANIFEST_SCHEMA!r}"
        )
    if executed_run_trace.trace_mode != V37C_EXECUTED_TRACE_MODE:
        raise MetaTestingEvidenceError(
            "executed_meta_loop_run_trace_reference_path must use "
            f"{V37C_EXECUTED_TRACE_MODE!r}"
        )
    if (
        executed_run_trace.checkpoint_result_manifest_ref
        != meta_loop_checkpoint_result_manifest_reference_path
    ):
        raise MetaTestingEvidenceError(
            "executed_meta_loop_run_trace_reference_path must bind the accepted "
            "meta_loop_checkpoint_result_manifest_reference_path"
        )

    try:
        assert_v37c_reference_bundle_consistent(
            intent_packet=intent_packet,
            module_catalog=module_catalog,
            sequence_contract=sequence_contract,
            reference_run_trace=reference_run_trace,
            executed_run_trace=executed_run_trace,
            checkpoint_result_manifest=checkpoint_result_manifest,
        )
        _validate_v37c_manifest_against_repo(
            repo_root=repo_root,
            checkpoint_result_manifest=checkpoint_result_manifest,
        )
        _assert_v37c_scope_boundary(
            checkpoint_result_manifest=checkpoint_result_manifest,
            executed_run_trace=executed_run_trace,
        )
    except ValueError as exc:
        raise MetaTestingEvidenceError(str(exc)) from exc

    evidence = V37CReferenceLoopEvidence(
        evidence_input_path=output_path,
        meta_testing_intent_packet_schema_path=meta_testing_intent_packet_schema_path,
        meta_testing_intent_packet_schema_hash=_sha256_canonical_json(intent_schema_payload),
        meta_module_catalog_schema_path=meta_module_catalog_schema_path,
        meta_module_catalog_schema_hash=_sha256_canonical_json(module_catalog_schema_payload),
        meta_loop_sequence_contract_schema_path=meta_loop_sequence_contract_schema_path,
        meta_loop_sequence_contract_schema_hash=_sha256_canonical_json(sequence_schema_payload),
        meta_loop_run_trace_schema_path=meta_loop_run_trace_schema_path,
        meta_loop_run_trace_schema_hash=_sha256_canonical_json(run_trace_schema_payload),
        meta_loop_checkpoint_result_manifest_schema_path=(
            meta_loop_checkpoint_result_manifest_schema_path
        ),
        meta_loop_checkpoint_result_manifest_schema_hash=_sha256_canonical_json(
            manifest_schema_payload
        ),
        meta_testing_intent_packet_reference_path=meta_testing_intent_packet_reference_path,
        meta_testing_intent_packet_reference_hash=_sha256_canonical_json(intent_payload),
        meta_module_catalog_reference_path=meta_module_catalog_reference_path,
        meta_module_catalog_reference_hash=_sha256_canonical_json(module_catalog_payload),
        meta_loop_sequence_contract_reference_path=meta_loop_sequence_contract_reference_path,
        meta_loop_sequence_contract_reference_hash=_sha256_canonical_json(sequence_payload),
        meta_loop_run_trace_reference_path=meta_loop_run_trace_reference_path,
        meta_loop_run_trace_reference_hash=_sha256_canonical_json(reference_run_trace_payload),
        meta_loop_checkpoint_result_manifest_reference_path=(
            meta_loop_checkpoint_result_manifest_reference_path
        ),
        meta_loop_checkpoint_result_manifest_reference_hash=_sha256_canonical_json(
            manifest_payload
        ),
        executed_meta_loop_run_trace_reference_path=(
            executed_meta_loop_run_trace_reference_path
        ),
        executed_meta_loop_run_trace_reference_hash=_sha256_canonical_json(
            executed_run_trace_payload
        ),
        v37a_meta_intent_module_catalog_evidence_path=(
            v37a_meta_intent_module_catalog_evidence_path
        ),
        v37a_meta_intent_module_catalog_evidence_hash=_sha256_canonical_json(
            v37a_evidence_payload
        ),
        v37b_sequence_trace_evidence_path=v37b_sequence_trace_evidence_path,
        v37b_sequence_trace_evidence_hash=_sha256_canonical_json(v37b_evidence_payload),
        v37a_reference_tuple_consumed_without_drift=True,
        v37b_reference_tuple_consumed_without_drift=True,
        executed_reference_run_emitted=True,
        checkpoint_result_manifest_emitted_and_hash_bound=True,
        executed_run_trace_artifact_distinct_from_v67_reference_trace=True,
        executed_run_trace_mode_verified=True,
        hard_checkpoint_results_captured_from_actual_executors=True,
        executed_capability_subset_declared_intentionally=True,
        authoritative_stop_gate_executor_binding_verified=True,
        actual_branch_and_retry_outcomes_verified=True,
        failed_checkpoint_attempts_still_emit_normalized_result_rows=True,
        output_artifact_refs_and_hashes_verified=True,
        reasoning_vs_checkpoint_truth_boundary_preserved=True,
        executed_step_order_matches_v37b_contract=True,
        v37c_scope_boundary_preserved=True,
        verification_passed=True,
        metric_key_cardinality=len(current_metric_keys),
        metric_key_exact_set_equal_v67=True,
        notes=(
            "v68 closeout evidence is the first executable recursive-compilation lane; "
            "it verifies the executed reference run, checkpoint result manifest, actual "
            "executor/output binding, and truth-boundary preservation without releasing "
            "diagnostics, conformance, or control-update surfaces."
        ),
    )
    payload = evidence.model_dump(mode="json", by_alias=True)
    output_file.parent.mkdir(parents=True, exist_ok=True)
    output_file.write_text(_pretty_canonical_json(payload), encoding="utf-8")
    return MaterializedMetaTestingEvidence(
        path=output_path,
        hash=_sha256_canonical_json(payload),
        payload=payload,
    )


__all__ = [
    "DEFAULT_META_LOOP_CHECKPOINT_RESULT_MANIFEST_REFERENCE_PATH",
    "DEFAULT_META_LOOP_CHECKPOINT_RESULT_MANIFEST_SCHEMA_PATH",
    "DEFAULT_META_LOOP_RUN_TRACE_REFERENCE_PATH",
    "DEFAULT_META_LOOP_RUN_TRACE_SCHEMA_PATH",
    "DEFAULT_META_LOOP_SEQUENCE_CONTRACT_REFERENCE_PATH",
    "DEFAULT_META_LOOP_SEQUENCE_CONTRACT_SCHEMA_PATH",
    "DEFAULT_META_MODULE_CATALOG_REFERENCE_PATH",
    "DEFAULT_META_MODULE_CATALOG_SCHEMA_PATH",
    "DEFAULT_META_TESTING_INTENT_PACKET_REFERENCE_PATH",
    "DEFAULT_META_TESTING_INTENT_PACKET_SCHEMA_PATH",
    "DEFAULT_V37C_EXECUTED_META_LOOP_RUN_TRACE_REFERENCE_PATH",
    "DEFAULT_V37C_REFERENCE_LOOP_EVIDENCE_PATH",
    "DEFAULT_V37A_META_INTENT_MODULE_CATALOG_EVIDENCE_PATH",
    "DEFAULT_V37B_SEQUENCE_TRACE_EVIDENCE_PATH",
    "DEFAULT_V65_BASELINE_METRICS_PATH",
    "DEFAULT_V66_BASELINE_METRICS_PATH",
    "DEFAULT_V67_BASELINE_METRICS_PATH",
    "MaterializedMetaTestingEvidence",
    "MetaTestingEvidenceError",
    "V37A_META_INTENT_MODULE_CATALOG_CONTRACT_SOURCE",
    "V37A_META_INTENT_MODULE_CATALOG_EVIDENCE_SCHEMA",
    "V37AMetaIntentModuleCatalogEvidence",
    "V37B_SEQUENCE_TRACE_CONTRACT_SOURCE",
    "V37B_SEQUENCE_TRACE_EVIDENCE_SCHEMA",
    "V37BSequenceTraceEvidence",
    "V37C_REFERENCE_LOOP_CONTRACT_SOURCE",
    "V37C_REFERENCE_LOOP_EVIDENCE_SCHEMA",
    "V37CReferenceLoopEvidence",
    "materialize_v37a_meta_intent_module_catalog_evidence",
    "materialize_v37b_sequence_trace_evidence",
    "materialize_v37c_reference_loop_evidence",
]
