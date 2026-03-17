from __future__ import annotations

import ast
import hashlib
from copy import deepcopy
from pathlib import Path
from typing import Any, Literal

from adeu_ir.repo import repo_root
from pydantic import BaseModel, ConfigDict, Field, model_validator

MetaTestingIntentPacketSchemaVersion = Literal["meta_testing_intent_packet@1"]
MetaModuleCatalogSchemaVersion = Literal["meta_module_catalog@1"]
MetaLoopSequenceContractSchemaVersion = Literal["meta_loop_sequence_contract@1"]
MetaLoopCheckpointResultManifestSchemaVersion = Literal["meta_loop_checkpoint_result_manifest@1"]
MetaLoopRunTraceSchemaVersion = Literal["meta_loop_run_trace@1"]
MetaReferenceLoopFamily = Literal["arc_bundle_recursive_compilation_loop"]
MetaReferenceAnchorShape = Literal["arc_closeout_bundle_instance"]
MetaReferencePhase = Literal["closeout"]
MetaModuleClass = Literal[
    "reasoning_module",
    "checkpoint_module",
    "evidence_gate_module",
    "operator_gate_module",
]
MetaCheckpointCapability = Literal[
    "artifact_consistency_lint",
    "bundle_lint",
    "committed_event_stream_validation",
    "instruction_policy_validation",
    "quality_dashboard_build",
    "semantic_closeout_lint",
    "stop_gate_metrics_build",
]
MetaAuthorityStatus = Literal[
    "hard_checkpoint_truth",
    "hard_evidence_gate",
    "operator_acceptance_gate",
    "soft_influence_only",
]
MetaCapabilityGranularity = Literal["executor_family", "single_executor", "soft_dispatch"]
MetaExecutorBindingKind = Literal["operator_surface", "python_function_entrypoint"]
MetaParameterSlotType = Literal[
    "boolean_literal",
    "integer_literal",
    "path_literal",
    "phase_literal",
    "repo_root_literal",
    "string_literal",
]
MetaParameterValueOrigin = Literal["hardcoded_literal", "soft_originated_input"]
MetaParameterValidationRule = Literal[
    "literal_or_validated_value_only",
    "no_unchecked_shell_interpolation",
    "typed_slots_only",
]
MetaADEUDimension = Literal["deontics", "epistemics", "ontology", "utility"]
MetaDriftClass = Literal[
    "deontic_drift",
    "epistemic_drift",
    "ontology_drift",
    "utility_drift",
]
MetaReasoningLatitude = Literal[
    "classify_drift_hypotheses",
    "compare_expected_and_observed_checkpoint_shape",
    "propose_narrow_repairs",
    "summarize_uncompiled_discrepancy",
]
MetaRefusalEscalationCondition = Literal[
    "attempted_checkpoint_truth_substitution_by_prose",
    "authoritative_input_ref_unresolved",
    "hard_checkpoint_claim_without_bound_executor",
    "out_of_scope_runnable_loop_request",
]
MetaRequiredEvidenceOutput = Literal[
    "metric_key_continuity_assertion@1",
    "quality_dashboard_json",
    "runtime_observability_comparison@1",
    "stop_gate_metrics@1",
    "stop_gate_report_markdown",
    "v37a_meta_intent_module_catalog_evidence@1",
]
MetaAuthoritativeInputId = Literal[
    "v65_assessment_doc",
    "v65_closeout_decision_doc",
    "v65_lock_doc",
    "v65_metric_key_continuity_assertion",
    "v65_quality_dashboard_artifact",
    "v65_runtime_observability_comparison",
    "v65_stop_gate_metrics_artifact",
    "v65_stop_gate_report_artifact",
    "v65_v36e_evidence",
]
MetaOutOfScopeSurface = Literal[
    "meta_control_update_candidate@1",
    "meta_control_update_manifest@1",
    "meta_loop_checkpoint_result_manifest@1",
    "meta_loop_conformance_report@1",
    "meta_loop_drift_diagnostics@1",
    "meta_loop_run_trace@1",
    "meta_loop_sequence_contract@1",
]
MetaSequencePhaseBoundary = Literal[
    "intent_interpretation",
    "pre_generation_validation",
    "artifact_generation",
    "post_generation_validation",
    "evidence_gate",
    "operator_gate",
]
MetaBranchConditionKind = Literal[
    "all_required_inputs_available",
    "all_required_generated_artifacts_available",
    "downstream_gate_required",
]
MetaFailureTrigger = Literal[
    "checkpoint_failure",
    "evidence_gate_failure",
    "operator_rejection",
]
MetaRetryTrigger = Literal[
    "fixture_refresh_required",
    "generated_artifact_refresh_required",
]
MetaCheckpointAttemptStatus = Literal["attempted_fail", "attempted_pass"]
MetaBranchOutcome = Literal["entered", "not_entered"]
MetaRetryOutcome = Literal["retried_and_failed", "retried_and_succeeded"]
MetaTraceMode = Literal["executed_reference_run", "reference_not_executed"]
MetaTraceStepStatus = Literal[
    "executed_fail",
    "executed_pass",
    "executed_retry",
    "executed_skip",
    "reference_not_executed",
]

META_TESTING_INTENT_PACKET_SCHEMA = "meta_testing_intent_packet@1"
META_MODULE_CATALOG_SCHEMA = "meta_module_catalog@1"
META_LOOP_SEQUENCE_CONTRACT_SCHEMA = "meta_loop_sequence_contract@1"
META_LOOP_CHECKPOINT_RESULT_MANIFEST_SCHEMA = "meta_loop_checkpoint_result_manifest@1"
META_LOOP_RUN_TRACE_SCHEMA = "meta_loop_run_trace@1"
V37A_REFERENCE_LOOP_FAMILY = "arc_bundle_recursive_compilation_loop"
V37A_REFERENCE_ANCHOR_SHAPE = "arc_closeout_bundle_instance"
V37A_REFERENCE_ARC = 65
V37A_REFERENCE_PHASE = "closeout"
V37A_OPERATOR_SURFACE = "explicit_repo_acceptance_boundary"
V37A_REFERENCE_INSTANCE_ID = "arc_closeout_v65_reference"
V37A_INTENT_PACKET_ID = "v37a_arc_closeout_v65_intent"
V37C_EXECUTED_TRACE_MODE = "executed_reference_run"
V37B_REFERENCE_TRACE_MODE = "reference_not_executed"
V37C_AUTHORITATIVE_STOP_GATE_BINDING_REF = "apps/api/scripts/build_stop_gate_metrics.py::main"

FROZEN_V37A_MODULE_CLASSES: tuple[MetaModuleClass, ...] = (
    "reasoning_module",
    "checkpoint_module",
    "evidence_gate_module",
    "operator_gate_module",
)
FROZEN_V37A_REQUIRED_CHECKPOINT_CAPABILITIES: tuple[MetaCheckpointCapability, ...] = (
    "bundle_lint",
    "artifact_consistency_lint",
    "semantic_closeout_lint",
    "stop_gate_metrics_build",
    "quality_dashboard_build",
    "committed_event_stream_validation",
    "instruction_policy_validation",
)
FROZEN_V37A_REQUIRED_EVIDENCE_OUTPUTS: tuple[MetaRequiredEvidenceOutput, ...] = (
    "metric_key_continuity_assertion@1",
    "quality_dashboard_json",
    "runtime_observability_comparison@1",
    "stop_gate_metrics@1",
    "stop_gate_report_markdown",
    "v37a_meta_intent_module_catalog_evidence@1",
)
FROZEN_V37A_REASONING_LATITUDE: tuple[MetaReasoningLatitude, ...] = (
    "classify_drift_hypotheses",
    "compare_expected_and_observed_checkpoint_shape",
    "propose_narrow_repairs",
    "summarize_uncompiled_discrepancy",
)
FROZEN_V37A_REFUSAL_ESCALATION_CONDITIONS: tuple[MetaRefusalEscalationCondition, ...] = (
    "attempted_checkpoint_truth_substitution_by_prose",
    "authoritative_input_ref_unresolved",
    "hard_checkpoint_claim_without_bound_executor",
    "out_of_scope_runnable_loop_request",
)
FROZEN_V37A_ADEU_PRIORITY_ORDER: tuple[MetaADEUDimension, ...] = (
    "ontology",
    "epistemics",
    "deontics",
    "utility",
)
FROZEN_V37A_DRIFT_TAXONOMY: tuple[MetaDriftClass, ...] = (
    "ontology_drift",
    "epistemic_drift",
    "deontic_drift",
    "utility_drift",
)
FROZEN_V37A_AUTHORITATIVE_INPUT_IDS: tuple[MetaAuthoritativeInputId, ...] = (
    "v65_assessment_doc",
    "v65_closeout_decision_doc",
    "v65_lock_doc",
    "v65_metric_key_continuity_assertion",
    "v65_quality_dashboard_artifact",
    "v65_runtime_observability_comparison",
    "v65_stop_gate_metrics_artifact",
    "v65_stop_gate_report_artifact",
    "v65_v36e_evidence",
)
FROZEN_V37A_OUT_OF_SCOPE_SURFACES: tuple[MetaOutOfScopeSurface, ...] = (
    "meta_control_update_candidate@1",
    "meta_control_update_manifest@1",
    "meta_loop_conformance_report@1",
    "meta_loop_drift_diagnostics@1",
    "meta_loop_checkpoint_result_manifest@1",
    "meta_loop_run_trace@1",
    "meta_loop_sequence_contract@1",
)
FROZEN_V37B_PHASE_BOUNDARIES: tuple[MetaSequencePhaseBoundary, ...] = (
    "intent_interpretation",
    "pre_generation_validation",
    "artifact_generation",
    "post_generation_validation",
    "evidence_gate",
    "operator_gate",
)
FROZEN_V37C_EXECUTED_CHECKPOINT_CAPABILITIES: tuple[MetaCheckpointCapability, ...] = (
    "bundle_lint",
    "quality_dashboard_build",
    "stop_gate_metrics_build",
    "instruction_policy_validation",
    "committed_event_stream_validation",
)
FROZEN_V37C_NON_EXECUTED_RELEASED_CAPABILITIES: tuple[MetaCheckpointCapability, ...] = (
    "artifact_consistency_lint",
    "semantic_closeout_lint",
)


def _module_catalog_binding_ref(module_id: str, suffix: str) -> str:
    return f"meta_module_catalog::{module_id}::{suffix}"


def _assert_sorted_unique(values: list[str], *, field_name: str, allow_empty: bool = False) -> None:
    if not allow_empty and not values:
        raise ValueError(f"{field_name} must not be empty")
    if any(not value for value in values):
        raise ValueError(f"{field_name} must not contain empty values")
    if values != sorted(values):
        raise ValueError(f"{field_name} must be lexicographically sorted")
    if len(values) != len(set(values)):
        raise ValueError(f"{field_name} must not contain duplicates")


def _assert_exact_sequence(
    values: list[str], *, expected: tuple[str, ...], field_name: str
) -> None:
    if values != list(expected):
        raise ValueError(f"{field_name} must equal the frozen sequence {list(expected)!r}")


def _strip_anchor(ref: str) -> str:
    return ref.split("#", 1)[0]


def _split_ref_and_anchor(ref: str) -> tuple[str, str | None]:
    path, anchor = (ref.split("#", 1) + [None])[:2]
    if anchor == "":
        anchor = None
    return path, anchor


def _assert_repo_relative_ref(ref: str, *, field_name: str) -> None:
    if not ref:
        raise ValueError(f"{field_name} must not be empty")
    if ref.startswith("/"):
        raise ValueError(f"{field_name} must be repo-relative")
    path = _strip_anchor(ref)
    parts = path.split("/")
    if any(part in {"", ".", ".."} for part in parts):
        raise ValueError(f"{field_name} contains invalid path components")


def _resolve_repo_relative_path(ref: str, *, field_name: str) -> Path:
    _assert_repo_relative_ref(ref, field_name=field_name)
    root = repo_root(anchor=Path(__file__))
    path = root / _strip_anchor(ref)
    if not path.is_file():
        raise ValueError(f"{field_name} must resolve to an existing repo file")
    return path


def _sha256_repo_file(ref: str, *, field_name: str) -> str:
    path = _resolve_repo_relative_path(ref, field_name=field_name)
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _assert_python_symbol_exists(*, repo_path: str, symbol: str, field_name: str) -> None:
    path = _resolve_repo_relative_path(repo_path, field_name=field_name)
    tree = ast.parse(path.read_text(encoding="utf-8"))
    for node in tree.body:
        if (
            isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
            and node.name == symbol
        ):
            return
    raise ValueError(f"{field_name} must resolve to an existing python symbol")


def _assert_output_contract_in_scope(values: list[str], *, field_name: str) -> None:
    for value in values:
        if value in FROZEN_V37A_OUT_OF_SCOPE_SURFACES:
            raise ValueError(f"{field_name} must not introduce out-of-scope v37b/v37c surfaces")


class MetaReferenceLoopAnchor(BaseModel):
    model_config = ConfigDict(extra="forbid")

    shape: MetaReferenceAnchorShape = V37A_REFERENCE_ANCHOR_SHAPE
    reference_arc: int = Field(ge=1)
    reference_phase: MetaReferencePhase = V37A_REFERENCE_PHASE


class MetaAuthoritativeInputRef(BaseModel):
    model_config = ConfigDict(extra="forbid")

    input_id: MetaAuthoritativeInputId
    artifact_ref: str = Field(min_length=1)
    artifact_sha256: str = Field(pattern=r"^[0-9a-f]{64}$")

    @model_validator(mode="after")
    def _validate_contract(self) -> "MetaAuthoritativeInputRef":
        actual_hash = _sha256_repo_file(
            self.artifact_ref,
            field_name=f"authoritative_inputs[{self.input_id}].artifact_ref",
        )
        if self.artifact_sha256 != actual_hash:
            raise ValueError(
                f"authoritative_inputs[{self.input_id}].artifact_sha256 must match repo file bytes"
            )
        return self


class MetaExecutorParameterSlot(BaseModel):
    model_config = ConfigDict(extra="forbid")

    slot_name: str = Field(min_length=1)
    slot_type: MetaParameterSlotType
    value_origin: MetaParameterValueOrigin
    literal_value: str | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "MetaExecutorParameterSlot":
        if self.value_origin == "hardcoded_literal" and not self.literal_value:
            raise ValueError(f"parameter slot {self.slot_name} must bind a literal_value")
        if self.slot_type in {"path_literal", "repo_root_literal"} and self.literal_value:
            _assert_repo_relative_ref(
                self.literal_value,
                field_name=f"parameter_slots[{self.slot_name}].literal_value",
            )
        if self.value_origin == "soft_originated_input" and self.literal_value is not None:
            raise ValueError(
                "parameter slot "
                f"{self.slot_name} must not pin literal_value for soft-originated input"
            )
        return self


class MetaExecutorParameterPolicy(BaseModel):
    model_config = ConfigDict(extra="forbid")

    requires_typed_slots: Literal[True] = True
    soft_originated_inputs_allowed: bool = False
    unchecked_shell_interpolation_forbidden: Literal[True] = True
    validation_rules: list[MetaParameterValidationRule]
    parameter_slots: list[MetaExecutorParameterSlot]

    @model_validator(mode="after")
    def _validate_contract(self) -> "MetaExecutorParameterPolicy":
        _assert_sorted_unique(
            self.validation_rules,
            field_name="executor_parameter_policy.validation_rules",
        )
        if "typed_slots_only" not in self.validation_rules:
            raise ValueError(
                "executor_parameter_policy.validation_rules must include typed_slots_only"
            )
        if "no_unchecked_shell_interpolation" not in self.validation_rules:
            raise ValueError(
                "executor_parameter_policy.validation_rules must include "
                "no_unchecked_shell_interpolation"
            )
        slot_names = [slot.slot_name for slot in self.parameter_slots]
        _assert_sorted_unique(
            slot_names,
            field_name="executor_parameter_policy.parameter_slots.slot_name",
            allow_empty=True,
        )
        if not self.soft_originated_inputs_allowed and any(
            slot.value_origin == "soft_originated_input" for slot in self.parameter_slots
        ):
            raise ValueError(
                "executor_parameter_policy must reject soft-originated inputs "
                "when they are not allowed"
            )
        return self


class MetaExecutorBinding(BaseModel):
    model_config = ConfigDict(extra="forbid")

    binding_id: str = Field(min_length=1)
    binding_kind: MetaExecutorBindingKind
    binding_ref: str = Field(min_length=1)
    parameter_policy: MetaExecutorParameterPolicy

    @model_validator(mode="after")
    def _validate_contract(self) -> "MetaExecutorBinding":
        if self.binding_kind == "python_function_entrypoint":
            if "::" not in self.binding_ref:
                raise ValueError(
                    "python_function_entrypoint binding_ref must use repo_path::symbol"
                )
            repo_path, symbol = self.binding_ref.split("::", 1)
            if not symbol:
                raise ValueError("python_function_entrypoint binding_ref must include a symbol")
            _assert_python_symbol_exists(
                repo_path=repo_path,
                symbol=symbol,
                field_name=f"executor_bindings[{self.binding_id}].binding_ref",
            )
        else:
            if self.binding_ref != V37A_OPERATOR_SURFACE:
                raise ValueError(
                    f"operator_surface binding_ref must equal {V37A_OPERATOR_SURFACE!r}"
                )
        return self


class MetaReasoningDispatchProvenance(BaseModel):
    model_config = ConfigDict(extra="forbid")

    dispatch_convention_id: str = Field(min_length=1)
    prompt_surface_ref: str = Field(min_length=1)
    template_version_ref: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "MetaReasoningDispatchProvenance":
        _resolve_repo_relative_path(
            self.prompt_surface_ref,
            field_name="dispatch_provenance.prompt_surface_ref",
        )
        _resolve_repo_relative_path(
            self.template_version_ref,
            field_name="dispatch_provenance.template_version_ref",
        )
        return self


class MetaModuleDescriptor(BaseModel):
    model_config = ConfigDict(extra="forbid")

    module_id: str = Field(min_length=1)
    module_class: MetaModuleClass
    authority_status: MetaAuthorityStatus
    capability_id: str = Field(min_length=1)
    capability_granularity: MetaCapabilityGranularity
    input_contract: list[str]
    output_contract: list[str]
    consumed_authoritative_input_ids: list[MetaAuthoritativeInputId]
    expected_evidence_refs: list[str] = Field(default_factory=list)
    executor_bindings: list[MetaExecutorBinding] = Field(default_factory=list)
    dispatch_provenance: MetaReasoningDispatchProvenance | None = None
    predecessor_module_ids: list[str] = Field(default_factory=list)
    successor_module_ids: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "MetaModuleDescriptor":
        _assert_sorted_unique(
            self.input_contract,
            field_name=f"modules[{self.module_id}].input_contract",
        )
        _assert_sorted_unique(
            self.output_contract,
            field_name=f"modules[{self.module_id}].output_contract",
        )
        _assert_output_contract_in_scope(
            self.input_contract,
            field_name=f"modules[{self.module_id}].input_contract",
        )
        _assert_output_contract_in_scope(
            self.output_contract,
            field_name=f"modules[{self.module_id}].output_contract",
        )
        _assert_sorted_unique(
            self.consumed_authoritative_input_ids,
            field_name=f"modules[{self.module_id}].consumed_authoritative_input_ids",
            allow_empty=True,
        )
        _assert_sorted_unique(
            self.predecessor_module_ids,
            field_name=f"modules[{self.module_id}].predecessor_module_ids",
            allow_empty=True,
        )
        _assert_sorted_unique(
            self.successor_module_ids,
            field_name=f"modules[{self.module_id}].successor_module_ids",
            allow_empty=True,
        )
        for ref in self.expected_evidence_refs:
            _resolve_repo_relative_path(
                ref,
                field_name=f"modules[{self.module_id}].expected_evidence_refs",
            )
        _assert_sorted_unique(
            self.expected_evidence_refs,
            field_name=f"modules[{self.module_id}].expected_evidence_refs",
            allow_empty=True,
        )

        binding_ids = [binding.binding_id for binding in self.executor_bindings]
        _assert_sorted_unique(
            binding_ids,
            field_name=f"modules[{self.module_id}].executor_bindings.binding_id",
            allow_empty=True,
        )

        if self.module_class == "reasoning_module":
            if self.authority_status != "soft_influence_only":
                raise ValueError(
                    f"reasoning module {self.module_id} must remain soft_influence_only"
                )
            if self.capability_granularity != "soft_dispatch":
                raise ValueError(
                    f"reasoning module {self.module_id} must use soft_dispatch granularity"
                )
            if self.dispatch_provenance is None:
                raise ValueError(
                    f"reasoning module {self.module_id} must declare dispatch_provenance"
                )
            if self.executor_bindings:
                raise ValueError(
                    f"reasoning module {self.module_id} must not declare hard executor bindings"
                )
            if self.capability_id in FROZEN_V37A_REQUIRED_CHECKPOINT_CAPABILITIES:
                raise ValueError(
                    f"reasoning module {self.module_id} must not claim "
                    f"checkpoint capability {self.capability_id}"
                )
        else:
            if self.dispatch_provenance is not None:
                raise ValueError(
                    f"hard module {self.module_id} must not declare reasoning dispatch provenance"
                )
            if not self.executor_bindings:
                raise ValueError(f"hard module {self.module_id} must declare executor_bindings")
            if self.capability_granularity == "soft_dispatch":
                raise ValueError(
                    f"hard module {self.module_id} must not use soft_dispatch granularity"
                )
            if (
                self.capability_granularity == "single_executor"
                and len(self.executor_bindings) != 1
            ):
                raise ValueError(
                    f"hard module {self.module_id} must bind exactly one "
                    "executor for single_executor granularity"
                )
            if self.capability_granularity == "executor_family" and len(self.executor_bindings) < 2:
                raise ValueError(
                    f"hard module {self.module_id} must bind multiple "
                    "executors for executor_family granularity"
                )
            if self.module_class == "checkpoint_module":
                if self.authority_status != "hard_checkpoint_truth":
                    raise ValueError(
                        f"checkpoint module {self.module_id} must remain hard_checkpoint_truth"
                    )
                if self.capability_id not in FROZEN_V37A_REQUIRED_CHECKPOINT_CAPABILITIES:
                    raise ValueError(
                        f"checkpoint module {self.module_id} must bind "
                        "a frozen checkpoint capability"
                    )
            elif self.module_class == "evidence_gate_module":
                if self.authority_status != "hard_evidence_gate":
                    raise ValueError(
                        f"evidence gate module {self.module_id} must remain hard_evidence_gate"
                    )
            else:
                if self.authority_status != "operator_acceptance_gate":
                    raise ValueError(
                        f"operator gate module {self.module_id} "
                        "must remain operator_acceptance_gate"
                    )
        return self


class MetaTestingIntentPacket(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: MetaTestingIntentPacketSchemaVersion = META_TESTING_INTENT_PACKET_SCHEMA
    reference_loop_family: MetaReferenceLoopFamily = V37A_REFERENCE_LOOP_FAMILY
    reference_instance_id: str = Field(min_length=1)
    intent_packet_id: str = Field(min_length=1)
    reference_anchor: MetaReferenceLoopAnchor
    objective: str = Field(min_length=1)
    success_condition: str = Field(min_length=1)
    failure_condition: str = Field(min_length=1)
    authoritative_inputs: list[MetaAuthoritativeInputRef]
    required_hard_checkpoints: list[MetaCheckpointCapability]
    required_evidence_outputs: list[MetaRequiredEvidenceOutput]
    allowed_reasoning_latitude: list[MetaReasoningLatitude]
    refusal_escalation_conditions: list[MetaRefusalEscalationCondition]
    adeu_priority_order: list[MetaADEUDimension]
    operational_influence_distinct_from_accepted_compilation: Literal[True] = True
    hard_checkpoint_truth_boundary_preserved: Literal[True] = True

    @model_validator(mode="after")
    def _validate_contract(self) -> "MetaTestingIntentPacket":
        input_ids = [entry.input_id for entry in self.authoritative_inputs]
        _assert_exact_sequence(
            input_ids,
            expected=FROZEN_V37A_AUTHORITATIVE_INPUT_IDS,
            field_name="authoritative_inputs.input_id",
        )
        _assert_exact_sequence(
            self.required_hard_checkpoints,
            expected=FROZEN_V37A_REQUIRED_CHECKPOINT_CAPABILITIES,
            field_name="required_hard_checkpoints",
        )
        _assert_exact_sequence(
            self.required_evidence_outputs,
            expected=FROZEN_V37A_REQUIRED_EVIDENCE_OUTPUTS,
            field_name="required_evidence_outputs",
        )
        _assert_exact_sequence(
            self.allowed_reasoning_latitude,
            expected=FROZEN_V37A_REASONING_LATITUDE,
            field_name="allowed_reasoning_latitude",
        )
        _assert_exact_sequence(
            self.refusal_escalation_conditions,
            expected=FROZEN_V37A_REFUSAL_ESCALATION_CONDITIONS,
            field_name="refusal_escalation_conditions",
        )
        _assert_exact_sequence(
            self.adeu_priority_order,
            expected=FROZEN_V37A_ADEU_PRIORITY_ORDER,
            field_name="adeu_priority_order",
        )
        if self.reference_anchor.reference_arc != V37A_REFERENCE_ARC:
            raise ValueError(
                "reference_anchor.reference_arc must equal the frozen "
                f"v37a anchor {V37A_REFERENCE_ARC}"
            )
        return self


class MetaModuleCatalog(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: MetaModuleCatalogSchemaVersion = META_MODULE_CATALOG_SCHEMA
    reference_loop_family: MetaReferenceLoopFamily = V37A_REFERENCE_LOOP_FAMILY
    reference_instance_id: str = Field(min_length=1)
    intent_packet_id: str = Field(min_length=1)
    reference_anchor: MetaReferenceLoopAnchor
    modules: list[MetaModuleDescriptor]
    drift_taxonomy: list[MetaDriftClass]
    hard_checkpoint_truth_boundary_preserved: Literal[True] = True
    no_hidden_prompt_only_module_authority: Literal[True] = True
    capability_to_executor_granularity_explicit: Literal[True] = True

    @model_validator(mode="after")
    def _validate_contract(self) -> "MetaModuleCatalog":
        module_ids = [module.module_id for module in self.modules]
        _assert_sorted_unique(module_ids, field_name="modules.module_id")
        _assert_exact_sequence(
            self.drift_taxonomy,
            expected=FROZEN_V37A_DRIFT_TAXONOMY,
            field_name="drift_taxonomy",
        )
        if self.reference_anchor.reference_arc != V37A_REFERENCE_ARC:
            raise ValueError(
                "reference_anchor.reference_arc must equal the frozen "
                f"v37a anchor {V37A_REFERENCE_ARC}"
            )
        present_classes = {module.module_class for module in self.modules}
        if present_classes != set(FROZEN_V37A_MODULE_CLASSES):
            raise ValueError(
                f"modules must cover the frozen module classes {list(FROZEN_V37A_MODULE_CLASSES)!r}"
            )

        checkpoint_capabilities = [
            module.capability_id
            for module in self.modules
            if module.module_class == "checkpoint_module"
        ]
        _assert_exact_sequence(
            checkpoint_capabilities,
            expected=FROZEN_V37A_REQUIRED_CHECKPOINT_CAPABILITIES,
            field_name="modules.checkpoint_module.capability_id",
        )
        module_id_set = set(module_ids)
        for module in self.modules:
            for predecessor in module.predecessor_module_ids:
                if predecessor not in module_id_set:
                    raise ValueError(
                        f"module {module.module_id} predecessor {predecessor!r} is not declared"
                    )
            for successor in module.successor_module_ids:
                if successor not in module_id_set:
                    raise ValueError(
                        f"module {module.module_id} successor {successor!r} is not declared"
                    )
        return self


class MetaLoopBranchCondition(BaseModel):
    model_config = ConfigDict(extra="forbid")

    branch_condition_id: str = Field(min_length=1)
    condition_kind: MetaBranchConditionKind
    description: str = Field(min_length=1)


class MetaLoopFailureEdge(BaseModel):
    model_config = ConfigDict(extra="forbid")

    failure_edge_id: str = Field(min_length=1)
    from_step_id: str = Field(min_length=1)
    to_step_id: str = Field(min_length=1)
    trigger: MetaFailureTrigger
    description: str = Field(min_length=1)


class MetaLoopRetryEdge(BaseModel):
    model_config = ConfigDict(extra="forbid")

    retry_edge_id: str = Field(min_length=1)
    from_step_id: str = Field(min_length=1)
    to_step_id: str = Field(min_length=1)
    trigger: MetaRetryTrigger
    description: str = Field(min_length=1)


class MetaLoopOperatorGate(BaseModel):
    model_config = ConfigDict(extra="forbid")

    operator_gate_id: str = Field(min_length=1)
    module_id: str = Field(min_length=1)
    acceptance_scope: str = Field(min_length=1)


class MetaLoopSequenceStep(BaseModel):
    model_config = ConfigDict(extra="forbid")

    step_id: str = Field(min_length=1)
    module_id: str = Field(min_length=1)
    phase_boundary: MetaSequencePhaseBoundary
    required_inputs: list[str]
    expected_outputs: list[str]
    checkpoint_binding_id: str | None
    branch_condition_id: str | None
    failure_edge_ids: list[str]
    retry_edge_ids: list[str]
    operator_gate_id: str | None
    dispatch_provenance_ref: str | None
    downstream_gate_module_id: str | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "MetaLoopSequenceStep":
        _assert_sorted_unique(
            self.required_inputs,
            field_name=f"sequence_steps[{self.step_id}].required_inputs",
            allow_empty=True,
        )
        _assert_sorted_unique(
            self.expected_outputs,
            field_name=f"sequence_steps[{self.step_id}].expected_outputs",
            allow_empty=True,
        )
        _assert_sorted_unique(
            self.failure_edge_ids,
            field_name=f"sequence_steps[{self.step_id}].failure_edge_ids",
            allow_empty=True,
        )
        _assert_sorted_unique(
            self.retry_edge_ids,
            field_name=f"sequence_steps[{self.step_id}].retry_edge_ids",
            allow_empty=True,
        )
        return self


class MetaLoopSequenceContract(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: MetaLoopSequenceContractSchemaVersion = META_LOOP_SEQUENCE_CONTRACT_SCHEMA
    reference_loop_family: MetaReferenceLoopFamily = V37A_REFERENCE_LOOP_FAMILY
    reference_instance_id: str = Field(min_length=1)
    intent_packet_id: str = Field(min_length=1)
    reference_anchor: MetaReferenceLoopAnchor
    phase_boundaries_in_order: list[MetaSequencePhaseBoundary]
    branch_conditions: list[MetaLoopBranchCondition]
    failure_edges: list[MetaLoopFailureEdge]
    retry_edges: list[MetaLoopRetryEdge]
    operator_gates: list[MetaLoopOperatorGate]
    steps: list[MetaLoopSequenceStep]
    operational_influence_threshold_explicit: Literal[True] = True
    accepted_compilation_threshold_explicit: Literal[True] = True
    no_hidden_prompt_only_step_order: Literal[True] = True
    no_hidden_branch_logic: Literal[True] = True
    no_model_prose_truth_substitution: Literal[True] = True

    @model_validator(mode="after")
    def _validate_contract(self) -> "MetaLoopSequenceContract":
        _assert_exact_sequence(
            self.phase_boundaries_in_order,
            expected=FROZEN_V37B_PHASE_BOUNDARIES,
            field_name="phase_boundaries_in_order",
        )
        if self.reference_anchor.reference_arc != V37A_REFERENCE_ARC:
            raise ValueError(
                "reference_anchor.reference_arc must equal the frozen "
                f"v37b anchor {V37A_REFERENCE_ARC}"
            )

        branch_condition_ids = [item.branch_condition_id for item in self.branch_conditions]
        _assert_sorted_unique(
            branch_condition_ids,
            field_name="branch_conditions.branch_condition_id",
            allow_empty=True,
        )
        failure_edge_ids = [item.failure_edge_id for item in self.failure_edges]
        _assert_sorted_unique(
            failure_edge_ids,
            field_name="failure_edges.failure_edge_id",
            allow_empty=True,
        )
        retry_edge_ids = [item.retry_edge_id for item in self.retry_edges]
        _assert_sorted_unique(
            retry_edge_ids,
            field_name="retry_edges.retry_edge_id",
            allow_empty=True,
        )
        operator_gate_ids = [item.operator_gate_id for item in self.operator_gates]
        _assert_sorted_unique(
            operator_gate_ids,
            field_name="operator_gates.operator_gate_id",
            allow_empty=True,
        )
        step_ids = [item.step_id for item in self.steps]
        _assert_sorted_unique(step_ids, field_name="steps.step_id")

        step_id_set = set(step_ids)
        branch_condition_id_set = set(branch_condition_ids)
        failure_edge_id_set = set(failure_edge_ids)
        retry_edge_id_set = set(retry_edge_ids)
        operator_gate_id_set = set(operator_gate_ids)

        for edge in self.failure_edges:
            if edge.from_step_id not in step_id_set or edge.to_step_id not in step_id_set:
                raise ValueError("failure_edges must resolve existing step ids")
        for edge in self.retry_edges:
            if edge.from_step_id not in step_id_set or edge.to_step_id not in step_id_set:
                raise ValueError("retry_edges must resolve existing step ids")
        step_module_id_set = {step.module_id for step in self.steps}

        for gate in self.operator_gates:
            if gate.module_id not in step_module_id_set:
                raise ValueError("operator_gates.module_id must resolve an existing step module")

        seen_phase_indices: list[int] = []
        boundary_index = {
            value: index for index, value in enumerate(self.phase_boundaries_in_order)
        }
        for step in self.steps:
            seen_phase_indices.append(boundary_index[step.phase_boundary])
            if (
                step.branch_condition_id is not None
                and step.branch_condition_id not in branch_condition_id_set
            ):
                raise ValueError(
                    "step "
                    f"{step.step_id} branch_condition_id must resolve "
                    "a declared branch condition"
                )
            for edge_id in step.failure_edge_ids:
                if edge_id not in failure_edge_id_set:
                    raise ValueError(
                        f"step {step.step_id} failure_edge_ids must resolve declared failure edges"
                    )
            for edge_id in step.retry_edge_ids:
                if edge_id not in retry_edge_id_set:
                    raise ValueError(
                        f"step {step.step_id} retry_edge_ids must resolve declared retry edges"
                    )
            if (
                step.operator_gate_id is not None
                and step.operator_gate_id not in operator_gate_id_set
            ):
                raise ValueError(
                    f"step {step.step_id} operator_gate_id must resolve a declared operator gate"
                )
        if seen_phase_indices != sorted(seen_phase_indices):
            raise ValueError("steps must preserve the frozen phase-boundary order")
        return self


class MetaCheckpointOutputArtifact(BaseModel):
    model_config = ConfigDict(extra="forbid")

    artifact_role: str = Field(min_length=1)
    artifact_ref: str = Field(min_length=1)
    artifact_sha256: str = Field(pattern=r"^[0-9a-f]{64}$")

    @model_validator(mode="after")
    def _validate_contract(self) -> "MetaCheckpointOutputArtifact":
        actual_hash = _sha256_repo_file(
            self.artifact_ref,
            field_name=f"output_artifacts[{self.artifact_role}].artifact_ref",
        )
        if self.artifact_sha256 != actual_hash:
            raise ValueError(
                f"output_artifacts[{self.artifact_role}].artifact_sha256 must match repo file bytes"
            )
        return self


class MetaLoopCheckpointResultRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    result_row_id: str = Field(min_length=1)
    planned_step_id: str = Field(min_length=1)
    module_id: str = Field(min_length=1)
    module_class: MetaModuleClass
    capability_id: str = Field(min_length=1)
    executor_binding_id: str = Field(min_length=1)
    executor_binding_ref: str = Field(min_length=1)
    attempt_index: int = Field(ge=1)
    attempt_status: MetaCheckpointAttemptStatus
    output_artifacts: list[MetaCheckpointOutputArtifact] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "MetaLoopCheckpointResultRow":
        if self.module_class == "reasoning_module":
            raise ValueError("checkpoint result rows must not bind reasoning modules")
        output_artifact_refs = [artifact.artifact_ref for artifact in self.output_artifacts]
        _assert_sorted_unique(
            output_artifact_refs,
            field_name=f"checkpoint_results[{self.result_row_id}].output_artifacts.artifact_ref",
            allow_empty=True,
        )
        if self.executor_binding_ref == V37A_OPERATOR_SURFACE:
            return self
        if "::" not in self.executor_binding_ref:
            raise ValueError("executor_binding_ref must use repo_path::symbol or operator surface")
        repo_path, symbol = self.executor_binding_ref.split("::", 1)
        if not symbol:
            raise ValueError("executor_binding_ref must include a python symbol")
        _assert_python_symbol_exists(
            repo_path=repo_path,
            symbol=symbol,
            field_name=f"checkpoint_results[{self.result_row_id}].executor_binding_ref",
        )
        return self


class MetaLoopBranchOutcomeRecord(BaseModel):
    model_config = ConfigDict(extra="forbid")

    branch_outcome_id: str = Field(min_length=1)
    planned_step_id: str = Field(min_length=1)
    branch_condition_id: str = Field(min_length=1)
    outcome: MetaBranchOutcome


class MetaLoopRetryOutcomeRecord(BaseModel):
    model_config = ConfigDict(extra="forbid")

    retry_outcome_id: str = Field(min_length=1)
    planned_step_id: str = Field(min_length=1)
    retry_edge_id: str = Field(min_length=1)
    outcome: MetaRetryOutcome
    triggering_result_row_id: str = Field(min_length=1)
    terminal_result_row_id: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "MetaLoopRetryOutcomeRecord":
        if self.triggering_result_row_id == self.terminal_result_row_id:
            raise ValueError(
                "retry_outcomes"
                f"[{self.retry_outcome_id}] must bind distinct triggering and terminal rows"
            )
        return self


class MetaLoopCheckpointResultManifest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: MetaLoopCheckpointResultManifestSchemaVersion = (
        META_LOOP_CHECKPOINT_RESULT_MANIFEST_SCHEMA
    )
    reference_loop_family: MetaReferenceLoopFamily = V37A_REFERENCE_LOOP_FAMILY
    reference_instance_id: str = Field(min_length=1)
    intent_packet_id: str = Field(min_length=1)
    reference_anchor: MetaReferenceLoopAnchor
    executed_checkpoint_capabilities: list[MetaCheckpointCapability]
    non_executed_released_capabilities: list[MetaCheckpointCapability]
    checkpoint_results: list[MetaLoopCheckpointResultRow]
    branch_outcomes: list[MetaLoopBranchOutcomeRecord] = Field(default_factory=list)
    retry_outcomes: list[MetaLoopRetryOutcomeRecord] = Field(default_factory=list)
    executed_capability_subset_is_intentional: Literal[True] = True
    hard_checkpoint_results_captured_from_actual_executors: Literal[True] = True
    failed_checkpoint_rows_preserved: Literal[True] = True
    reasoning_vs_checkpoint_truth_boundary_preserved: Literal[True] = True

    @model_validator(mode="after")
    def _validate_contract(self) -> "MetaLoopCheckpointResultManifest":
        if self.reference_anchor.reference_arc != V37A_REFERENCE_ARC:
            raise ValueError(
                "reference_anchor.reference_arc must equal the frozen "
                f"v37c anchor {V37A_REFERENCE_ARC}"
            )
        _assert_exact_sequence(
            self.executed_checkpoint_capabilities,
            expected=FROZEN_V37C_EXECUTED_CHECKPOINT_CAPABILITIES,
            field_name="executed_checkpoint_capabilities",
        )
        _assert_exact_sequence(
            self.non_executed_released_capabilities,
            expected=FROZEN_V37C_NON_EXECUTED_RELEASED_CAPABILITIES,
            field_name="non_executed_released_capabilities",
        )
        result_row_ids = [row.result_row_id for row in self.checkpoint_results]
        _assert_sorted_unique(result_row_ids, field_name="checkpoint_results.result_row_id")
        branch_outcome_ids = [row.branch_outcome_id for row in self.branch_outcomes]
        _assert_sorted_unique(
            branch_outcome_ids,
            field_name="branch_outcomes.branch_outcome_id",
            allow_empty=True,
        )
        retry_outcome_ids = [row.retry_outcome_id for row in self.retry_outcomes]
        _assert_sorted_unique(
            retry_outcome_ids,
            field_name="retry_outcomes.retry_outcome_id",
            allow_empty=True,
        )
        return self


class MetaLoopRunTraceStep(BaseModel):
    model_config = ConfigDict(extra="forbid")

    planned_step_id: str = Field(min_length=1)
    actual_module_id: str = Field(min_length=1)
    consumed_inputs: list[str]
    emitted_outputs: list[str]
    observed_checkpoint_result_refs: list[str]
    actual_branch_outcome_ref: str | None = None
    actual_retry_outcome_refs: list[str] | None = None
    step_status: MetaTraceStepStatus
    operational_influence_occurred: bool
    accepted_compilation_occurred: bool

    @model_validator(mode="after")
    def _validate_contract(self) -> "MetaLoopRunTraceStep":
        _assert_sorted_unique(
            self.consumed_inputs,
            field_name=f"run_trace_steps[{self.planned_step_id}].consumed_inputs",
            allow_empty=True,
        )
        _assert_sorted_unique(
            self.emitted_outputs,
            field_name=f"run_trace_steps[{self.planned_step_id}].emitted_outputs",
            allow_empty=True,
        )
        _assert_sorted_unique(
            self.observed_checkpoint_result_refs,
            field_name=(f"run_trace_steps[{self.planned_step_id}].observed_checkpoint_result_refs"),
            allow_empty=True,
        )
        for ref in self.observed_checkpoint_result_refs:
            _resolve_repo_relative_path(
                ref,
                field_name=(
                    f"run_trace_steps[{self.planned_step_id}].observed_checkpoint_result_refs"
                ),
            )
        if self.actual_branch_outcome_ref is not None:
            _resolve_repo_relative_path(
                self.actual_branch_outcome_ref,
                field_name=f"run_trace_steps[{self.planned_step_id}].actual_branch_outcome_ref",
            )
        if self.actual_retry_outcome_refs is not None:
            _assert_sorted_unique(
                self.actual_retry_outcome_refs,
                field_name=f"run_trace_steps[{self.planned_step_id}].actual_retry_outcome_refs",
            )
            for ref in self.actual_retry_outcome_refs:
                _resolve_repo_relative_path(
                    ref,
                    field_name=(
                        f"run_trace_steps[{self.planned_step_id}].actual_retry_outcome_refs"
                    ),
                )
        return self


class MetaLoopRunTrace(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: MetaLoopRunTraceSchemaVersion = META_LOOP_RUN_TRACE_SCHEMA
    reference_loop_family: MetaReferenceLoopFamily = V37A_REFERENCE_LOOP_FAMILY
    reference_instance_id: str = Field(min_length=1)
    intent_packet_id: str = Field(min_length=1)
    reference_anchor: MetaReferenceLoopAnchor
    trace_mode: MetaTraceMode
    checkpoint_result_manifest_ref: str | None = None
    steps: list[MetaLoopRunTraceStep]
    operational_influence_threshold_explicit: Literal[True] = True
    accepted_compilation_threshold_explicit: Literal[True] = True
    no_model_prose_truth_substitution: Literal[True] = True

    @model_validator(mode="after")
    def _validate_contract(self) -> "MetaLoopRunTrace":
        if self.reference_anchor.reference_arc != V37A_REFERENCE_ARC:
            raise ValueError(
                "reference_anchor.reference_arc must equal the frozen "
                f"v37b anchor {V37A_REFERENCE_ARC}"
            )
        step_ids = [item.planned_step_id for item in self.steps]
        _assert_sorted_unique(step_ids, field_name="run_trace.steps.planned_step_id")
        if self.trace_mode == V37B_REFERENCE_TRACE_MODE:
            if self.checkpoint_result_manifest_ref is not None:
                raise ValueError(
                    "reference_not_executed traces must not bind checkpoint_result_manifest_ref"
                )
            for step in self.steps:
                if step.step_status != "reference_not_executed":
                    raise ValueError(
                        "reference_not_executed traces must keep "
                        "step_status = reference_not_executed"
                    )
                if step.accepted_compilation_occurred:
                    raise ValueError(
                        "reference_not_executed traces must keep "
                        "accepted_compilation_occurred = false"
                    )
                if step.actual_branch_outcome_ref is not None:
                    raise ValueError(
                        "reference_not_executed traces must not bind actual_branch_outcome_ref"
                    )
                if step.actual_retry_outcome_refs is not None:
                    raise ValueError(
                        "reference_not_executed traces must not bind actual_retry_outcome_refs"
                    )
        elif self.trace_mode == V37C_EXECUTED_TRACE_MODE:
            if self.checkpoint_result_manifest_ref is None:
                raise ValueError(
                    "executed_reference_run traces must bind checkpoint_result_manifest_ref"
                )
            _resolve_repo_relative_path(
                self.checkpoint_result_manifest_ref,
                field_name="checkpoint_result_manifest_ref",
            )
            for step in self.steps:
                if step.step_status == "reference_not_executed":
                    raise ValueError(
                        "executed_reference_run traces must not keep "
                        "step_status = reference_not_executed"
                    )
                if step.step_status == "executed_skip" and step.observed_checkpoint_result_refs:
                    raise ValueError(
                        "executed_skip steps must not bind observed_checkpoint_result_refs"
                    )
                if step.accepted_compilation_occurred and step.step_status != "executed_pass":
                    raise ValueError(
                        "accepted_compilation_occurred requires step_status = executed_pass"
                    )
        return self


def canonicalize_meta_testing_intent_packet_payload(payload: dict[str, Any]) -> dict[str, Any]:
    model = MetaTestingIntentPacket.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def canonicalize_meta_module_catalog_payload(payload: dict[str, Any]) -> dict[str, Any]:
    model = MetaModuleCatalog.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def canonicalize_meta_loop_sequence_contract_payload(payload: dict[str, Any]) -> dict[str, Any]:
    model = MetaLoopSequenceContract.model_validate(deepcopy(payload))
    return model.model_dump(mode="json")


def canonicalize_meta_loop_checkpoint_result_manifest_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    model = MetaLoopCheckpointResultManifest.model_validate(deepcopy(payload))
    return model.model_dump(mode="json")


def canonicalize_meta_loop_run_trace_payload(payload: dict[str, Any]) -> dict[str, Any]:
    model = MetaLoopRunTrace.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def _parse_manifest_anchor_ref(
    ref: str,
    *,
    manifest_ref: str,
    expected_section: str,
    field_name: str,
) -> str:
    path, anchor = _split_ref_and_anchor(ref)
    if path != manifest_ref:
        raise ValueError(f"{field_name} must stay bound to checkpoint_result_manifest_ref")
    if anchor is None:
        raise ValueError(f"{field_name} must include an anchor")
    if "/" not in anchor:
        raise ValueError(f"{field_name} anchor must use '<section>/<id>' form")
    section, item_id = anchor.split("/", 1)
    if section != expected_section or not item_id:
        raise ValueError(
            f"{field_name} must target '{expected_section}/<id>' within the checkpoint manifest"
        )
    return item_id


def assert_v37a_reference_instance_binding(
    *,
    intent_packet: MetaTestingIntentPacket,
    module_catalog: MetaModuleCatalog,
) -> None:
    for field_name in ("reference_loop_family", "reference_instance_id", "intent_packet_id"):
        if getattr(intent_packet, field_name) != getattr(module_catalog, field_name):
            raise ValueError(f"reference instance binding mismatch for {field_name}")
    if intent_packet.reference_anchor != module_catalog.reference_anchor:
        raise ValueError("reference instance binding mismatch for reference_anchor")


def assert_v37a_reference_bundle_consistent(
    *,
    intent_packet: MetaTestingIntentPacket,
    module_catalog: MetaModuleCatalog,
) -> None:
    assert_v37a_reference_instance_binding(
        intent_packet=intent_packet,
        module_catalog=module_catalog,
    )

    authoritative_input_ids = {entry.input_id for entry in intent_packet.authoritative_inputs}
    checkpoint_capability_to_module: dict[str, MetaModuleDescriptor] = {}
    has_evidence_gate = False
    has_operator_gate = False

    for module in module_catalog.modules:
        if not set(module.consumed_authoritative_input_ids).issubset(authoritative_input_ids):
            raise ValueError(
                f"module {module.module_id} consumes authoritative inputs "
                "not declared by intent packet"
            )
        if module.module_class == "checkpoint_module":
            if module.capability_id in checkpoint_capability_to_module:
                raise ValueError(
                    f"checkpoint capability {module.capability_id} must bind exactly one module"
                )
            checkpoint_capability_to_module[module.capability_id] = module
        elif module.module_class == "evidence_gate_module":
            has_evidence_gate = True
            if set(module.consumed_authoritative_input_ids) != authoritative_input_ids:
                raise ValueError(
                    "evidence gate module must resolve the full authoritative input set"
                )
        elif module.module_class == "operator_gate_module":
            has_operator_gate = True

    if set(checkpoint_capability_to_module) != set(intent_packet.required_hard_checkpoints):
        raise ValueError(
            "module catalog checkpoint capabilities must match "
            "intent packet required_hard_checkpoints"
        )
    if not has_evidence_gate:
        raise ValueError("module catalog must include one evidence gate module")
    if not has_operator_gate:
        raise ValueError("module catalog must include one operator gate module")


def assert_v37b_reference_instance_binding(
    *,
    intent_packet: MetaTestingIntentPacket,
    module_catalog: MetaModuleCatalog,
    sequence_contract: MetaLoopSequenceContract,
    run_trace: MetaLoopRunTrace,
) -> None:
    assert_v37a_reference_instance_binding(
        intent_packet=intent_packet,
        module_catalog=module_catalog,
    )
    for field_name in ("reference_loop_family", "reference_instance_id", "intent_packet_id"):
        expected = getattr(intent_packet, field_name)
        if getattr(sequence_contract, field_name) != expected:
            raise ValueError(f"reference instance binding mismatch for {field_name}")
        if getattr(run_trace, field_name) != expected:
            raise ValueError(f"reference instance binding mismatch for {field_name}")
    if sequence_contract.reference_anchor != intent_packet.reference_anchor:
        raise ValueError("reference instance binding mismatch for reference_anchor")
    if run_trace.reference_anchor != intent_packet.reference_anchor:
        raise ValueError("reference instance binding mismatch for reference_anchor")


def assert_v37b_reference_bundle_consistent(
    *,
    intent_packet: MetaTestingIntentPacket,
    module_catalog: MetaModuleCatalog,
    sequence_contract: MetaLoopSequenceContract,
    run_trace: MetaLoopRunTrace,
) -> None:
    assert_v37a_reference_bundle_consistent(
        intent_packet=intent_packet,
        module_catalog=module_catalog,
    )
    assert_v37b_reference_instance_binding(
        intent_packet=intent_packet,
        module_catalog=module_catalog,
        sequence_contract=sequence_contract,
        run_trace=run_trace,
    )

    module_by_id = {module.module_id: module for module in module_catalog.modules}
    branch_condition_ids = {
        item.branch_condition_id for item in sequence_contract.branch_conditions
    }
    failure_edge_by_id = {item.failure_edge_id: item for item in sequence_contract.failure_edges}
    retry_edge_by_id = {item.retry_edge_id: item for item in sequence_contract.retry_edges}
    operator_gate_by_id = {item.operator_gate_id: item for item in sequence_contract.operator_gates}
    trace_step_by_id = {item.planned_step_id: item for item in run_trace.steps}

    expected_step_ids_in_order = [step.step_id for step in sequence_contract.steps]
    if [step.planned_step_id for step in run_trace.steps] != expected_step_ids_in_order:
        raise ValueError(
            "run trace planned_step_id order must match the accepted sequence contract step order"
        )

    if run_trace.trace_mode != V37B_REFERENCE_TRACE_MODE:
        raise ValueError(
            f"accepted v37b run trace must use trace_mode {V37B_REFERENCE_TRACE_MODE!r}"
        )

    for step in sequence_contract.steps:
        if step.module_id not in module_by_id:
            raise ValueError(f"sequence step {step.step_id} must resolve an accepted module_id")
        trace_step = trace_step_by_id[step.step_id]
        if trace_step.actual_module_id != step.module_id:
            raise ValueError(
                f"run trace step {step.step_id} must resolve actual_module_id to the bound module"
            )

        module = module_by_id[step.module_id]
        if (
            step.branch_condition_id is not None
            and step.branch_condition_id not in branch_condition_ids
        ):
            raise ValueError(
                "sequence step "
                f"{step.step_id} branch_condition_id must resolve "
                "an accepted branch condition"
            )
        for edge_id in step.failure_edge_ids:
            if failure_edge_by_id[edge_id].from_step_id != step.step_id:
                raise ValueError(
                    f"failure edge {edge_id} must start at sequence step {step.step_id}"
                )
        for edge_id in step.retry_edge_ids:
            if retry_edge_by_id[edge_id].from_step_id != step.step_id:
                raise ValueError(f"retry edge {edge_id} must start at sequence step {step.step_id}")

        if module.module_class == "reasoning_module":
            if step.dispatch_provenance_ref != _module_catalog_binding_ref(
                module.module_id, "dispatch_provenance"
            ):
                raise ValueError(
                    f"reasoning step {step.step_id} must bind the released v37a dispatch provenance"
                )
            if step.checkpoint_binding_id is not None:
                raise ValueError(
                    f"reasoning step {step.step_id} must not declare checkpoint_binding_id"
                )
            if step.operator_gate_id is not None:
                raise ValueError(f"reasoning step {step.step_id} must not declare operator_gate_id")
            if step.downstream_gate_module_id is None:
                raise ValueError(
                    f"reasoning step {step.step_id} must bind a downstream gate module"
                )
            downstream = module_by_id.get(step.downstream_gate_module_id)
            if downstream is None or downstream.module_class == "reasoning_module":
                raise ValueError(
                    f"reasoning step {step.step_id} downstream gate must resolve a hard module"
                )
            if not trace_step.operational_influence_occurred:
                raise ValueError(
                    f"reasoning step {step.step_id} must mark operational_influence_occurred = true"
                )
        else:
            if step.dispatch_provenance_ref is not None:
                raise ValueError(
                    f"hard step {step.step_id} must not declare dispatch_provenance_ref"
                )
            if trace_step.operational_influence_occurred:
                raise ValueError(
                    f"hard step {step.step_id} must not claim operational_influence_occurred"
                )
            if step.downstream_gate_module_id is not None:
                raise ValueError(
                    f"hard step {step.step_id} must not bind downstream_gate_module_id"
                )

            if module.module_class == "operator_gate_module":
                if step.operator_gate_id is None:
                    raise ValueError(
                        f"operator gate step {step.step_id} must declare operator_gate_id"
                    )
                operator_gate = operator_gate_by_id.get(step.operator_gate_id)
                if operator_gate is None or operator_gate.module_id != module.module_id:
                    raise ValueError(
                        f"operator gate step {step.step_id} must resolve the accepted operator gate"
                    )
                if step.checkpoint_binding_id is not None:
                    raise ValueError(
                        f"operator gate step {step.step_id} must not declare checkpoint_binding_id"
                    )
            else:
                if step.checkpoint_binding_id is None:
                    raise ValueError(f"hard step {step.step_id} must declare checkpoint_binding_id")
                binding_ids = {binding.binding_id for binding in module.executor_bindings}
                if step.checkpoint_binding_id not in binding_ids:
                    raise ValueError(
                        "hard step "
                        f"{step.step_id} must bind an executor from the "
                        "released v37a catalog"
                    )
                if (
                    module.module_class == "evidence_gate_module"
                    and step.operator_gate_id is not None
                ):
                    raise ValueError(
                        f"evidence gate step {step.step_id} must not declare operator_gate_id"
                    )

        if trace_step.observed_checkpoint_result_refs:
            if run_trace.trace_mode != V37B_REFERENCE_TRACE_MODE:
                raise ValueError(
                    "observed checkpoint refs require the reference trace mode contract"
                )
            for ref in trace_step.observed_checkpoint_result_refs:
                _resolve_repo_relative_path(
                    ref,
                    field_name=(
                        "run_trace.steps"
                        f"[{trace_step.planned_step_id}].observed_checkpoint_result_refs"
                    ),
                )
        if trace_step.accepted_compilation_occurred:
            raise ValueError(
                "run trace step "
                f"{trace_step.planned_step_id} must not claim accepted compilation in v37b"
            )


def assert_v37c_reference_instance_binding(
    *,
    intent_packet: MetaTestingIntentPacket,
    module_catalog: MetaModuleCatalog,
    sequence_contract: MetaLoopSequenceContract,
    reference_run_trace: MetaLoopRunTrace,
    executed_run_trace: MetaLoopRunTrace,
    checkpoint_result_manifest: MetaLoopCheckpointResultManifest,
) -> None:
    assert_v37b_reference_instance_binding(
        intent_packet=intent_packet,
        module_catalog=module_catalog,
        sequence_contract=sequence_contract,
        run_trace=reference_run_trace,
    )
    for field_name in ("reference_loop_family", "reference_instance_id", "intent_packet_id"):
        expected = getattr(intent_packet, field_name)
        if getattr(executed_run_trace, field_name) != expected:
            raise ValueError(f"reference instance binding mismatch for {field_name}")
        if getattr(checkpoint_result_manifest, field_name) != expected:
            raise ValueError(f"reference instance binding mismatch for {field_name}")
    if executed_run_trace.reference_anchor != intent_packet.reference_anchor:
        raise ValueError("reference instance binding mismatch for reference_anchor")
    if checkpoint_result_manifest.reference_anchor != intent_packet.reference_anchor:
        raise ValueError("reference instance binding mismatch for reference_anchor")


def assert_v37c_reference_bundle_consistent(
    *,
    intent_packet: MetaTestingIntentPacket,
    module_catalog: MetaModuleCatalog,
    sequence_contract: MetaLoopSequenceContract,
    reference_run_trace: MetaLoopRunTrace,
    executed_run_trace: MetaLoopRunTrace,
    checkpoint_result_manifest: MetaLoopCheckpointResultManifest,
) -> None:
    assert_v37b_reference_bundle_consistent(
        intent_packet=intent_packet,
        module_catalog=module_catalog,
        sequence_contract=sequence_contract,
        run_trace=reference_run_trace,
    )
    assert_v37c_reference_instance_binding(
        intent_packet=intent_packet,
        module_catalog=module_catalog,
        sequence_contract=sequence_contract,
        reference_run_trace=reference_run_trace,
        executed_run_trace=executed_run_trace,
        checkpoint_result_manifest=checkpoint_result_manifest,
    )

    if executed_run_trace.trace_mode != V37C_EXECUTED_TRACE_MODE:
        raise ValueError(
            f"accepted v37c run trace must use trace_mode {V37C_EXECUTED_TRACE_MODE!r}"
        )
    if executed_run_trace.checkpoint_result_manifest_ref is None:
        raise ValueError("executed run trace must bind checkpoint_result_manifest_ref")

    expected_step_ids_in_order = [step.step_id for step in sequence_contract.steps]
    if [step.planned_step_id for step in executed_run_trace.steps] != expected_step_ids_in_order:
        raise ValueError(
            "executed run trace planned_step_id order must match the accepted sequence contract"
        )
    if executed_run_trace.model_dump(
        mode="json", exclude_none=True
    ) == reference_run_trace.model_dump(
        mode="json",
        exclude_none=True,
    ):
        raise ValueError("executed run trace must remain distinct from the v37b reference trace")

    module_by_id = {module.module_id: module for module in module_catalog.modules}
    retry_edge_by_id = {item.retry_edge_id: item for item in sequence_contract.retry_edges}
    trace_step_by_id = {item.planned_step_id: item for item in executed_run_trace.steps}
    result_row_by_id = {
        row.result_row_id: row for row in checkpoint_result_manifest.checkpoint_results
    }
    branch_outcome_by_id = {
        row.branch_outcome_id: row for row in checkpoint_result_manifest.branch_outcomes
    }
    retry_outcome_by_id = {
        row.retry_outcome_id: row for row in checkpoint_result_manifest.retry_outcomes
    }
    manifest_ref = executed_run_trace.checkpoint_result_manifest_ref

    executed_checkpoint_capabilities: set[str] = set()
    skipped_checkpoint_capabilities: set[str] = set()

    for step in sequence_contract.steps:
        trace_step = trace_step_by_id[step.step_id]
        module = module_by_id[step.module_id]
        if trace_step.actual_module_id != step.module_id:
            raise ValueError(
                "executed run trace step "
                f"{step.step_id} must resolve actual_module_id to the bound module"
            )

        if trace_step.step_status == "executed_skip":
            if trace_step.consumed_inputs or trace_step.emitted_outputs:
                raise ValueError(
                    f"executed_skip step {step.step_id} must not claim "
                    "consumed_inputs or emitted_outputs"
                )
        else:
            if trace_step.consumed_inputs != step.required_inputs:
                raise ValueError(
                    f"executed step {step.step_id} consumed_inputs must match "
                    "the accepted sequence contract"
                )
            if trace_step.emitted_outputs != step.expected_outputs:
                raise ValueError(
                    f"executed step {step.step_id} emitted_outputs must match "
                    "the accepted sequence contract"
                )

        if module.module_class == "reasoning_module":
            if trace_step.step_status != "executed_pass":
                raise ValueError(
                    f"reasoning step {step.step_id} must use step_status = executed_pass in v37c"
                )
            if not trace_step.operational_influence_occurred:
                raise ValueError(
                    f"reasoning step {step.step_id} must keep operational_influence_occurred = true"
                )
            if trace_step.observed_checkpoint_result_refs:
                raise ValueError(
                    f"reasoning step {step.step_id} must not bind observed_checkpoint_result_refs"
                )
            if trace_step.actual_branch_outcome_ref is not None:
                raise ValueError(
                    f"reasoning step {step.step_id} must not bind actual_branch_outcome_ref"
                )
            if trace_step.actual_retry_outcome_refs is not None:
                raise ValueError(
                    f"reasoning step {step.step_id} must not bind actual_retry_outcome_refs"
                )
            continue

        if trace_step.operational_influence_occurred:
            raise ValueError(
                f"hard step {step.step_id} must not claim operational_influence_occurred"
            )

        if trace_step.step_status == "executed_skip":
            if trace_step.accepted_compilation_occurred:
                raise ValueError(
                    f"executed_skip step {step.step_id} must not claim "
                    "accepted_compilation_occurred"
                )
            if trace_step.observed_checkpoint_result_refs:
                raise ValueError(
                    f"executed_skip step {step.step_id} must not bind "
                    "observed_checkpoint_result_refs"
                )
            if trace_step.actual_branch_outcome_ref is not None:
                raise ValueError(
                    f"executed_skip step {step.step_id} must not bind actual_branch_outcome_ref"
                )
            if trace_step.actual_retry_outcome_refs is not None:
                raise ValueError(
                    f"executed_skip step {step.step_id} must not bind actual_retry_outcome_refs"
                )
            if module.module_class == "checkpoint_module":
                skipped_checkpoint_capabilities.add(module.capability_id)
            continue

        if module.module_class == "checkpoint_module":
            executed_checkpoint_capabilities.add(module.capability_id)

        if not trace_step.observed_checkpoint_result_refs:
            raise ValueError(
                f"executed hard step {step.step_id} must bind observed_checkpoint_result_refs"
            )

        row_ids: list[str] = []
        for index, ref in enumerate(trace_step.observed_checkpoint_result_refs):
            row_id = _parse_manifest_anchor_ref(
                ref,
                manifest_ref=manifest_ref,
                expected_section="checkpoint_results",
                field_name=(
                    f"run_trace.steps[{step.step_id}].observed_checkpoint_result_refs[{index}]"
                ),
            )
            row = result_row_by_id.get(row_id)
            if row is None:
                raise ValueError(
                    f"executed step {step.step_id} observed checkpoint ref "
                    "must resolve a manifest row"
                )
            if row.planned_step_id != step.step_id:
                raise ValueError(
                    f"manifest row {row_id} must stay bound to executed step {step.step_id}"
                )
            if row.module_id != module.module_id or row.module_class != module.module_class:
                raise ValueError(
                    f"manifest row {row_id} must resolve the bound module for step {step.step_id}"
                )
            binding_ids = {binding.binding_id: binding for binding in module.executor_bindings}
            if row.executor_binding_id not in binding_ids:
                raise ValueError(
                    f"manifest row {row_id} must bind an executor from the released v37a catalog"
                )
            binding = binding_ids[row.executor_binding_id]
            if (
                module.capability_id == "stop_gate_metrics_build"
                and row.executor_binding_ref != V37C_AUTHORITATIVE_STOP_GATE_BINDING_REF
            ):
                raise ValueError(
                    "stop_gate_metrics_build must stay bound to the "
                    "authoritative stop-gate executor"
                )
            if row.executor_binding_ref != binding.binding_ref:
                raise ValueError(
                    f"manifest row {row_id} executor_binding_ref must match "
                    "the released v37a catalog"
                )
            if row.capability_id != module.capability_id:
                raise ValueError(
                    f"manifest row {row_id} capability_id must match "
                    f"module capability {module.capability_id}"
                )
            row_ids.append(row_id)

        if step.branch_condition_id is not None:
            if trace_step.actual_branch_outcome_ref is None:
                raise ValueError(
                    f"executed step {step.step_id} must bind actual_branch_outcome_ref"
                )
            branch_outcome_id = _parse_manifest_anchor_ref(
                trace_step.actual_branch_outcome_ref,
                manifest_ref=manifest_ref,
                expected_section="branch_outcomes",
                field_name=f"run_trace.steps[{step.step_id}].actual_branch_outcome_ref",
            )
            branch_outcome = branch_outcome_by_id.get(branch_outcome_id)
            if branch_outcome is None:
                raise ValueError(
                    f"executed step {step.step_id} actual_branch_outcome_ref "
                    "must resolve a manifest outcome"
                )
            if branch_outcome.planned_step_id != step.step_id:
                raise ValueError(
                    f"branch outcome {branch_outcome_id} must stay bound to "
                    f"executed step {step.step_id}"
                )
            if branch_outcome.branch_condition_id != step.branch_condition_id:
                raise ValueError(
                    f"branch outcome {branch_outcome_id} must stay bound to "
                    f"branch_condition_id {step.branch_condition_id}"
                )
        elif trace_step.actual_branch_outcome_ref is not None:
            raise ValueError(
                f"step {step.step_id} must not bind actual_branch_outcome_ref "
                "without branch_condition_id"
            )

        if trace_step.step_status == "executed_retry":
            if trace_step.actual_retry_outcome_refs is None:
                raise ValueError(f"retried step {step.step_id} must bind actual_retry_outcome_refs")
            if len(row_ids) < 2:
                raise ValueError(
                    f"retried step {step.step_id} must bind at least two manifest result rows"
                )
            if not any(
                result_row_by_id[row_id].attempt_status == "attempted_fail" for row_id in row_ids
            ):
                raise ValueError(
                    f"retried step {step.step_id} must preserve at least one "
                    "attempted_fail manifest row"
                )
            for index, ref in enumerate(trace_step.actual_retry_outcome_refs):
                retry_outcome_id = _parse_manifest_anchor_ref(
                    ref,
                    manifest_ref=manifest_ref,
                    expected_section="retry_outcomes",
                    field_name=(
                        f"run_trace.steps[{step.step_id}].actual_retry_outcome_refs[{index}]"
                    ),
                )
                retry_outcome = retry_outcome_by_id.get(retry_outcome_id)
                if retry_outcome is None:
                    raise ValueError(
                        f"retried step {step.step_id} retry outcome ref must "
                        "resolve a manifest retry outcome"
                    )
                if retry_outcome.planned_step_id != step.step_id:
                    raise ValueError(
                        f"retry outcome {retry_outcome_id} must stay bound to "
                        f"executed step {step.step_id}"
                    )
                retry_edge = retry_edge_by_id.get(retry_outcome.retry_edge_id)
                if retry_edge is None:
                    raise ValueError(
                        f"retry outcome {retry_outcome_id} must resolve an accepted retry edge"
                    )
                if retry_edge.from_step_id != step.step_id:
                    raise ValueError(
                        f"retry outcome {retry_outcome_id} must stay bound to step {step.step_id}"
                    )
                if retry_outcome.triggering_result_row_id not in row_ids:
                    raise ValueError(
                        f"retry outcome {retry_outcome_id} triggering row "
                        f"must belong to executed step {step.step_id}"
                    )
                if retry_outcome.terminal_result_row_id not in row_ids:
                    raise ValueError(
                        f"retry outcome {retry_outcome_id} terminal row "
                        f"must belong to executed step {step.step_id}"
                    )
        elif trace_step.actual_retry_outcome_refs is not None:
            raise ValueError(
                f"non-retried step {step.step_id} must not bind actual_retry_outcome_refs"
            )

        attempt_statuses = {result_row_by_id[row_id].attempt_status for row_id in row_ids}
        if trace_step.step_status == "executed_pass" and attempt_statuses != {"attempted_pass"}:
            raise ValueError(
                f"executed_pass step {step.step_id} must bind only attempted_pass manifest rows"
            )
        if trace_step.step_status == "executed_fail" and attempt_statuses != {"attempted_fail"}:
            raise ValueError(
                f"executed_fail step {step.step_id} must bind only attempted_fail manifest rows"
            )
        if trace_step.step_status == "executed_retry" and attempt_statuses != {
            "attempted_fail",
            "attempted_pass",
        }:
            raise ValueError(
                f"executed_retry step {step.step_id} must bind attempted_fail "
                "and attempted_pass manifest rows"
            )

        if module.module_class == "checkpoint_module":
            if module.capability_id == "quality_dashboard_build":
                expected_output_refs = {"artifacts/quality_dashboard_v65_closeout.json"}
            elif module.capability_id == "stop_gate_metrics_build":
                expected_output_refs = {
                    "artifacts/stop_gate/metrics_v65_closeout.json",
                    "artifacts/stop_gate/report_v65_closeout.md",
                }
            else:
                expected_output_refs = set()
            actual_output_refs = {
                artifact.artifact_ref
                for row_id in row_ids
                for artifact in result_row_by_id[row_id].output_artifacts
            }
            if actual_output_refs != expected_output_refs:
                raise ValueError(
                    f"executed step {step.step_id} must preserve the expected output artifact refs"
                )

        if (
            module.module_class == "operator_gate_module"
            and not trace_step.accepted_compilation_occurred
        ):
            raise ValueError(
                f"operator gate step {step.step_id} must mark accepted_compilation_occurred = true"
            )
        if (
            module.module_class != "operator_gate_module"
            and trace_step.accepted_compilation_occurred
        ):
            raise ValueError(
                f"non-operator step {step.step_id} must not mark accepted_compilation_occurred"
            )

    if executed_checkpoint_capabilities != set(
        checkpoint_result_manifest.executed_checkpoint_capabilities
    ):
        raise ValueError(
            "executed checkpoint capabilities must match the intentional v37c subset declaration"
        )
    if skipped_checkpoint_capabilities != set(
        checkpoint_result_manifest.non_executed_released_capabilities
    ):
        raise ValueError(
            "skipped checkpoint capabilities must match the declared non-executed released subset"
        )


__all__ = [
    "FROZEN_V37A_AUTHORITATIVE_INPUT_IDS",
    "FROZEN_V37A_DRIFT_TAXONOMY",
    "FROZEN_V37A_MODULE_CLASSES",
    "FROZEN_V37A_REQUIRED_CHECKPOINT_CAPABILITIES",
    "META_LOOP_RUN_TRACE_SCHEMA",
    "META_LOOP_CHECKPOINT_RESULT_MANIFEST_SCHEMA",
    "META_LOOP_SEQUENCE_CONTRACT_SCHEMA",
    "META_MODULE_CATALOG_SCHEMA",
    "META_TESTING_INTENT_PACKET_SCHEMA",
    "FROZEN_V37B_PHASE_BOUNDARIES",
    "FROZEN_V37C_EXECUTED_CHECKPOINT_CAPABILITIES",
    "FROZEN_V37C_NON_EXECUTED_RELEASED_CAPABILITIES",
    "V37A_INTENT_PACKET_ID",
    "V37A_OPERATOR_SURFACE",
    "V37A_REFERENCE_ANCHOR_SHAPE",
    "V37A_REFERENCE_ARC",
    "V37A_REFERENCE_INSTANCE_ID",
    "V37A_REFERENCE_LOOP_FAMILY",
    "V37A_REFERENCE_PHASE",
    "MetaAuthoritativeInputRef",
    "MetaCheckpointOutputArtifact",
    "MetaExecutorBinding",
    "MetaExecutorParameterPolicy",
    "MetaExecutorParameterSlot",
    "MetaLoopBranchCondition",
    "MetaLoopBranchOutcomeRecord",
    "MetaLoopCheckpointResultManifest",
    "MetaLoopCheckpointResultRow",
    "MetaLoopFailureEdge",
    "MetaLoopOperatorGate",
    "MetaLoopRetryEdge",
    "MetaLoopRetryOutcomeRecord",
    "MetaLoopRunTrace",
    "MetaLoopRunTraceStep",
    "MetaLoopSequenceContract",
    "MetaLoopSequenceStep",
    "MetaModuleCatalog",
    "MetaModuleDescriptor",
    "MetaReasoningDispatchProvenance",
    "MetaReferenceLoopAnchor",
    "MetaTestingIntentPacket",
    "assert_v37a_reference_bundle_consistent",
    "assert_v37a_reference_instance_binding",
    "assert_v37b_reference_bundle_consistent",
    "assert_v37b_reference_instance_binding",
    "assert_v37c_reference_bundle_consistent",
    "assert_v37c_reference_instance_binding",
    "canonicalize_meta_loop_checkpoint_result_manifest_payload",
    "canonicalize_meta_loop_run_trace_payload",
    "canonicalize_meta_loop_sequence_contract_payload",
    "canonicalize_meta_module_catalog_payload",
    "canonicalize_meta_testing_intent_packet_payload",
    "V37B_REFERENCE_TRACE_MODE",
    "V37C_AUTHORITATIVE_STOP_GATE_BINDING_REF",
    "V37C_EXECUTED_TRACE_MODE",
]
