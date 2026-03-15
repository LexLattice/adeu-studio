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
    "meta_loop_conformance_report@1",
    "meta_loop_drift_diagnostics@1",
    "meta_loop_run_trace@1",
    "meta_loop_sequence_contract@1",
]

META_TESTING_INTENT_PACKET_SCHEMA = "meta_testing_intent_packet@1"
META_MODULE_CATALOG_SCHEMA = "meta_module_catalog@1"
V37A_REFERENCE_LOOP_FAMILY = "arc_bundle_recursive_compilation_loop"
V37A_REFERENCE_ANCHOR_SHAPE = "arc_closeout_bundle_instance"
V37A_REFERENCE_ARC = 65
V37A_REFERENCE_PHASE = "closeout"
V37A_OPERATOR_SURFACE = "explicit_repo_acceptance_boundary"
V37A_REFERENCE_INSTANCE_ID = "arc_closeout_v65_reference"
V37A_INTENT_PACKET_ID = "v37a_arc_closeout_v65_intent"

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
    "meta_loop_run_trace@1",
    "meta_loop_sequence_contract@1",
)


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


def canonicalize_meta_testing_intent_packet_payload(payload: dict[str, Any]) -> dict[str, Any]:
    model = MetaTestingIntentPacket.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


def canonicalize_meta_module_catalog_payload(payload: dict[str, Any]) -> dict[str, Any]:
    model = MetaModuleCatalog.model_validate(deepcopy(payload))
    return model.model_dump(mode="json", exclude_none=True)


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


__all__ = [
    "META_MODULE_CATALOG_SCHEMA",
    "META_TESTING_INTENT_PACKET_SCHEMA",
    "V37A_INTENT_PACKET_ID",
    "V37A_OPERATOR_SURFACE",
    "V37A_REFERENCE_ANCHOR_SHAPE",
    "V37A_REFERENCE_ARC",
    "V37A_REFERENCE_INSTANCE_ID",
    "V37A_REFERENCE_LOOP_FAMILY",
    "V37A_REFERENCE_PHASE",
    "FROZEN_V37A_AUTHORITATIVE_INPUT_IDS",
    "FROZEN_V37A_DRIFT_TAXONOMY",
    "FROZEN_V37A_MODULE_CLASSES",
    "FROZEN_V37A_REQUIRED_CHECKPOINT_CAPABILITIES",
    "MetaAuthoritativeInputRef",
    "MetaExecutorBinding",
    "MetaExecutorParameterPolicy",
    "MetaExecutorParameterSlot",
    "MetaModuleCatalog",
    "MetaModuleDescriptor",
    "MetaReasoningDispatchProvenance",
    "MetaReferenceLoopAnchor",
    "MetaTestingIntentPacket",
    "assert_v37a_reference_bundle_consistent",
    "assert_v37a_reference_instance_binding",
    "canonicalize_meta_module_catalog_payload",
    "canonicalize_meta_testing_intent_packet_payload",
]
