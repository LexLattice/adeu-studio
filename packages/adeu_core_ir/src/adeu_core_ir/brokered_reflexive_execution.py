from __future__ import annotations

import hashlib
import json
from collections import Counter
from pathlib import Path
from typing import Any, Literal

from adeu_ir.repo import repo_root
from pydantic import BaseModel, ConfigDict, Field, model_validator

BrokeredReflexivePayloadSchemaVersion = Literal["adeu_brokered_reflexive_payload@1"]
BrokeredReflexiveExecutionPlanSchemaVersion = Literal["adeu_brokered_reflexive_execution_plan@1"]
BrokeredADEUDimension = Literal["ontology", "epistemics", "deontics", "utility"]
BrokeredDomainClass = Literal["hard_physical", "soft_reflexive", "rule_based"]
BrokeredAgentRole = Literal[
    "orchestrator",
    "explorer",
    "adversarial_reviewer",
    "implementer",
    "code_reviewer",
    "gatekeeper",
]
BrokeredBudgetPosture = Literal["tight", "medium", "broad"]
BrokeredInterventionDepth = Literal[
    "observation_only",
    "advisory_reframing",
    "constraint_suggestion",
]
BrokeredPressureClass = Literal[
    "coercive_reprioritization",
    "epistemic_suppression",
    "utility_capture",
    "utility_deformation",
]
BrokeredAllowedEvidenceScope = Literal[
    "compiled_plan",
    "repo_codebase",
    "repo_control_plane",
    "source_payload",
    "subagent_findings_non_authoritative",
    "test_and_gate_outputs",
]
BrokeredDeonticGuardrail = Literal[
    "bind_claims_to_repo_evidence",
    "fail_closed_on_missing_truth_condition",
    "no_authority_substitution",
    "no_scope_widening",
    "no_unlicensed_utility_rewrite",
]
BrokeredRefusalReason = Literal[
    "contradictory_intervention_depth",
    "missing_authority_boundary",
    "missing_domain_class",
    "missing_task_truth_condition",
    "non_advisory_action_request",
    "unsupported_delegation_role",
]
BrokeredStageKind = Literal[
    "intent_normalization",
    "route_selection",
    "delegation_scaffolding",
    "adversarial_review",
    "implementation",
    "code_review",
    "gate_verification",
    "recursive_honesty_audit",
]
BrokeredAgentModel = Literal["gpt-5.4", "gpt-5.3-codex", "gpt-5.4-mini"]
BrokeredReasoningEffort = Literal["xhigh"]

ADEU_BROKERED_REFLEXIVE_PAYLOAD_SCHEMA = "adeu_brokered_reflexive_payload@1"
ADEU_BROKERED_REFLEXIVE_EXECUTION_PLAN_SCHEMA = "adeu_brokered_reflexive_execution_plan@1"
BROKERED_REFLEXIVE_PRIMARY_EXECUTION_SURFACE = "adeu.compile_brokered_reflexive_execution"
BROKERED_REFLEXIVE_SUPPORTING_API_ROUTE = "/urm/reflex/compile"

_HEX16_CHARS = frozenset("0123456789abcdef")
_HEX64_CHARS = frozenset("0123456789abcdef")
_FROZEN_ROLE_ORDER: tuple[BrokeredAgentRole, ...] = (
    "orchestrator",
    "explorer",
    "adversarial_reviewer",
    "implementer",
    "code_reviewer",
    "gatekeeper",
)
_FROZEN_STAGE_ORDER: tuple[BrokeredStageKind, ...] = (
    "intent_normalization",
    "route_selection",
    "delegation_scaffolding",
    "adversarial_review",
    "implementation",
    "code_review",
    "gate_verification",
    "recursive_honesty_audit",
)
_FROZEN_ROUTING_ORDER_BY_DOMAIN: dict[BrokeredDomainClass, tuple[BrokeredADEUDimension, ...]] = {
    "hard_physical": ("ontology", "epistemics", "deontics", "utility"),
    "soft_reflexive": ("utility", "deontics", "ontology", "epistemics"),
    "rule_based": ("deontics", "ontology", "epistemics", "utility"),
}
_FROZEN_MODEL_BY_ROLE: dict[BrokeredAgentRole, BrokeredAgentModel] = {
    "orchestrator": "gpt-5.4",
    "explorer": "gpt-5.4-mini",
    "adversarial_reviewer": "gpt-5.4",
    "implementer": "gpt-5.3-codex",
    "code_reviewer": "gpt-5.4",
    "gatekeeper": "gpt-5.4-mini",
}
_FROZEN_BUDGET_BY_ROLE: dict[BrokeredAgentRole, BrokeredBudgetPosture] = {
    "orchestrator": "broad",
    "explorer": "tight",
    "adversarial_reviewer": "tight",
    "implementer": "medium",
    "code_reviewer": "tight",
    "gatekeeper": "tight",
}
_FROZEN_NON_AUTHORITY_BY_ROLE: dict[BrokeredAgentRole, str] = {
    "orchestrator": (
        "The orchestrator may decompose, integrate, and decide next local steps, "
        "but may not declare accepted compilation or governance by prose alone."
    ),
    "explorer": (
        "Exploration outputs are context only and may not declare pass/fail, acceptance, "
        "or authority."
    ),
    "adversarial_reviewer": (
        "Adversarial review outputs are findings only and may not widen scope, rewrite intent, "
        "or substitute for acceptance."
    ),
    "implementer": (
        "Implementation outputs are bounded changes only and may not assert merge, closeout, "
        "or policy authority."
    ),
    "code_reviewer": (
        "Code review outputs are findings only and may not substitute for gate results "
        "or merge authority."
    ),
    "gatekeeper": (
        "Gate reports are observational only and may not waive constraints, redefine semantics, "
        "or promote advisory output into acceptance."
    ),
}
_FROZEN_ALLOWED_EVIDENCE_BY_ROLE: dict[
    BrokeredAgentRole,
    tuple[BrokeredAllowedEvidenceScope, ...],
] = {
    "orchestrator": (
        "compiled_plan",
        "repo_codebase",
        "repo_control_plane",
        "source_payload",
        "subagent_findings_non_authoritative",
        "test_and_gate_outputs",
    ),
    "explorer": ("repo_codebase", "repo_control_plane", "source_payload"),
    "adversarial_reviewer": ("compiled_plan", "repo_control_plane", "source_payload"),
    "implementer": ("compiled_plan", "repo_codebase", "source_payload", "test_and_gate_outputs"),
    "code_reviewer": ("compiled_plan", "repo_codebase", "source_payload", "test_and_gate_outputs"),
    "gatekeeper": ("compiled_plan", "repo_control_plane", "test_and_gate_outputs"),
}
_FROZEN_GUARDRAILS_BY_ROLE: dict[
    BrokeredAgentRole,
    tuple[BrokeredDeonticGuardrail, ...],
] = {
    "orchestrator": (
        "bind_claims_to_repo_evidence",
        "fail_closed_on_missing_truth_condition",
        "no_authority_substitution",
        "no_scope_widening",
        "no_unlicensed_utility_rewrite",
    ),
    "explorer": (
        "bind_claims_to_repo_evidence",
        "fail_closed_on_missing_truth_condition",
        "no_authority_substitution",
    ),
    "adversarial_reviewer": (
        "bind_claims_to_repo_evidence",
        "fail_closed_on_missing_truth_condition",
        "no_authority_substitution",
        "no_scope_widening",
    ),
    "implementer": (
        "bind_claims_to_repo_evidence",
        "fail_closed_on_missing_truth_condition",
        "no_scope_widening",
        "no_unlicensed_utility_rewrite",
    ),
    "code_reviewer": (
        "bind_claims_to_repo_evidence",
        "fail_closed_on_missing_truth_condition",
        "no_authority_substitution",
    ),
    "gatekeeper": (
        "bind_claims_to_repo_evidence",
        "fail_closed_on_missing_truth_condition",
        "no_authority_substitution",
    ),
}
_FROZEN_REPLY_CONTRACT_BY_ROLE: dict[BrokeredAgentRole, tuple[str, ...]] = {
    "orchestrator": (
        "integrate_findings",
        "preserve_payload_fidelity",
        "refuse_unbound_authority_claims",
    ),
    "explorer": ("context_only", "no_authority_claims", "repo_refs_only"),
    "adversarial_reviewer": (
        "bind_findings_to_payload_or_repo",
        "findings_first",
        "no_fix_commitment",
    ),
    "implementer": ("bounded_patch_only", "respect_scope", "surface_risks"),
    "code_reviewer": ("bugs_first", "regression_risks", "tests_or_gaps"),
    "gatekeeper": ("no_semantic_waivers", "report_gate_state_only", "report_inputs_used"),
}
_FROZEN_STAGE_BY_ROLE: dict[BrokeredAgentRole, BrokeredStageKind] = {
    "orchestrator": "delegation_scaffolding",
    "explorer": "route_selection",
    "adversarial_reviewer": "adversarial_review",
    "implementer": "implementation",
    "code_reviewer": "code_review",
    "gatekeeper": "gate_verification",
}
_FROZEN_ACCEPTED_COMPILATION_BOUNDARY_REFS: tuple[str, ...] = (
    "repo:accepted_lock_docs",
    "repo:human_acceptance_boundary",
    "repo:tests_and_gates",
)
_FROZEN_RECURSIVE_HONESTY_CHECKS: tuple[str, ...] = (
    "advisory_boundary_preserved",
    "authority_boundary_present",
    "delegation_scope_complete",
    "task_truth_condition_present",
    "utility_intervention_licensed",
)

def _hash16(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode(
            "utf-8"
        )
    ).hexdigest()[:16]


def _hash64(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode(
            "utf-8"
        )
    ).hexdigest()


def _is_hex16(value: str) -> bool:
    return len(value) == 16 and all(char in _HEX16_CHARS for char in value)


def _is_hex64(value: str) -> bool:
    return len(value) == 64 and all(char in _HEX64_CHARS for char in value)


def _normalize_repo_relative_path(value: str, *, field_name: str) -> str:
    normalized = value.strip().replace("\\", "/")
    if not normalized:
        raise ValueError(f"{field_name} must not be empty")
    if normalized.startswith("/") or normalized.startswith("../") or "/../" in normalized:
        raise ValueError(f"{field_name} must be repository-relative")
    return normalized


def _sha256_repo_file(value: str, *, field_name: str) -> str:
    normalized = _normalize_repo_relative_path(value, field_name=field_name)
    path = repo_root(anchor=Path(__file__)) / normalized
    if not path.is_file():
        raise ValueError(f"{field_name} must resolve to an existing repo file")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _assert_sorted_unique(values: list[str], *, field_name: str) -> None:
    if any(not value for value in values):
        raise ValueError(f"{field_name} must not contain empty values")
    if values != sorted(values):
        raise ValueError(f"{field_name} must be lexicographically sorted")
    if len(values) != len(set(values)):
        raise ValueError(f"{field_name} must not contain duplicates")


def _role_sort_key(value: BrokeredAgentRole) -> int:
    return _FROZEN_ROLE_ORDER.index(value)


def _stage_sort_key(value: BrokeredStageKind) -> int:
    return _FROZEN_STAGE_ORDER.index(value)


class BrokeredMetaOntology(BaseModel):
    model_config = ConfigDict(extra="forbid")

    realist_thesis: str = Field(min_length=1)
    mediated_ontology_clause: str = Field(min_length=1)
    teleological_vector: str = Field(min_length=1)


class BrokeredCompilerPipeline(BaseModel):
    model_config = ConfigDict(extra="forbid")

    ontology_question: str = Field(min_length=1)
    epistemics_question: str = Field(min_length=1)
    deontics_question: str = Field(min_length=1)
    utility_question: str = Field(min_length=1)


class BrokeredAdaptiveDomainRouting(BaseModel):
    model_config = ConfigDict(extra="forbid")

    hard_physical_order: list[BrokeredADEUDimension]
    soft_reflexive_order: list[BrokeredADEUDimension]
    rule_based_order: list[BrokeredADEUDimension]

    @model_validator(mode="after")
    def _validate_contract(self) -> "BrokeredAdaptiveDomainRouting":
        expected = {
            "hard_physical_order": list(_FROZEN_ROUTING_ORDER_BY_DOMAIN["hard_physical"]),
            "soft_reflexive_order": list(_FROZEN_ROUTING_ORDER_BY_DOMAIN["soft_reflexive"]),
            "rule_based_order": list(_FROZEN_ROUTING_ORDER_BY_DOMAIN["rule_based"]),
        }
        for field_name, expected_value in expected.items():
            actual_value = getattr(self, field_name)
            if actual_value != expected_value:
                raise ValueError(f"{field_name} must match the frozen routing order")
        return self

    def order_for(self, domain_class: BrokeredDomainClass) -> list[BrokeredADEUDimension]:
        if domain_class == "hard_physical":
            return list(self.hard_physical_order)
        if domain_class == "soft_reflexive":
            return list(self.soft_reflexive_order)
        return list(self.rule_based_order)


class BrokeredDelegationDoctrine(BaseModel):
    model_config = ConfigDict(extra="forbid")

    delegation_axiom: str = Field(min_length=1)
    task_truth_condition_clause: str = Field(min_length=1)
    epistemic_severance_clause: str = Field(min_length=1)
    epistemic_abuse_clause: str = Field(min_length=1)


class BrokeredSentinelDoctrine(BaseModel):
    model_config = ConfigDict(extra="forbid")

    udeo_inversion: str = Field(min_length=1)
    sentinel_axiom: str = Field(min_length=1)
    socratic_limit: str = Field(min_length=1)
    protected_aims: list[str]
    forbidden_pressure_classes: list[BrokeredPressureClass]
    permitted_intervention_depth: BrokeredInterventionDepth

    @model_validator(mode="after")
    def _validate_contract(self) -> "BrokeredSentinelDoctrine":
        _assert_sorted_unique(self.protected_aims, field_name="protected_aims")
        if not self.forbidden_pressure_classes:
            raise ValueError("forbidden_pressure_classes must be non-empty")
        if self.forbidden_pressure_classes != sorted(self.forbidden_pressure_classes):
            raise ValueError("forbidden_pressure_classes must be lexicographically sorted")
        if len(set(self.forbidden_pressure_classes)) != len(self.forbidden_pressure_classes):
            raise ValueError("forbidden_pressure_classes must not contain duplicates")
        return self


class BrokeredRecursiveHonestyDoctrine(BaseModel):
    model_config = ConfigDict(extra="forbid")

    recursive_honesty_axiom: str = Field(min_length=1)
    fail_closed_refusal_reasons: list[BrokeredRefusalReason]

    @model_validator(mode="after")
    def _validate_contract(self) -> "BrokeredRecursiveHonestyDoctrine":
        if self.fail_closed_refusal_reasons != sorted(self.fail_closed_refusal_reasons):
            raise ValueError("fail_closed_refusal_reasons must be lexicographically sorted")
        if len(set(self.fail_closed_refusal_reasons)) != len(self.fail_closed_refusal_reasons):
            raise ValueError("fail_closed_refusal_reasons must not contain duplicates")
        return self


class AdeuBrokeredReflexivePayload(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: BrokeredReflexivePayloadSchemaVersion = ADEU_BROKERED_REFLEXIVE_PAYLOAD_SCHEMA
    payload_id: str = Field(min_length=1)
    title: str = Field(min_length=1)
    source_doc_ref: str = Field(min_length=1)
    source_doc_sha256: str = Field(min_length=64, max_length=64)
    domain_class: BrokeredDomainClass
    requested_roles: list[BrokeredAgentRole]
    max_delegation_depth: int = Field(ge=1, le=4)
    advisory_only: bool = True
    meta_ontology: BrokeredMetaOntology
    compiler_pipeline: BrokeredCompilerPipeline
    adaptive_domain_routing: BrokeredAdaptiveDomainRouting
    delegation_doctrine: BrokeredDelegationDoctrine
    sentinel_doctrine: BrokeredSentinelDoctrine
    recursive_honesty_doctrine: BrokeredRecursiveHonestyDoctrine

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuBrokeredReflexivePayload":
        self.source_doc_ref = _normalize_repo_relative_path(
            self.source_doc_ref,
            field_name="source_doc_ref",
        )
        actual_source_doc_sha256 = _sha256_repo_file(
            self.source_doc_ref,
            field_name="source_doc_ref",
        )
        if not _is_hex64(self.source_doc_sha256):
            raise ValueError("source_doc_sha256 must be lowercase sha256 hex")
        if self.source_doc_sha256 != actual_source_doc_sha256:
            raise ValueError("source_doc_sha256 must match repo file bytes")
        if not self.advisory_only:
            raise ValueError("advisory_only must remain true in the first family")
        if not self.requested_roles:
            raise ValueError("requested_roles must be non-empty")
        if self.requested_roles[0] != "orchestrator":
            raise ValueError("requested_roles must start with orchestrator")
        if self.requested_roles != sorted(self.requested_roles, key=_role_sort_key):
            raise ValueError("requested_roles must follow the frozen role order")
        if len(set(self.requested_roles)) != len(self.requested_roles):
            raise ValueError("requested_roles must not contain duplicates")
        return self


class BrokeredTaskTruthCondition(BaseModel):
    model_config = ConfigDict(extra="forbid")

    statement: str = Field(min_length=1)
    authority_refs: list[str]
    refuse_on_missing_authority: bool = True
    local_only: bool = True

    @model_validator(mode="after")
    def _validate_contract(self) -> "BrokeredTaskTruthCondition":
        _assert_sorted_unique(self.authority_refs, field_name="authority_refs")
        return self


class BrokeredPromptPacket(BaseModel):
    model_config = ConfigDict(extra="forbid")

    prompt_id: str = Field(min_length=16, max_length=16)
    role: BrokeredAgentRole
    recommended_agent_model: BrokeredAgentModel
    reasoning_effort: BrokeredReasoningEffort = "xhigh"
    objective: str = Field(min_length=1)
    constraints: list[str]
    reply_contract: list[str]

    @model_validator(mode="after")
    def _validate_contract(self) -> "BrokeredPromptPacket":
        if not _is_hex16(self.prompt_id):
            raise ValueError("prompt_id must be lowercase hex")
        _assert_sorted_unique(self.constraints, field_name="constraints")
        _assert_sorted_unique(self.reply_contract, field_name="reply_contract")
        if self.recommended_agent_model != _FROZEN_MODEL_BY_ROLE[self.role]:
            raise ValueError("recommended_agent_model must match the frozen role mapping")
        return self


class BrokeredSessionPacket(BaseModel):
    model_config = ConfigDict(extra="forbid")

    session_id: str = Field(min_length=16, max_length=16)
    role: BrokeredAgentRole
    local_objective: str = Field(min_length=1)
    delegation_depth_limit: int = Field(ge=0, le=4)
    budget_posture: BrokeredBudgetPosture
    task_truth_condition: BrokeredTaskTruthCondition
    allowed_evidence_scope: list[BrokeredAllowedEvidenceScope]
    deontic_guardrails: list[BrokeredDeonticGuardrail]
    non_authority_statement: str = Field(min_length=1)
    prompt_packet: BrokeredPromptPacket

    @model_validator(mode="after")
    def _validate_contract(self) -> "BrokeredSessionPacket":
        if not _is_hex16(self.session_id):
            raise ValueError("session_id must be lowercase hex")
        if self.allowed_evidence_scope != sorted(self.allowed_evidence_scope):
            raise ValueError("allowed_evidence_scope must be lexicographically sorted")
        if len(set(self.allowed_evidence_scope)) != len(self.allowed_evidence_scope):
            raise ValueError("allowed_evidence_scope must not contain duplicates")
        if self.deontic_guardrails != sorted(self.deontic_guardrails):
            raise ValueError("deontic_guardrails must be lexicographically sorted")
        if len(set(self.deontic_guardrails)) != len(self.deontic_guardrails):
            raise ValueError("deontic_guardrails must not contain duplicates")
        if self.budget_posture != _FROZEN_BUDGET_BY_ROLE[self.role]:
            raise ValueError("budget_posture must match the frozen role mapping")
        if self.non_authority_statement != _FROZEN_NON_AUTHORITY_BY_ROLE[self.role]:
            raise ValueError("non_authority_statement must match the frozen role mapping")
        if self.prompt_packet.role != self.role:
            raise ValueError("prompt_packet.role must match session role")
        return self


class BrokeredExecutionLayer(BaseModel):
    model_config = ConfigDict(extra="forbid")

    layer_id: str = Field(min_length=16, max_length=16)
    stage: BrokeredStageKind
    owner_role: BrokeredAgentRole
    input_refs: list[str]
    output_refs: list[str]
    success_condition: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "BrokeredExecutionLayer":
        if not _is_hex16(self.layer_id):
            raise ValueError("layer_id must be lowercase hex")
        _assert_sorted_unique(self.input_refs, field_name="input_refs")
        _assert_sorted_unique(self.output_refs, field_name="output_refs")
        return self


class UtilityCaptureRiskRule(BaseModel):
    model_config = ConfigDict(extra="forbid")

    risk_id: str = Field(min_length=16, max_length=16)
    pressure_class: BrokeredPressureClass
    detection_signal: str = Field(min_length=1)
    response_posture: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "UtilityCaptureRiskRule":
        if not _is_hex16(self.risk_id):
            raise ValueError("risk_id must be lowercase hex")
        return self


class BrokeredSentinelProfile(BaseModel):
    model_config = ConfigDict(extra="forbid")

    protected_aims: list[str]
    forbidden_pressure_classes: list[BrokeredPressureClass]
    permitted_intervention_depth: BrokeredInterventionDepth
    utility_capture_risk_rules: list[UtilityCaptureRiskRule]

    @model_validator(mode="after")
    def _validate_contract(self) -> "BrokeredSentinelProfile":
        _assert_sorted_unique(self.protected_aims, field_name="protected_aims")
        if self.forbidden_pressure_classes != sorted(self.forbidden_pressure_classes):
            raise ValueError("forbidden_pressure_classes must be lexicographically sorted")
        if len(set(self.forbidden_pressure_classes)) != len(self.forbidden_pressure_classes):
            raise ValueError("forbidden_pressure_classes must not contain duplicates")
        risk_sort_keys = [
            (item.pressure_class, item.risk_id) for item in self.utility_capture_risk_rules
        ]
        if risk_sort_keys != sorted(risk_sort_keys):
            raise ValueError("utility_capture_risk_rules must be lexicographically sorted")
        observed_pressure_classes = [
            item.pressure_class for item in self.utility_capture_risk_rules
        ]
        if observed_pressure_classes != self.forbidden_pressure_classes:
            raise ValueError(
                "utility_capture_risk_rules must cover forbidden_pressure_classes exactly once"
            )
        return self


class BrokeredRecursiveHonestyProtocol(BaseModel):
    model_config = ConfigDict(extra="forbid")

    self_audit_required: bool = True
    required_checks: list[str]
    fail_closed_refusal_reasons: list[BrokeredRefusalReason]
    audit_stage: BrokeredStageKind = "recursive_honesty_audit"

    @model_validator(mode="after")
    def _validate_contract(self) -> "BrokeredRecursiveHonestyProtocol":
        _assert_sorted_unique(self.required_checks, field_name="required_checks")
        if self.required_checks != sorted(_FROZEN_RECURSIVE_HONESTY_CHECKS):
            raise ValueError("required_checks must match the frozen recursive-honesty checks")
        if self.fail_closed_refusal_reasons != sorted(self.fail_closed_refusal_reasons):
            raise ValueError("fail_closed_refusal_reasons must be lexicographically sorted")
        if len(set(self.fail_closed_refusal_reasons)) != len(self.fail_closed_refusal_reasons):
            raise ValueError("fail_closed_refusal_reasons must not contain duplicates")
        if self.audit_stage != "recursive_honesty_audit":
            raise ValueError("audit_stage must remain recursive_honesty_audit")
        return self


class BrokeredExecutionSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")

    total_layers: int = Field(ge=0)
    total_sessions: int = Field(ge=0)
    counts_by_role: dict[str, int]
    counts_by_stage: dict[str, int]

    @model_validator(mode="after")
    def _validate_contract(self) -> "BrokeredExecutionSummary":
        if list(self.counts_by_role.keys()) != sorted(self.counts_by_role.keys()):
            raise ValueError("counts_by_role keys must be lexicographically sorted")
        if any(key not in _FROZEN_ROLE_ORDER for key in self.counts_by_role):
            raise ValueError("counts_by_role contains unsupported role")
        if list(self.counts_by_stage.keys()) != sorted(self.counts_by_stage.keys()):
            raise ValueError("counts_by_stage keys must be lexicographically sorted")
        if any(key not in _FROZEN_STAGE_ORDER for key in self.counts_by_stage):
            raise ValueError("counts_by_stage contains unsupported stage")
        return self


class AdeuBrokeredReflexiveExecutionPlan(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: BrokeredReflexiveExecutionPlanSchemaVersion = (
        ADEU_BROKERED_REFLEXIVE_EXECUTION_PLAN_SCHEMA
    )
    payload_id: str = Field(min_length=1)
    plan_id: str = Field(min_length=16, max_length=16)
    source_doc_ref: str = Field(min_length=1)
    source_doc_sha256: str = Field(min_length=64, max_length=64)
    source_payload_hash: str = Field(min_length=64, max_length=64)
    domain_class: BrokeredDomainClass
    inspection_order: list[BrokeredADEUDimension]
    max_delegation_depth: int = Field(ge=1, le=4)
    advisory_only: bool = True
    primary_execution_surface: str = BROKERED_REFLEXIVE_PRIMARY_EXECUTION_SURFACE
    supporting_api_route: str = BROKERED_REFLEXIVE_SUPPORTING_API_ROUTE
    accepted_compilation_boundary_refs: list[str]
    sessions: list[BrokeredSessionPacket]
    execution_ladder: list[BrokeredExecutionLayer]
    sentinel_profile: BrokeredSentinelProfile
    recursive_honesty_protocol: BrokeredRecursiveHonestyProtocol
    summary: BrokeredExecutionSummary

    @model_validator(mode="after")
    def _validate_contract(self) -> "AdeuBrokeredReflexiveExecutionPlan":
        if not _is_hex16(self.plan_id):
            raise ValueError("plan_id must be lowercase hex")
        self.source_doc_ref = _normalize_repo_relative_path(
            self.source_doc_ref,
            field_name="source_doc_ref",
        )
        if not _is_hex64(self.source_doc_sha256):
            raise ValueError("source_doc_sha256 must be lowercase sha256 hex")
        if not _is_hex64(self.source_payload_hash):
            raise ValueError("source_payload_hash must be lowercase sha256 hex")
        if self.inspection_order != list(_FROZEN_ROUTING_ORDER_BY_DOMAIN[self.domain_class]):
            raise ValueError("inspection_order must match the frozen domain-class routing order")
        if not self.advisory_only:
            raise ValueError("advisory_only must remain true in the first family")
        _assert_sorted_unique(
            self.accepted_compilation_boundary_refs,
            field_name="accepted_compilation_boundary_refs",
        )
        if self.accepted_compilation_boundary_refs != sorted(
            _FROZEN_ACCEPTED_COMPILATION_BOUNDARY_REFS
        ):
            raise ValueError(
                "accepted_compilation_boundary_refs must match the frozen acceptance boundary"
            )
        session_roles = [item.role for item in self.sessions]
        if session_roles != sorted(session_roles, key=_role_sort_key):
            raise ValueError("sessions must follow the frozen role order")
        if len(set(session_roles)) != len(session_roles):
            raise ValueError("sessions must not contain duplicate roles")
        stage_keys = [item.stage for item in self.execution_ladder]
        if stage_keys != sorted(stage_keys, key=_stage_sort_key):
            raise ValueError("execution_ladder must follow the frozen stage order")
        if len(set(stage_keys)) != len(stage_keys):
            raise ValueError("execution_ladder must not contain duplicate stages")
        role_counts = Counter(session_roles)
        stage_counts = Counter(item.stage for item in self.execution_ladder)
        expected_role_counts = {role: role_counts[role] for role in sorted(role_counts)}
        expected_stage_counts = {stage: stage_counts[stage] for stage in sorted(stage_counts)}
        if self.summary.total_sessions != len(self.sessions):
            raise ValueError("summary.total_sessions must equal len(sessions)")
        if self.summary.total_layers != len(self.execution_ladder):
            raise ValueError("summary.total_layers must equal len(execution_ladder)")
        if self.summary.counts_by_role != expected_role_counts:
            raise ValueError("summary.counts_by_role must match sessions")
        if self.summary.counts_by_stage != expected_stage_counts:
            raise ValueError("summary.counts_by_stage must match execution_ladder")
        return self


def _task_truth_condition_for_role(
    *,
    role: BrokeredAgentRole,
    payload: AdeuBrokeredReflexivePayload,
) -> BrokeredTaskTruthCondition:
    statement = f"{payload.delegation_doctrine.task_truth_condition_clause} Local role: {role}."
    authority_refs = sorted(
        {
            f"doc:{payload.source_doc_ref}",
            "payload:delegation_doctrine.epistemic_severance_clause",
            "payload:delegation_doctrine.task_truth_condition_clause",
            "payload:recursive_honesty_doctrine.recursive_honesty_axiom",
            "payload:sentinel_doctrine.socratic_limit",
            "repo:accepted_compilation_boundary",
        }
    )
    return BrokeredTaskTruthCondition(
        statement=statement,
        authority_refs=authority_refs,
        refuse_on_missing_authority=True,
        local_only=True,
    )


def _prompt_packet_for_role(
    *,
    role: BrokeredAgentRole,
    payload: AdeuBrokeredReflexivePayload,
) -> BrokeredPromptPacket:
    objective = {
        "orchestrator": (
            "Preserve payload fidelity, decompose work, and integrate bounded "
            "outputs."
        ),
        "explorer": "Map only the repo surfaces needed for the current bounded step.",
        "adversarial_reviewer": (
            "Stress-test the plan and surface payload drift, authority drift, "
            "and scope drift."
        ),
        "implementer": (
            "Implement the bounded module described by the plan without "
            "widening scope."
        ),
        "code_reviewer": (
            "Review the diff for bugs, regressions, missing tests, and payload "
            "misalignment."
        ),
        "gatekeeper": (
            "Report hard-gate outcomes and evidence posture without waiving "
            "constraints."
        ),
    }[role]
    prompt_payload = {
        "role": role,
        "objective": objective,
        "constraints": list(_FROZEN_GUARDRAILS_BY_ROLE[role]),
        "reply_contract": list(_FROZEN_REPLY_CONTRACT_BY_ROLE[role]),
        "payload_id": payload.payload_id,
    }
    return BrokeredPromptPacket(
        prompt_id=_hash16(prompt_payload),
        role=role,
        recommended_agent_model=_FROZEN_MODEL_BY_ROLE[role],
        reasoning_effort="xhigh",
        objective=objective,
        constraints=sorted(_FROZEN_GUARDRAILS_BY_ROLE[role]),
        reply_contract=sorted(_FROZEN_REPLY_CONTRACT_BY_ROLE[role]),
    )


def _session_packet_for_role(
    *,
    role: BrokeredAgentRole,
    payload: AdeuBrokeredReflexivePayload,
    plan_id: str,
) -> BrokeredSessionPacket:
    prompt_packet = _prompt_packet_for_role(role=role, payload=payload)
    local_objective = prompt_packet.objective
    session_payload = {
        "plan_id": plan_id,
        "role": role,
        "budget_posture": _FROZEN_BUDGET_BY_ROLE[role],
        "prompt_id": prompt_packet.prompt_id,
    }
    return BrokeredSessionPacket(
        session_id=_hash16(session_payload),
        role=role,
        local_objective=local_objective,
        delegation_depth_limit=_delegation_depth_limit_for_role(role=role, payload=payload),
        budget_posture=_FROZEN_BUDGET_BY_ROLE[role],
        task_truth_condition=_task_truth_condition_for_role(role=role, payload=payload),
        allowed_evidence_scope=sorted(_FROZEN_ALLOWED_EVIDENCE_BY_ROLE[role]),
        deontic_guardrails=sorted(_FROZEN_GUARDRAILS_BY_ROLE[role]),
        non_authority_statement=_FROZEN_NON_AUTHORITY_BY_ROLE[role],
        prompt_packet=prompt_packet,
    )


def _layer_for_role(
    *,
    role: BrokeredAgentRole,
    payload: AdeuBrokeredReflexivePayload,
    plan_id: str,
    inspection_order: list[BrokeredADEUDimension],
) -> BrokeredExecutionLayer:
    stage = _FROZEN_STAGE_BY_ROLE[role]
    input_refs = {
        "orchestrator": [
            f"doc:{payload.source_doc_ref}",
            f"payload:{payload.payload_id}",
            "repo:accepted_compilation_boundary",
        ],
        "explorer": [
            f"doc:{payload.source_doc_ref}",
            f"payload:{payload.payload_id}",
            "repo:codebase_and_control_plane",
        ],
        "adversarial_reviewer": [f"plan:{plan_id}", f"payload:{payload.payload_id}"],
        "implementer": [f"plan:{plan_id}", "repo:codebase_and_tests"],
        "code_reviewer": [f"plan:{plan_id}", "repo:bounded_diff_and_tests"],
        "gatekeeper": [f"plan:{plan_id}", "repo:hard_gates"],
    }[role]
    output_refs = {
        "orchestrator": [
            f"ladder:{plan_id}",
            f"route:{':'.join(inspection_order)}",
            f"sessions:{plan_id}",
        ],
        "explorer": ["context:repo_surface_map"],
        "adversarial_reviewer": ["findings:payload_drift_review"],
        "implementer": ["delta:bounded_module_changes"],
        "code_reviewer": ["findings:code_review"],
        "gatekeeper": ["gate_report:hard_checks"],
    }[role]
    success_condition = {
        "orchestrator": (
            "A bounded, advisory-only execution plan exists with explicit "
            "authority and refusal law."
        ),
        "explorer": (
            "Relevant repo surfaces are mapped without claiming authority or "
            "completion."
        ),
        "adversarial_reviewer": (
            "Payload and repo drift are surfaced as bounded findings tied to "
            "evidence."
        ),
        "implementer": (
            "The selected bounded module is implemented without widening scope "
            "or inventing authority."
        ),
        "code_reviewer": (
            "Primary risks, regressions, and missing tests are surfaced before "
            "acceptance."
        ),
        "gatekeeper": (
            "Hard-gate outcomes are reported without semantic waiver or "
            "rhetorical substitution."
        ),
    }[role]
    layer_payload = {
        "plan_id": plan_id,
        "stage": stage,
        "role": role,
        "inputs": sorted(input_refs),
        "outputs": sorted(output_refs),
    }
    return BrokeredExecutionLayer(
        layer_id=_hash16(layer_payload),
        stage=stage,
        owner_role=role,
        input_refs=sorted(input_refs),
        output_refs=sorted(output_refs),
        success_condition=success_condition,
    )


def _utility_capture_risk_rules(
    *,
    sentinel: BrokeredSentinelDoctrine,
) -> list[UtilityCaptureRiskRule]:
    rule_map = {
        "coercive_reprioritization": (
            "Detect attempts to force a utility reprioritization beyond the "
            "licensed intervention depth.",
            "Escalate and refuse utility rewrite beyond licensed depth.",
        ),
        "epistemic_suppression": (
            "Detect discourse that degrades truth-tracking to close off "
            "legitimate evidence access.",
            "Flag epistemic abuse and require evidence-bound restatement.",
        ),
        "utility_capture": (
            "Detect attempts to seize another actor's utility channel through "
            "manipulative pressure rather than truth-tracking.",
            "Mark as sentinel breach and refuse silent optimization transfer.",
        ),
        "utility_deformation": (
            "Detect advisory output that reshapes protected aims rather than "
            "serving them.",
            "Constrain output to advisory reframing or observation only.",
        ),
    }
    rules: list[UtilityCaptureRiskRule] = []
    for pressure_class in sentinel.forbidden_pressure_classes:
        detection_signal, response_posture = rule_map[pressure_class]
        payload = {
            "pressure_class": pressure_class,
            "detection_signal": detection_signal,
            "response_posture": response_posture,
        }
        rules.append(
            UtilityCaptureRiskRule(
                risk_id=_hash16(payload),
                pressure_class=pressure_class,
                detection_signal=detection_signal,
                response_posture=response_posture,
            )
        )
    return sorted(rules, key=lambda item: (item.pressure_class, item.risk_id))


def _delegation_depth_limit_for_role(
    *,
    role: BrokeredAgentRole,
    payload: AdeuBrokeredReflexivePayload,
) -> int:
    if role == "orchestrator":
        return payload.max_delegation_depth
    return max(payload.max_delegation_depth - 1, 0)


def compile_brokered_reflexive_execution_plan(
    payload: AdeuBrokeredReflexivePayload | dict[str, Any],
) -> AdeuBrokeredReflexiveExecutionPlan:
    normalized = (
        payload
        if isinstance(payload, AdeuBrokeredReflexivePayload)
        else AdeuBrokeredReflexivePayload.model_validate(payload)
    )
    canonical_payload = normalized.model_dump(mode="json", by_alias=True, exclude_none=True)
    source_payload_hash = _hash64(canonical_payload)
    inspection_order = normalized.adaptive_domain_routing.order_for(normalized.domain_class)
    plan_id = _hash16(
        {
            "payload_id": normalized.payload_id,
            "domain_class": normalized.domain_class,
            "requested_roles": normalized.requested_roles,
            "source_payload_hash": source_payload_hash,
        }
    )
    sessions = [
        _session_packet_for_role(role=role, payload=normalized, plan_id=plan_id)
        for role in normalized.requested_roles
    ]
    execution_ladder = sorted(
        [
            _layer_for_role(
                role=role,
                payload=normalized,
                plan_id=plan_id,
                inspection_order=inspection_order,
            )
            for role in normalized.requested_roles
        ]
        + [
            BrokeredExecutionLayer(
                layer_id=_hash16(
                    {
                        "plan_id": plan_id,
                        "stage": "intent_normalization",
                        "owner_role": "orchestrator",
                    }
                ),
                stage="intent_normalization",
                owner_role="orchestrator",
                input_refs=[
                    f"doc:{normalized.source_doc_ref}",
                    f"payload:{normalized.payload_id}",
                ],
                output_refs=[f"payload_normalized:{normalized.payload_id}"],
                success_condition=(
                    "The raw philosophical intent is normalized into a bounded typed payload "
                    "without widening authority."
                ),
            ),
            BrokeredExecutionLayer(
                layer_id=_hash16(
                    {
                        "plan_id": plan_id,
                        "stage": "recursive_honesty_audit",
                        "owner_role": "orchestrator",
                    }
                ),
                stage="recursive_honesty_audit",
                owner_role="orchestrator",
                input_refs=[f"plan:{plan_id}", "repo:hard_gates_and_findings"],
                output_refs=[f"recursive_honesty_report:{plan_id}"],
                success_condition=(
                    "The plan is audited against authority boundary, task truth, scope, "
                    "and licensed utility intervention."
                ),
            ),
        ],
        key=lambda item: _stage_sort_key(item.stage),
    )
    stage_counts = Counter(item.stage for item in execution_ladder)
    role_counts = Counter(item.role for item in sessions)
    return AdeuBrokeredReflexiveExecutionPlan(
        payload_id=normalized.payload_id,
        plan_id=plan_id,
        source_doc_ref=normalized.source_doc_ref,
        source_doc_sha256=normalized.source_doc_sha256,
        source_payload_hash=source_payload_hash,
        domain_class=normalized.domain_class,
        inspection_order=inspection_order,
        max_delegation_depth=normalized.max_delegation_depth,
        advisory_only=True,
        primary_execution_surface=BROKERED_REFLEXIVE_PRIMARY_EXECUTION_SURFACE,
        supporting_api_route=BROKERED_REFLEXIVE_SUPPORTING_API_ROUTE,
        accepted_compilation_boundary_refs=sorted(_FROZEN_ACCEPTED_COMPILATION_BOUNDARY_REFS),
        sessions=sessions,
        execution_ladder=execution_ladder,
        sentinel_profile=BrokeredSentinelProfile(
            protected_aims=normalized.sentinel_doctrine.protected_aims,
            forbidden_pressure_classes=normalized.sentinel_doctrine.forbidden_pressure_classes,
            permitted_intervention_depth=normalized.sentinel_doctrine.permitted_intervention_depth,
            utility_capture_risk_rules=_utility_capture_risk_rules(
                sentinel=normalized.sentinel_doctrine
            ),
        ),
        recursive_honesty_protocol=BrokeredRecursiveHonestyProtocol(
            self_audit_required=True,
            required_checks=sorted(_FROZEN_RECURSIVE_HONESTY_CHECKS),
            fail_closed_refusal_reasons=normalized.recursive_honesty_doctrine.fail_closed_refusal_reasons,
            audit_stage="recursive_honesty_audit",
        ),
        summary=BrokeredExecutionSummary(
            total_layers=len(execution_ladder),
            total_sessions=len(sessions),
            counts_by_role={role: role_counts[role] for role in sorted(role_counts)},
            counts_by_stage={stage: stage_counts[stage] for stage in sorted(stage_counts)},
        ),
    )


def canonicalize_brokered_reflexive_payload_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    normalized = AdeuBrokeredReflexivePayload.model_validate(payload)
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


def canonicalize_brokered_reflexive_execution_plan_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    normalized = AdeuBrokeredReflexiveExecutionPlan.model_validate(payload)
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)
