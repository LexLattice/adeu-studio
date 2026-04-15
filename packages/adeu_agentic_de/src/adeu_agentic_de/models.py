from __future__ import annotations

from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

AGENTIC_DE_DOMAIN_PACKET_SCHEMA = "agentic_de_domain_packet@1"
AGENTIC_DE_MORPH_IR_SCHEMA = "agentic_de_morph_ir@1"
AGENTIC_DE_INTERACTION_CONTRACT_SCHEMA = "agentic_de_interaction_contract@1"
AGENTIC_DE_ACTION_PROPOSAL_SCHEMA = "agentic_de_action_proposal@1"
AGENTIC_DE_MEMBRANE_CHECKPOINT_SCHEMA = "agentic_de_membrane_checkpoint@1"
AGENTIC_DE_MORPH_DIAGNOSTICS_SCHEMA = "agentic_de_morph_diagnostics@1"
AGENTIC_DE_CONFORMANCE_REPORT_SCHEMA = "agentic_de_conformance_report@1"
AGENTIC_DE_ACTION_CLASS_TAXONOMY_SCHEMA = "agentic_de_action_class_taxonomy@1"
AGENTIC_DE_RUNTIME_STATE_SCHEMA = "agentic_de_runtime_state@1"
AGENTIC_DE_ACTION_TICKET_SCHEMA = "agentic_de_action_ticket@1"
AGENTIC_DE_LANE_DRIFT_RECORD_SCHEMA = "agentic_de_lane_drift_record@1"
AGENTIC_DE_RUNTIME_HARVEST_RECORD_SCHEMA = "agentic_de_runtime_harvest_record@1"
AGENTIC_DE_GOVERNANCE_CALIBRATION_REGISTER_SCHEMA = (
    "agentic_de_governance_calibration_register@1"
)
AGENTIC_DE_MIGRATION_DECISION_REGISTER_SCHEMA = "agentic_de_migration_decision_register@1"
AGENTIC_DE_LOCAL_EFFECT_OBSERVATION_RECORD_SCHEMA = (
    "agentic_de_local_effect_observation_record@1"
)
AGENTIC_DE_LOCAL_EFFECT_CONFORMANCE_REPORT_SCHEMA = (
    "agentic_de_local_effect_conformance_report@1"
)
AGENTIC_DE_LOCAL_EFFECT_RESTORATION_RECORD_SCHEMA = (
    "agentic_de_local_effect_restoration_record@1"
)
AGENTIC_DE_LOCAL_EFFECT_HARDENING_REGISTER_SCHEMA = (
    "agentic_de_local_effect_hardening_register@1"
)
AGENTIC_DE_LIVE_TURN_ADMISSION_RECORD_SCHEMA = (
    "agentic_de_live_turn_admission_record@1"
)
AGENTIC_DE_LIVE_TURN_HANDOFF_RECORD_SCHEMA = "agentic_de_live_turn_handoff_record@1"
AGENTIC_DE_LIVE_TURN_REINTEGRATION_REPORT_SCHEMA = (
    "agentic_de_live_turn_reintegration_report@1"
)
AGENTIC_DE_LIVE_RESTORATION_HANDOFF_RECORD_SCHEMA = (
    "agentic_de_live_restoration_handoff_record@1"
)
AGENTIC_DE_LIVE_RESTORATION_REINTEGRATION_REPORT_SCHEMA = (
    "agentic_de_live_restoration_reintegration_report@1"
)
AGENTIC_DE_LIVE_HARNESS_HARDENING_REGISTER_SCHEMA = (
    "agentic_de_live_harness_hardening_register@1"
)

ACTION_CLASS_VOCABULARY = ("inspect", "write", "execute", "dispatch")
EXACT_ACTION_CLASS_VOCABULARY = (
    "pure_read_inspect",
    "capability_sensitive_inspect",
    "local_reversible_execute",
    "stronger_execute",
    "local_write",
    "delegated_or_external_dispatch",
)
RISK_POSTURE_VOCABULARY = ("low", "medium", "high")
CAPABILITY_POSTURE_VOCABULARY = ("read_only", "dry_run_only", "live_gate_required")
CHECKPOINT_STATUS_VOCABULARY = (
    "accepted",
    "residualized",
    "blocked",
    "escalated",
    "rejected_by_form",
)
CHECKPOINT_REASON_CODE_VOCABULARY = (
    "authority_missing",
    "insufficient_evidence",
    "proposal_malformed",
    "out_of_scope",
    "noncomparable",
    "unresolved_dependency",
    "not_evaluable_yet",
)
DIAGNOSTIC_SEVERITY_VOCABULARY = ("info", "warn", "error")
DRIFT_STATUS_VOCABULARY = ("holds", "amended", "superseded", "not_selected_anymore")
CALIBRATION_SUBJECT_KIND_VOCABULARY = ("action_class", "surface")
GOVERNANCE_DECISION_OUTCOME_VOCABULARY = (
    "keep_warning_only",
    "needs_more_evidence",
    "candidate_for_later_local_hardening",
    "not_selected_for_escalation",
)
RUNTIME_COMPATIBILITY_VOCABULARY = ("compatible", "incompatible")
REVERSIBILITY_MODE_VOCABULARY = ("not_applicable", "rollback_defined_and_testable")
WRITE_SURFACE_CATEGORY_VOCABULARY = (
    "not_applicable",
    "bounded_local_artifact",
    "family_constitution",
    "lock_doc",
    "ci_config",
    "secret_or_credential",
    "dispatch_surface",
)
TICKET_DURATION_MODE_VOCABULARY = ("single_step_local",)
LOCAL_WRITE_KIND_VOCABULARY = ("create_new", "append_only")
LOCAL_EFFECT_OBSERVATION_OUTCOME_VOCABULARY = (
    "bounded_effect_observed",
    "no_effect_observed",
    "out_of_scope_write_observed",
    "mismatched_effect_observed",
    "boundedness_verdict_failed",
)
BOUNDEDNESS_VERDICT_VOCABULARY = ("bounded", "failed")
LOCAL_EFFECT_CONFORMANCE_STATUS_VOCABULARY = ("effect_aligned", "effect_divergent")
LOCAL_EFFECT_RESTORATION_OUTCOME_VOCABULARY = (
    "restoration_effect_observed",
    "no_restoration_effect_observed",
    "restoration_out_of_scope_write_observed",
    "restoration_mismatched_effect_observed",
    "restoration_boundedness_verdict_failed",
)
LOCAL_EFFECT_RESTORATION_OPERATION_VOCABULARY = (
    "compensating_remove_create_new_artifact",
)
LIVE_TURN_ADMISSION_VERDICT_VOCABULARY = (
    "admitted",
    "absent_not_owed",
    "rejected_inadmissible",
    "stale_or_expired",
    "withheld",
    "unknown",
    "partial",
)
LIVE_TURN_FIELD_ORIGIN_TAG_VOCABULARY = (
    "current_turn_native",
    "current_turn_derived",
    "observability_only",
    "prior_artifact",
    "shaping_only",
)
LIVE_TURN_REINTEGRATION_STATUS_VOCABULARY = (
    "reintegrated",
    "blocked",
    "residualized",
    "not_evaluable_yet",
)
LIVE_RESTORATION_CONTINUATION_VERDICT_VOCABULARY = ("continued",)
LIVE_HARNESS_HARDENING_OUTCOME_VOCABULARY = (
    "keep_warning_only",
    "needs_more_evidence",
    "candidate_for_later_harness_hardening",
    "not_selected_for_escalation",
)

MODEL_CONFIG = ConfigDict(
    extra="forbid",
    frozen=True,
    populate_by_name=True,
    protected_namespaces=(),
)

ActionClass = Literal["inspect", "write", "execute", "dispatch"]
ExactActionClass = Literal[
    "pure_read_inspect",
    "capability_sensitive_inspect",
    "local_reversible_execute",
    "stronger_execute",
    "local_write",
    "delegated_or_external_dispatch",
]
SelectedLiveActionClass = Literal["local_reversible_execute", "local_write"]
RiskPosture = Literal["low", "medium", "high"]
CapabilityPosture = Literal["read_only", "dry_run_only", "live_gate_required"]
CheckpointStatus = Literal[
    "accepted",
    "residualized",
    "blocked",
    "escalated",
    "rejected_by_form",
]
CheckpointReasonCode = Literal[
    "authority_missing",
    "insufficient_evidence",
    "proposal_malformed",
    "out_of_scope",
    "noncomparable",
    "unresolved_dependency",
    "not_evaluable_yet",
]
DiagnosticSeverity = Literal["info", "warn", "error"]
ConformanceStatus = Literal["dry_run_aligned", "dry_run_divergent"]
EvaluationReadiness = Literal["ready", "not_evaluable_yet"]
DriftStatus = Literal["holds", "amended", "superseded", "not_selected_anymore"]
CalibrationSubjectKind = Literal["action_class", "surface"]
GovernanceDecisionOutcome = Literal[
    "keep_warning_only",
    "needs_more_evidence",
    "candidate_for_later_local_hardening",
    "not_selected_for_escalation",
]
RuntimeCompatibility = Literal["compatible", "incompatible"]
ReversibilityMode = Literal["not_applicable", "rollback_defined_and_testable"]
WriteSurfaceCategory = Literal[
    "not_applicable",
    "bounded_local_artifact",
    "family_constitution",
    "lock_doc",
    "ci_config",
    "secret_or_credential",
    "dispatch_surface",
]
TicketDurationMode = Literal["single_step_local"]
LocalWriteKind = Literal["create_new", "append_only"]
LocalEffectObservationOutcome = Literal[
    "bounded_effect_observed",
    "no_effect_observed",
    "out_of_scope_write_observed",
    "mismatched_effect_observed",
    "boundedness_verdict_failed",
]
BoundednessVerdict = Literal["bounded", "failed"]
LocalEffectConformanceStatus = Literal["effect_aligned", "effect_divergent"]
LocalEffectRestorationOutcome = Literal[
    "restoration_effect_observed",
    "no_restoration_effect_observed",
    "restoration_out_of_scope_write_observed",
    "restoration_mismatched_effect_observed",
    "restoration_boundedness_verdict_failed",
]
LocalEffectRestorationOperation = Literal["compensating_remove_create_new_artifact"]
LiveTurnAdmissionVerdict = Literal[
    "admitted",
    "absent_not_owed",
    "rejected_inadmissible",
    "stale_or_expired",
    "withheld",
    "unknown",
    "partial",
]
LiveTurnFieldOriginTag = Literal[
    "current_turn_native",
    "current_turn_derived",
    "observability_only",
    "prior_artifact",
    "shaping_only",
]
LiveTurnReintegrationStatus = Literal[
    "reintegrated",
    "blocked",
    "residualized",
    "not_evaluable_yet",
]
LiveRestorationContinuationVerdict = Literal["continued"]
LiveHarnessHardeningOutcome = Literal[
    "keep_warning_only",
    "needs_more_evidence",
    "candidate_for_later_harness_hardening",
    "not_selected_for_escalation",
]


def _assert_present_text(value: str, *, field_name: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{field_name} must be non-empty")
    return value.strip()


def _ordered_unique_texts(values: list[str], *, field_name: str) -> list[str]:
    seen: set[str] = set()
    ordered: list[str] = []
    for raw_value in values:
        value = _assert_present_text(raw_value, field_name=field_name)
        if value in seen:
            raise ValueError(f"{field_name} must be unique")
        seen.add(value)
        ordered.append(value)
    return ordered


def _compute_id(prefix: str, payload: dict[str, object]) -> str:
    return f"{prefix}_{sha256_canonical_json(payload)[:12]}"


def _assign_or_verify_content_addressed_id(
    *,
    value: str | None,
    field_name: str,
    prefix: str,
    payload: dict[str, object],
) -> str:
    computed_id = _compute_id(prefix, payload)
    if value is None:
        return computed_id
    normalized = _assert_present_text(value, field_name=field_name)
    if normalized != computed_id:
        raise ValueError(f"{field_name} mismatch: expected {computed_id}, got {normalized}")
    return normalized


class AgenticDeDomainPacket(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_DOMAIN_PACKET_SCHEMA] = AGENTIC_DE_DOMAIN_PACKET_SCHEMA
    packet_id: str | None = None
    lineage_source_schema: Literal["ux_domain_packet@1"] = "ux_domain_packet@1"
    task_scope_ref: str
    task_scope_summary: str
    authority_frame_ref: str
    risk_posture: RiskPosture
    capability_posture: CapabilityPosture
    environment_identity: str

    @model_validator(mode="after")
    def _validate_packet(self) -> AgenticDeDomainPacket:
        _assert_present_text(self.task_scope_ref, field_name="task_scope_ref")
        _assert_present_text(self.task_scope_summary, field_name="task_scope_summary")
        _assert_present_text(self.authority_frame_ref, field_name="authority_frame_ref")
        _assert_present_text(self.environment_identity, field_name="environment_identity")
        object.__setattr__(
            self,
            "packet_id",
            _assign_or_verify_content_addressed_id(
                value=self.packet_id,
                field_name="packet_id",
                prefix="agentic_de_domain_packet",
                payload=self.model_dump(mode="json", exclude={"packet_id"}),
            ),
        )
        return self


class AgenticDeMorphIr(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_MORPH_IR_SCHEMA] = AGENTIC_DE_MORPH_IR_SCHEMA
    morph_ir_id: str | None = None
    lineage_source_schema: Literal["ux_morph_ir@1"] = "ux_morph_ir@1"
    domain_packet_ref: str
    semantic_frame_summary: str
    evaluation_readiness: EvaluationReadiness
    deontic_guards: list[str]
    evidence_expectations: list[str]
    utility_posture: list[str]

    @model_validator(mode="after")
    def _validate_morph_ir(self) -> AgenticDeMorphIr:
        _assert_present_text(self.domain_packet_ref, field_name="domain_packet_ref")
        _assert_present_text(self.semantic_frame_summary, field_name="semantic_frame_summary")
        object.__setattr__(
            self,
            "deontic_guards",
            _ordered_unique_texts(self.deontic_guards, field_name="deontic_guards"),
        )
        object.__setattr__(
            self,
            "evidence_expectations",
            _ordered_unique_texts(
                self.evidence_expectations,
                field_name="evidence_expectations",
            ),
        )
        object.__setattr__(
            self,
            "utility_posture",
            _ordered_unique_texts(self.utility_posture, field_name="utility_posture"),
        )
        object.__setattr__(
            self,
            "morph_ir_id",
            _assign_or_verify_content_addressed_id(
                value=self.morph_ir_id,
                field_name="morph_ir_id",
                prefix="agentic_de_morph_ir",
                payload=self.model_dump(mode="json", exclude={"morph_ir_id"}),
            ),
        )
        return self


class AgenticDeInteractionContractEntry(BaseModel):
    model_config = MODEL_CONFIG

    action_id: str
    action_class: ActionClass
    evidence_required: bool
    authority_required: bool
    live_effect_permitted: Literal[False] = False
    consequence_visibility: str

    @model_validator(mode="after")
    def _validate_entry(self) -> AgenticDeInteractionContractEntry:
        _assert_present_text(self.action_id, field_name="action_id")
        _assert_present_text(self.consequence_visibility, field_name="consequence_visibility")
        return self


class AgenticDeInteractionContract(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_INTERACTION_CONTRACT_SCHEMA] = AGENTIC_DE_INTERACTION_CONTRACT_SCHEMA
    contract_id: str | None = None
    lineage_source_schema: Literal["ux_interaction_contract@1"] = "ux_interaction_contract@1"
    domain_packet_ref: str
    morph_ir_ref: str
    advisory_until_governed_gate: Literal[True] = True
    no_hidden_write_execute_or_dispatch_boundary: Literal[True] = True
    interactions: list[AgenticDeInteractionContractEntry]

    @model_validator(mode="after")
    def _validate_contract(self) -> AgenticDeInteractionContract:
        _assert_present_text(self.domain_packet_ref, field_name="domain_packet_ref")
        _assert_present_text(self.morph_ir_ref, field_name="morph_ir_ref")
        if not self.interactions:
            raise ValueError("interactions must be non-empty")
        seen: set[str] = set()
        for entry in self.interactions:
            if entry.action_id in seen:
                raise ValueError("interaction action_id values must be unique")
            seen.add(entry.action_id)
        object.__setattr__(
            self,
            "contract_id",
            _assign_or_verify_content_addressed_id(
                value=self.contract_id,
                field_name="contract_id",
                prefix="agentic_de_interaction_contract",
                payload=self.model_dump(mode="json", exclude={"contract_id"}),
            ),
        )
        return self


class AgenticDeActionProposal(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_ACTION_PROPOSAL_SCHEMA] = AGENTIC_DE_ACTION_PROPOSAL_SCHEMA
    proposal_id: str | None = None
    domain_packet_ref: str
    contract_ref: str
    action_id: str
    action_class: ActionClass
    claimed_basis_summary: str
    authority_basis_refs: list[str] = Field(default_factory=list)
    evidence_refs: list[str] = Field(default_factory=list)
    requested_effect_summary: str
    entitlement_posture: Literal["non_entitling_candidate"] = "non_entitling_candidate"

    @model_validator(mode="after")
    def _validate_proposal(self) -> AgenticDeActionProposal:
        _assert_present_text(self.domain_packet_ref, field_name="domain_packet_ref")
        _assert_present_text(self.contract_ref, field_name="contract_ref")
        _assert_present_text(self.action_id, field_name="action_id")
        _assert_present_text(self.claimed_basis_summary, field_name="claimed_basis_summary")
        _assert_present_text(self.requested_effect_summary, field_name="requested_effect_summary")
        object.__setattr__(
            self,
            "authority_basis_refs",
            (
                _ordered_unique_texts(
                    self.authority_basis_refs,
                    field_name="authority_basis_refs",
                )
                if self.authority_basis_refs
                else []
            ),
        )
        object.__setattr__(
            self,
            "evidence_refs",
            (
                _ordered_unique_texts(
                    self.evidence_refs,
                    field_name="evidence_refs",
                )
                if self.evidence_refs
                else []
            ),
        )
        object.__setattr__(
            self,
            "proposal_id",
            _assign_or_verify_content_addressed_id(
                value=self.proposal_id,
                field_name="proposal_id",
                prefix="agentic_de_action_proposal",
                payload=self.model_dump(mode="json", exclude={"proposal_id"}),
            ),
        )
        return self


class AgenticDeMembraneCheckpoint(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_MEMBRANE_CHECKPOINT_SCHEMA] = AGENTIC_DE_MEMBRANE_CHECKPOINT_SCHEMA
    checkpoint_id: str | None = None
    domain_packet_ref: str
    contract_ref: str
    proposal_ref: str
    status: CheckpointStatus
    reason_code: CheckpointReasonCode | None = None
    status_explanation: str
    dry_run_only: Literal[True] = True
    action_ticket_issuable: Literal[False] = False
    live_effect_authorized: Literal[False] = False

    @model_validator(mode="after")
    def _validate_checkpoint(self) -> AgenticDeMembraneCheckpoint:
        _assert_present_text(self.domain_packet_ref, field_name="domain_packet_ref")
        _assert_present_text(self.contract_ref, field_name="contract_ref")
        _assert_present_text(self.proposal_ref, field_name="proposal_ref")
        _assert_present_text(self.status_explanation, field_name="status_explanation")
        if self.status == "accepted" and self.reason_code is not None:
            raise ValueError("accepted checkpoints may not carry a reason_code")
        if self.status != "accepted" and self.reason_code is None:
            raise ValueError("non-accepted checkpoints must carry a reason_code")
        object.__setattr__(
            self,
            "checkpoint_id",
            _assign_or_verify_content_addressed_id(
                value=self.checkpoint_id,
                field_name="checkpoint_id",
                prefix="agentic_de_membrane_checkpoint",
                payload=self.model_dump(mode="json", exclude={"checkpoint_id"}),
            ),
        )
        return self


class AgenticDeMorphDiagnosticFinding(BaseModel):
    model_config = MODEL_CONFIG

    finding_id: str | None = None
    severity: DiagnosticSeverity
    code: str
    subject_ref: str
    message: str

    @model_validator(mode="after")
    def _validate_finding(self) -> AgenticDeMorphDiagnosticFinding:
        _assert_present_text(self.code, field_name="code")
        _assert_present_text(self.subject_ref, field_name="subject_ref")
        _assert_present_text(self.message, field_name="message")
        object.__setattr__(
            self,
            "finding_id",
            _assign_or_verify_content_addressed_id(
                value=self.finding_id,
                field_name="finding_id",
                prefix="agentic_de_morph_diagnostic_finding",
                payload=self.model_dump(mode="json", exclude={"finding_id"}),
            ),
        )
        return self


class AgenticDeMorphDiagnostics(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_MORPH_DIAGNOSTICS_SCHEMA] = AGENTIC_DE_MORPH_DIAGNOSTICS_SCHEMA
    diagnostics_id: str | None = None
    packet_ref: str
    proposal_ref: str
    checkpoint_ref: str
    finding_count: int
    findings: list[AgenticDeMorphDiagnosticFinding]

    @model_validator(mode="after")
    def _validate_diagnostics(self) -> AgenticDeMorphDiagnostics:
        _assert_present_text(self.packet_ref, field_name="packet_ref")
        _assert_present_text(self.proposal_ref, field_name="proposal_ref")
        _assert_present_text(self.checkpoint_ref, field_name="checkpoint_ref")
        if self.finding_count != len(self.findings):
            raise ValueError("finding_count must equal len(findings)")
        object.__setattr__(
            self,
            "diagnostics_id",
            _assign_or_verify_content_addressed_id(
                value=self.diagnostics_id,
                field_name="diagnostics_id",
                prefix="agentic_de_morph_diagnostics",
                payload=self.model_dump(mode="json", exclude={"diagnostics_id"}),
            ),
        )
        return self


class AgenticDeConformanceReport(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_CONFORMANCE_REPORT_SCHEMA] = AGENTIC_DE_CONFORMANCE_REPORT_SCHEMA
    report_id: str | None = None
    packet_ref: str
    proposal_ref: str
    checkpoint_ref: str
    packed_state_summary: str
    proposed_action_summary: str
    checkpoint_entitlement_summary: str
    executed_or_observed_effect: Literal["no_live_effect"] = "no_live_effect"
    live_effect_present: Literal[False] = False
    conformance_status: ConformanceStatus
    delta_notes: list[str]

    @model_validator(mode="after")
    def _validate_report(self) -> AgenticDeConformanceReport:
        _assert_present_text(self.packet_ref, field_name="packet_ref")
        _assert_present_text(self.proposal_ref, field_name="proposal_ref")
        _assert_present_text(self.checkpoint_ref, field_name="checkpoint_ref")
        _assert_present_text(self.packed_state_summary, field_name="packed_state_summary")
        _assert_present_text(self.proposed_action_summary, field_name="proposed_action_summary")
        _assert_present_text(
            self.checkpoint_entitlement_summary,
            field_name="checkpoint_entitlement_summary",
        )
        object.__setattr__(
            self,
            "delta_notes",
            _ordered_unique_texts(self.delta_notes, field_name="delta_notes"),
        )
        object.__setattr__(
            self,
            "report_id",
            _assign_or_verify_content_addressed_id(
                value=self.report_id,
                field_name="report_id",
                prefix="agentic_de_conformance_report",
                payload=self.model_dump(mode="json", exclude={"report_id"}),
            ),
        )
        return self


class AgenticDeActionClassTaxonomyEntry(BaseModel):
    model_config = MODEL_CONFIG

    action_id: str
    base_action_class: ActionClass
    exact_action_class: ExactActionClass
    effect_scope_summary: str
    reversibility_mode: ReversibilityMode
    write_surface_category: WriteSurfaceCategory
    live_selected_in_v56b: bool

    @model_validator(mode="after")
    def _validate_entry(self) -> AgenticDeActionClassTaxonomyEntry:
        _assert_present_text(self.action_id, field_name="action_id")
        _assert_present_text(self.effect_scope_summary, field_name="effect_scope_summary")
        expected_base_action_class = {
            "pure_read_inspect": "inspect",
            "capability_sensitive_inspect": "inspect",
            "local_reversible_execute": "execute",
            "stronger_execute": "execute",
            "local_write": "write",
            "delegated_or_external_dispatch": "dispatch",
        }[self.exact_action_class]
        if self.base_action_class != expected_base_action_class:
            raise ValueError("base_action_class must match exact_action_class family mapping")
        if self.exact_action_class == "local_reversible_execute":
            if self.reversibility_mode != "rollback_defined_and_testable":
                raise ValueError("local_reversible_execute requires rollback_defined_and_testable")
            if self.write_surface_category != "not_applicable":
                raise ValueError(
                    "local_reversible_execute may not declare a write_surface_category"
                )
        elif self.exact_action_class == "local_write":
            if self.reversibility_mode != "not_applicable":
                raise ValueError("local_write may not declare a reversibility mode")
            if self.write_surface_category != "bounded_local_artifact":
                raise ValueError("local_write must remain bounded_local_artifact in V56-B")
        elif self.exact_action_class == "delegated_or_external_dispatch":
            if self.reversibility_mode != "not_applicable":
                raise ValueError(
                    "delegated_or_external_dispatch may not declare a reversibility mode"
                )
            if self.write_surface_category != "dispatch_surface":
                raise ValueError("delegated_or_external_dispatch must declare dispatch_surface")
            if self.live_selected_in_v56b:
                raise ValueError("delegated_or_external_dispatch may not be live-selected in V56-B")
        else:
            if self.reversibility_mode != "not_applicable":
                raise ValueError(
                    "non-local-reversible classes must use not_applicable reversibility"
                )
            if self.write_surface_category != "not_applicable":
                raise ValueError(
                    "non-write dispatch classes must use not_applicable write surface category"
                )
        if self.exact_action_class not in {"local_reversible_execute", "local_write"}:
            if self.live_selected_in_v56b:
                raise ValueError(
                    "only local_reversible_execute and local_write may be live-selected in V56-B"
                )
        return self


class AgenticDeActionClassTaxonomy(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_ACTION_CLASS_TAXONOMY_SCHEMA] = (
        AGENTIC_DE_ACTION_CLASS_TAXONOMY_SCHEMA
    )
    taxonomy_id: str | None = None
    contract_ref: str
    entry_count: int
    entries: list[AgenticDeActionClassTaxonomyEntry]

    @model_validator(mode="after")
    def _validate_taxonomy(self) -> AgenticDeActionClassTaxonomy:
        _assert_present_text(self.contract_ref, field_name="contract_ref")
        if self.entry_count != len(self.entries):
            raise ValueError("entry_count must equal len(entries)")
        seen_action_ids: set[str] = set()
        live_selected: set[str] = set()
        for entry in self.entries:
            if entry.action_id in seen_action_ids:
                raise ValueError("taxonomy action_id values must be unique")
            seen_action_ids.add(entry.action_id)
            if entry.live_selected_in_v56b:
                live_selected.add(entry.exact_action_class)
        if not live_selected:
            raise ValueError("taxonomy must select at least one live action class for V56-B")
        object.__setattr__(
            self,
            "taxonomy_id",
            _assign_or_verify_content_addressed_id(
                value=self.taxonomy_id,
                field_name="taxonomy_id",
                prefix="agentic_de_action_class_taxonomy",
                payload=self.model_dump(mode="json", exclude={"taxonomy_id"}),
            ),
        )
        return self


class AgenticDeRuntimeState(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_RUNTIME_STATE_SCHEMA] = AGENTIC_DE_RUNTIME_STATE_SCHEMA
    state_id: str | None = None
    domain_packet_ref: str
    contract_ref: str
    checkpoint_ref: str
    authority_frame_ref: str
    issuance_capability_posture: Literal["live_gate_required"] = "live_gate_required"
    selected_live_action_classes: list[SelectedLiveActionClass]
    compatibility_status: RuntimeCompatibility
    compatibility_note: str
    local_scope_summary: str
    ticket_duration_mode: TicketDurationMode = "single_step_local"
    ticket_scope_summary: str

    @model_validator(mode="after")
    def _validate_runtime_state(self) -> AgenticDeRuntimeState:
        _assert_present_text(self.domain_packet_ref, field_name="domain_packet_ref")
        _assert_present_text(self.contract_ref, field_name="contract_ref")
        _assert_present_text(self.checkpoint_ref, field_name="checkpoint_ref")
        _assert_present_text(self.authority_frame_ref, field_name="authority_frame_ref")
        _assert_present_text(self.compatibility_note, field_name="compatibility_note")
        _assert_present_text(self.local_scope_summary, field_name="local_scope_summary")
        _assert_present_text(self.ticket_scope_summary, field_name="ticket_scope_summary")
        if not self.selected_live_action_classes:
            raise ValueError("selected_live_action_classes must be non-empty")
        if len(set(self.selected_live_action_classes)) != len(self.selected_live_action_classes):
            raise ValueError("selected_live_action_classes must be unique")
        object.__setattr__(
            self,
            "state_id",
            _assign_or_verify_content_addressed_id(
                value=self.state_id,
                field_name="state_id",
                prefix="agentic_de_runtime_state",
                payload=self.model_dump(mode="json", exclude={"state_id"}),
            ),
        )
        return self


class AgenticDeActionTicket(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_ACTION_TICKET_SCHEMA] = AGENTIC_DE_ACTION_TICKET_SCHEMA
    ticket_id: str | None = None
    domain_packet_ref: str
    contract_ref: str
    proposal_ref: str
    checkpoint_ref: str
    runtime_state_ref: str
    taxonomy_ref: str
    exact_action_class: SelectedLiveActionClass
    authority_frame_ref: str
    ticket_scope_summary: str
    ticket_duration_mode: TicketDurationMode = "single_step_local"
    live_effect_authorized: Literal[True] = True

    @model_validator(mode="after")
    def _validate_ticket(self) -> AgenticDeActionTicket:
        _assert_present_text(self.domain_packet_ref, field_name="domain_packet_ref")
        _assert_present_text(self.contract_ref, field_name="contract_ref")
        _assert_present_text(self.proposal_ref, field_name="proposal_ref")
        _assert_present_text(self.checkpoint_ref, field_name="checkpoint_ref")
        _assert_present_text(self.runtime_state_ref, field_name="runtime_state_ref")
        _assert_present_text(self.taxonomy_ref, field_name="taxonomy_ref")
        _assert_present_text(self.authority_frame_ref, field_name="authority_frame_ref")
        _assert_present_text(self.ticket_scope_summary, field_name="ticket_scope_summary")
        object.__setattr__(
            self,
            "ticket_id",
            _assign_or_verify_content_addressed_id(
                value=self.ticket_id,
                field_name="ticket_id",
                prefix="agentic_de_action_ticket",
                payload=self.model_dump(mode="json", exclude={"ticket_id"}),
            ),
        )
        return self


class AgenticDeLaneDriftEntry(BaseModel):
    model_config = MODEL_CONFIG

    assumption_ref: str
    status: DriftStatus
    note: str

    @model_validator(mode="after")
    def _validate_entry(self) -> AgenticDeLaneDriftEntry:
        _assert_present_text(self.assumption_ref, field_name="assumption_ref")
        _assert_present_text(self.note, field_name="note")
        return self


class AgenticDeLaneDriftRecord(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_LANE_DRIFT_RECORD_SCHEMA] = AGENTIC_DE_LANE_DRIFT_RECORD_SCHEMA
    record_id: str | None = None
    target_arc: str
    target_path: str
    prior_lane_ref: str
    entry_count: int
    entries: list[AgenticDeLaneDriftEntry]

    @model_validator(mode="after")
    def _validate_record(self) -> AgenticDeLaneDriftRecord:
        _assert_present_text(self.target_arc, field_name="target_arc")
        _assert_present_text(self.target_path, field_name="target_path")
        _assert_present_text(self.prior_lane_ref, field_name="prior_lane_ref")
        if self.entry_count != len(self.entries):
            raise ValueError("entry_count must equal len(entries)")
        seen: set[str] = set()
        for entry in self.entries:
            if entry.assumption_ref in seen:
                raise ValueError("lane drift assumption_ref values must be unique")
            seen.add(entry.assumption_ref)
        object.__setattr__(
            self,
            "record_id",
            _assign_or_verify_content_addressed_id(
                value=self.record_id,
                field_name="record_id",
                prefix="agentic_de_lane_drift",
                payload=self.model_dump(mode="json", exclude={"record_id"}),
            ),
        )
        return self


class AgenticDeRuntimeHarvestRecord(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_RUNTIME_HARVEST_RECORD_SCHEMA] = (
        AGENTIC_DE_RUNTIME_HARVEST_RECORD_SCHEMA
    )
    harvest_id: str | None = None
    target_arc: str
    target_path: str
    observation_only: Literal[True] = True
    governance_classification_deferred: Literal[True] = True
    baseline_checker_version: str
    packet_ref: str
    proposal_ref: str
    checkpoint_ref: str
    runtime_state_ref: str
    ticket_ref: str | None = None
    diagnostics_ref: str
    conformance_ref: str
    selected_live_action_classes: list[SelectedLiveActionClass]
    selected_live_action_class_interpretation_frozen: Literal[True] = True
    packed_state_summary: str
    proposed_action_summary: str
    checkpoint_entitlement_summary: str
    ticket_issued: bool
    ticket_visibility_summary: str
    executed_or_observed_effect: str
    live_effect_present: bool
    observed_pattern_summary: str
    delta_notes: list[str]
    bounded_derived_summaries: list[str]
    evidence_refs: list[str]

    @model_validator(mode="after")
    def _validate_record(self) -> AgenticDeRuntimeHarvestRecord:
        _assert_present_text(self.target_arc, field_name="target_arc")
        _assert_present_text(self.target_path, field_name="target_path")
        _assert_present_text(
            self.baseline_checker_version,
            field_name="baseline_checker_version",
        )
        _assert_present_text(self.packet_ref, field_name="packet_ref")
        _assert_present_text(self.proposal_ref, field_name="proposal_ref")
        _assert_present_text(self.checkpoint_ref, field_name="checkpoint_ref")
        _assert_present_text(self.runtime_state_ref, field_name="runtime_state_ref")
        _assert_present_text(self.diagnostics_ref, field_name="diagnostics_ref")
        _assert_present_text(self.conformance_ref, field_name="conformance_ref")
        _assert_present_text(self.packed_state_summary, field_name="packed_state_summary")
        _assert_present_text(self.proposed_action_summary, field_name="proposed_action_summary")
        _assert_present_text(
            self.checkpoint_entitlement_summary,
            field_name="checkpoint_entitlement_summary",
        )
        _assert_present_text(
            self.ticket_visibility_summary,
            field_name="ticket_visibility_summary",
        )
        _assert_present_text(
            self.executed_or_observed_effect,
            field_name="executed_or_observed_effect",
        )
        _assert_present_text(
            self.observed_pattern_summary,
            field_name="observed_pattern_summary",
        )
        if self.observation_only is not True:
            raise ValueError("observation_only must remain true in V56-C")
        if self.governance_classification_deferred is not True:
            raise ValueError("governance_classification_deferred must remain true in V56-C")
        if self.selected_live_action_class_interpretation_frozen is not True:
            raise ValueError(
                "selected_live_action_class_interpretation_frozen must remain true in V56-C"
            )
        if not self.selected_live_action_classes:
            raise ValueError("selected_live_action_classes must be non-empty")
        if len(set(self.selected_live_action_classes)) != len(self.selected_live_action_classes):
            raise ValueError("selected_live_action_classes must be unique")
        object.__setattr__(
            self,
            "delta_notes",
            _ordered_unique_texts(self.delta_notes, field_name="delta_notes"),
        )
        object.__setattr__(
            self,
            "bounded_derived_summaries",
            _ordered_unique_texts(
                self.bounded_derived_summaries,
                field_name="bounded_derived_summaries",
            ),
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _ordered_unique_texts(self.evidence_refs, field_name="evidence_refs"),
        )
        if self.ticket_issued and self.ticket_ref is None:
            raise ValueError("ticket_ref required when ticket_issued is true")
        if not self.ticket_issued and self.ticket_ref is not None:
            raise ValueError("ticket_ref must be omitted when ticket_issued is false")
        if self.ticket_ref is not None:
            _assert_present_text(self.ticket_ref, field_name="ticket_ref")
        object.__setattr__(
            self,
            "harvest_id",
            _assign_or_verify_content_addressed_id(
                value=self.harvest_id,
                field_name="harvest_id",
                prefix="agentic_de_runtime_harvest",
                payload=self.model_dump(mode="json", exclude={"harvest_id"}),
            ),
        )
        return self


class AgenticDeGovernanceCalibrationEntry(BaseModel):
    model_config = MODEL_CONFIG

    calibration_id: str | None = None
    subject_kind: CalibrationSubjectKind
    subject_ref: str
    current_posture: str
    recommended_outcome: GovernanceDecisionOutcome
    rationale: str
    evidence_refs: list[str]

    @model_validator(mode="after")
    def _validate_entry(self) -> AgenticDeGovernanceCalibrationEntry:
        _assert_present_text(self.subject_ref, field_name="subject_ref")
        _assert_present_text(self.current_posture, field_name="current_posture")
        _assert_present_text(self.rationale, field_name="rationale")
        object.__setattr__(
            self,
            "evidence_refs",
            _ordered_unique_texts(self.evidence_refs, field_name="evidence_refs"),
        )
        object.__setattr__(
            self,
            "calibration_id",
            _assign_or_verify_content_addressed_id(
                value=self.calibration_id,
                field_name="calibration_id",
                prefix="agentic_de_governance_calibration",
                payload=self.model_dump(mode="json", exclude={"calibration_id"}),
            ),
        )
        return self


class AgenticDeGovernanceCalibrationRegister(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_GOVERNANCE_CALIBRATION_REGISTER_SCHEMA] = (
        AGENTIC_DE_GOVERNANCE_CALIBRATION_REGISTER_SCHEMA
    )
    register_id: str | None = None
    target_arc: str
    target_path: str
    advisory_only: Literal[True] = True
    changes_live_behavior_by_default: Literal[False] = False
    baseline_checker_version: str
    entry_count: int
    entries: list[AgenticDeGovernanceCalibrationEntry]

    @model_validator(mode="after")
    def _validate_register(self) -> AgenticDeGovernanceCalibrationRegister:
        _assert_present_text(self.target_arc, field_name="target_arc")
        _assert_present_text(self.target_path, field_name="target_path")
        _assert_present_text(
            self.baseline_checker_version,
            field_name="baseline_checker_version",
        )
        if self.advisory_only is not True:
            raise ValueError("advisory_only must remain true in V56-C")
        if self.changes_live_behavior_by_default is not False:
            raise ValueError("changes_live_behavior_by_default must remain false in V56-C")
        if self.entry_count != len(self.entries):
            raise ValueError("entry_count must equal len(entries)")
        object.__setattr__(
            self,
            "register_id",
            _assign_or_verify_content_addressed_id(
                value=self.register_id,
                field_name="register_id",
                prefix="agentic_de_governance_calibration_register",
                payload=self.model_dump(mode="json", exclude={"register_id"}),
            ),
        )
        return self


class AgenticDeMigrationDecisionEntry(BaseModel):
    model_config = MODEL_CONFIG

    decision_id: str | None = None
    surface_id: str
    current_posture: str
    recommended_outcome: GovernanceDecisionOutcome
    rationale: str
    evidence_refs: list[str]

    @model_validator(mode="after")
    def _validate_entry(self) -> AgenticDeMigrationDecisionEntry:
        _assert_present_text(self.surface_id, field_name="surface_id")
        _assert_present_text(self.current_posture, field_name="current_posture")
        _assert_present_text(self.rationale, field_name="rationale")
        object.__setattr__(
            self,
            "evidence_refs",
            _ordered_unique_texts(self.evidence_refs, field_name="evidence_refs"),
        )
        object.__setattr__(
            self,
            "decision_id",
            _assign_or_verify_content_addressed_id(
                value=self.decision_id,
                field_name="decision_id",
                prefix="agentic_de_migration_decision",
                payload=self.model_dump(mode="json", exclude={"decision_id"}),
            ),
        )
        return self


class AgenticDeMigrationDecisionRegister(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_MIGRATION_DECISION_REGISTER_SCHEMA] = (
        AGENTIC_DE_MIGRATION_DECISION_REGISTER_SCHEMA
    )
    register_id: str | None = None
    target_arc: str
    target_path: str
    advisory_only: Literal[True] = True
    candidate_only: Literal[True] = True
    changes_live_behavior_by_default: Literal[False] = False
    baseline_checker_version: str
    entry_count: int
    entries: list[AgenticDeMigrationDecisionEntry]

    @model_validator(mode="after")
    def _validate_register(self) -> AgenticDeMigrationDecisionRegister:
        _assert_present_text(self.target_arc, field_name="target_arc")
        _assert_present_text(self.target_path, field_name="target_path")
        _assert_present_text(
            self.baseline_checker_version,
            field_name="baseline_checker_version",
        )
        if self.advisory_only is not True:
            raise ValueError("advisory_only must remain true in V56-C")
        if self.candidate_only is not True:
            raise ValueError("candidate_only must remain true in V56-C")
        if self.changes_live_behavior_by_default is not False:
            raise ValueError("changes_live_behavior_by_default must remain false in V56-C")
        if self.entry_count != len(self.entries):
            raise ValueError("entry_count must equal len(entries)")
        object.__setattr__(
            self,
            "register_id",
            _assign_or_verify_content_addressed_id(
                value=self.register_id,
                field_name="register_id",
                prefix="agentic_de_migration_decision_register",
                payload=self.model_dump(mode="json", exclude={"register_id"}),
            ),
        )
        return self


class AgenticDeObservedWriteEntry(BaseModel):
    model_config = MODEL_CONFIG

    relative_path: str
    write_kind: LocalWriteKind
    existed_before: bool
    bytes_written: int = Field(ge=0)
    content_sha256: str

    @model_validator(mode="after")
    def _validate_entry(self) -> AgenticDeObservedWriteEntry:
        _assert_present_text(self.relative_path, field_name="relative_path")
        _assert_present_text(self.content_sha256, field_name="content_sha256")
        return self


class AgenticDeLocalEffectObservationRecord(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_LOCAL_EFFECT_OBSERVATION_RECORD_SCHEMA] = (
        AGENTIC_DE_LOCAL_EFFECT_OBSERVATION_RECORD_SCHEMA
    )
    observation_id: str | None = None
    target_arc: str
    target_path: str
    evidence_only: Literal[True] = True
    changes_live_behavior_by_default: Literal[False] = False
    selected_live_action_class: Literal["local_write"] = "local_write"
    selected_local_write_kind: LocalWriteKind
    designated_sandbox_root: str
    packet_ref: str
    action_proposal_ref: str
    checkpoint_ref: str
    runtime_state_ref: str
    ticket_ref: str
    harvest_ref: str
    pre_state_ref: str
    observed_write_set: list[AgenticDeObservedWriteEntry]
    post_state_ref: str
    observed_effect: str
    observation_outcome: LocalEffectObservationOutcome
    boundedness_verdict: BoundednessVerdict
    boundedness_note: str
    evidence_refs: list[str]

    @model_validator(mode="after")
    def _validate_record(self) -> AgenticDeLocalEffectObservationRecord:
        _assert_present_text(self.target_arc, field_name="target_arc")
        _assert_present_text(self.target_path, field_name="target_path")
        _assert_present_text(
            self.designated_sandbox_root,
            field_name="designated_sandbox_root",
        )
        _assert_present_text(self.packet_ref, field_name="packet_ref")
        _assert_present_text(self.action_proposal_ref, field_name="action_proposal_ref")
        _assert_present_text(self.checkpoint_ref, field_name="checkpoint_ref")
        _assert_present_text(self.runtime_state_ref, field_name="runtime_state_ref")
        _assert_present_text(self.ticket_ref, field_name="ticket_ref")
        _assert_present_text(self.harvest_ref, field_name="harvest_ref")
        _assert_present_text(self.pre_state_ref, field_name="pre_state_ref")
        _assert_present_text(self.post_state_ref, field_name="post_state_ref")
        _assert_present_text(self.observed_effect, field_name="observed_effect")
        _assert_present_text(self.boundedness_note, field_name="boundedness_note")
        object.__setattr__(
            self,
            "evidence_refs",
            _ordered_unique_texts(self.evidence_refs, field_name="evidence_refs"),
        )
        observed_paths = [entry.relative_path for entry in self.observed_write_set]
        if len(set(observed_paths)) != len(observed_paths):
            raise ValueError("observed_write_set relative_path values must be unique")
        if self.observation_outcome == "bounded_effect_observed":
            if not self.observed_write_set:
                raise ValueError("bounded_effect_observed requires an observed_write_set")
            if self.boundedness_verdict != "bounded":
                raise ValueError("bounded_effect_observed requires bounded verdict")
        elif self.observation_outcome == "no_effect_observed":
            if self.observed_write_set:
                raise ValueError("no_effect_observed may not carry observed writes")
            if self.boundedness_verdict != "bounded":
                raise ValueError("no_effect_observed requires bounded verdict")
        elif self.observation_outcome == "out_of_scope_write_observed":
            if not self.observed_write_set:
                raise ValueError("out_of_scope_write_observed requires observed writes")
            if self.boundedness_verdict != "failed":
                raise ValueError("out_of_scope_write_observed requires failed verdict")
        elif self.observation_outcome == "mismatched_effect_observed":
            if not self.observed_write_set:
                raise ValueError("mismatched_effect_observed requires observed writes")
            if self.boundedness_verdict != "bounded":
                raise ValueError("mismatched_effect_observed requires bounded verdict")
        elif self.boundedness_verdict != "failed":
            raise ValueError("boundedness_verdict_failed requires failed verdict")
        object.__setattr__(
            self,
            "observation_id",
            _assign_or_verify_content_addressed_id(
                value=self.observation_id,
                field_name="observation_id",
                prefix="agentic_de_local_effect_observation",
                payload=self.model_dump(mode="json", exclude={"observation_id"}),
            ),
        )
        return self


class AgenticDeLocalEffectConformanceReport(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_LOCAL_EFFECT_CONFORMANCE_REPORT_SCHEMA] = (
        AGENTIC_DE_LOCAL_EFFECT_CONFORMANCE_REPORT_SCHEMA
    )
    report_id: str | None = None
    target_arc: str
    target_path: str
    evidence_only: Literal[True] = True
    changes_live_behavior_by_default: Literal[False] = False
    packet_ref: str
    action_proposal_ref: str
    checkpoint_ref: str
    runtime_state_ref: str
    ticket_ref: str
    harvest_ref: str
    observation_ref: str
    packed_state_summary: str
    proposed_action_summary: str
    checkpoint_entitlement_summary: str
    ticket_visibility_summary: str
    observed_effect: str
    observation_outcome: LocalEffectObservationOutcome
    live_effect_present: bool
    boundedness_verdict: BoundednessVerdict
    conformance_status: LocalEffectConformanceStatus
    delta_notes: list[str]
    evidence_refs: list[str]

    @model_validator(mode="after")
    def _validate_report(self) -> AgenticDeLocalEffectConformanceReport:
        _assert_present_text(self.target_arc, field_name="target_arc")
        _assert_present_text(self.target_path, field_name="target_path")
        _assert_present_text(self.packet_ref, field_name="packet_ref")
        _assert_present_text(self.action_proposal_ref, field_name="action_proposal_ref")
        _assert_present_text(self.checkpoint_ref, field_name="checkpoint_ref")
        _assert_present_text(self.runtime_state_ref, field_name="runtime_state_ref")
        _assert_present_text(self.ticket_ref, field_name="ticket_ref")
        _assert_present_text(self.harvest_ref, field_name="harvest_ref")
        _assert_present_text(self.observation_ref, field_name="observation_ref")
        _assert_present_text(self.packed_state_summary, field_name="packed_state_summary")
        _assert_present_text(self.proposed_action_summary, field_name="proposed_action_summary")
        _assert_present_text(
            self.checkpoint_entitlement_summary,
            field_name="checkpoint_entitlement_summary",
        )
        _assert_present_text(
            self.ticket_visibility_summary,
            field_name="ticket_visibility_summary",
        )
        _assert_present_text(self.observed_effect, field_name="observed_effect")
        object.__setattr__(
            self,
            "delta_notes",
            _ordered_unique_texts(self.delta_notes, field_name="delta_notes"),
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _ordered_unique_texts(self.evidence_refs, field_name="evidence_refs"),
        )
        expected_live_effect_present = self.observation_outcome != "no_effect_observed"
        if self.live_effect_present != expected_live_effect_present:
            raise ValueError(
                "live_effect_present must match whether the observation outcome recorded an effect"
            )
        if self.conformance_status == "effect_aligned":
            if self.observation_outcome != "bounded_effect_observed":
                raise ValueError("effect_aligned requires bounded_effect_observed")
            if self.boundedness_verdict != "bounded":
                raise ValueError("effect_aligned requires bounded verdict")
        else:
            if self.observation_outcome == "bounded_effect_observed":
                raise ValueError("effect_divergent may not carry bounded_effect_observed")
        object.__setattr__(
            self,
            "report_id",
            _assign_or_verify_content_addressed_id(
                value=self.report_id,
                field_name="report_id",
                prefix="agentic_de_local_effect_conformance_report",
                payload=self.model_dump(mode="json", exclude={"report_id"}),
            ),
        )
        return self


class AgenticDeObservedRestorationWriteEntry(BaseModel):
    model_config = MODEL_CONFIG

    relative_path: str
    restoration_operation: LocalEffectRestorationOperation
    prior_observation_write_kind: Literal["create_new"] = "create_new"
    existed_before_restoration: bool
    exists_after_restoration: bool
    bytes_removed: int = Field(ge=0)
    removed_content_sha256: str

    @model_validator(mode="after")
    def _validate_entry(self) -> AgenticDeObservedRestorationWriteEntry:
        _assert_present_text(self.relative_path, field_name="relative_path")
        _assert_present_text(
            self.removed_content_sha256,
            field_name="removed_content_sha256",
        )
        if self.exists_after_restoration:
            raise ValueError("restoration observed write entries must end with no surviving target")
        return self


class AgenticDeLocalEffectRestorationRecord(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_LOCAL_EFFECT_RESTORATION_RECORD_SCHEMA] = (
        AGENTIC_DE_LOCAL_EFFECT_RESTORATION_RECORD_SCHEMA
    )
    restoration_id: str | None = None
    target_arc: str
    target_path: str
    evidence_only: Literal[True] = True
    changes_live_behavior_by_default: Literal[False] = False
    selected_live_action_class: Literal["local_write"] = "local_write"
    selected_restoration_exemplar: Literal[
        "compensating_restore_of_v57a_create_new_artifact_only"
    ] = "compensating_restore_of_v57a_create_new_artifact_only"
    replay_mode: Literal[
        "bounded_recomputation_and_re_evaluation_of_the_restoration_event_against_prior_observed_effect_lineage_only"
    ] = (
        "bounded_recomputation_and_re_evaluation_of_the_restoration_event_"
        "against_prior_observed_effect_lineage_only"
    )
    restoration_entitlement_mode: Literal[
        "lineage_bound_evidence_bound_bounded_compensating_scope_derivation_only"
    ] = "lineage_bound_evidence_bound_bounded_compensating_scope_derivation_only"
    designated_sandbox_root: str
    packet_ref: str
    action_proposal_ref: str
    checkpoint_ref: str
    runtime_state_ref: str
    ticket_ref: str
    harvest_ref: str
    observation_ref: str
    conformance_ref: str
    restoration_pre_state_ref: str
    restoration_observed_write_set: list[AgenticDeObservedRestorationWriteEntry]
    restoration_post_state_ref: str
    restoration_effect: str
    restoration_outcome: LocalEffectRestorationOutcome
    restoration_boundedness_verdict: BoundednessVerdict
    restoration_boundedness_note: str
    evidence_refs: list[str]

    @model_validator(mode="after")
    def _validate_record(self) -> AgenticDeLocalEffectRestorationRecord:
        _assert_present_text(self.target_arc, field_name="target_arc")
        _assert_present_text(self.target_path, field_name="target_path")
        _assert_present_text(
            self.designated_sandbox_root,
            field_name="designated_sandbox_root",
        )
        _assert_present_text(self.packet_ref, field_name="packet_ref")
        _assert_present_text(self.action_proposal_ref, field_name="action_proposal_ref")
        _assert_present_text(self.checkpoint_ref, field_name="checkpoint_ref")
        _assert_present_text(self.runtime_state_ref, field_name="runtime_state_ref")
        _assert_present_text(self.ticket_ref, field_name="ticket_ref")
        _assert_present_text(self.harvest_ref, field_name="harvest_ref")
        _assert_present_text(self.observation_ref, field_name="observation_ref")
        _assert_present_text(self.conformance_ref, field_name="conformance_ref")
        _assert_present_text(
            self.restoration_pre_state_ref,
            field_name="restoration_pre_state_ref",
        )
        _assert_present_text(
            self.restoration_post_state_ref,
            field_name="restoration_post_state_ref",
        )
        _assert_present_text(self.restoration_effect, field_name="restoration_effect")
        _assert_present_text(
            self.restoration_boundedness_note,
            field_name="restoration_boundedness_note",
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _ordered_unique_texts(self.evidence_refs, field_name="evidence_refs"),
        )
        observed_paths = [entry.relative_path for entry in self.restoration_observed_write_set]
        if len(set(observed_paths)) != len(observed_paths):
            raise ValueError("restoration_observed_write_set relative_path values must be unique")
        if self.restoration_outcome == "restoration_effect_observed":
            if not self.restoration_observed_write_set:
                raise ValueError(
                    "restoration_effect_observed requires a restoration_observed_write_set"
                )
            if self.restoration_boundedness_verdict != "bounded":
                raise ValueError("restoration_effect_observed requires bounded verdict")
        elif self.restoration_outcome == "no_restoration_effect_observed":
            if self.restoration_observed_write_set:
                raise ValueError(
                    "no_restoration_effect_observed may not carry restoration observed writes"
                )
            if self.restoration_boundedness_verdict != "bounded":
                raise ValueError("no_restoration_effect_observed requires bounded verdict")
        elif self.restoration_outcome == "restoration_out_of_scope_write_observed":
            if not self.restoration_observed_write_set:
                raise ValueError(
                    "restoration_out_of_scope_write_observed requires restoration observed writes"
                )
            if self.restoration_boundedness_verdict != "failed":
                raise ValueError(
                    "restoration_out_of_scope_write_observed requires failed verdict"
                )
        elif self.restoration_outcome == "restoration_mismatched_effect_observed":
            if not self.restoration_observed_write_set:
                raise ValueError(
                    "restoration_mismatched_effect_observed requires restoration observed writes"
                )
            if self.restoration_boundedness_verdict != "bounded":
                raise ValueError(
                    "restoration_mismatched_effect_observed requires bounded verdict"
                )
        elif self.restoration_outcome == "restoration_boundedness_verdict_failed":
            if self.restoration_boundedness_verdict != "failed":
                raise ValueError("restoration_boundedness_verdict_failed requires failed verdict")
        object.__setattr__(
            self,
            "restoration_id",
            _assign_or_verify_content_addressed_id(
                value=self.restoration_id,
                field_name="restoration_id",
                prefix="agentic_de_local_effect_restoration",
                payload=self.model_dump(mode="json", exclude={"restoration_id"}),
            ),
        )
        return self


class AgenticDeLocalEffectHardeningEntry(BaseModel):
    model_config = MODEL_CONFIG

    hardening_id: str | None = None
    ticket_ref: str
    action_proposal_ref: str
    checkpoint_ref: str
    observation_ref: str
    local_effect_conformance_ref: str
    restoration_ref: str
    observation_boundedness_verdict: BoundednessVerdict
    restoration_boundedness_verdict: BoundednessVerdict
    selected_hardening_target_surface: str
    evidence_basis_summary: str
    boundedness_conformance_summary: str
    recommendation_scope_requires_later_lock: Literal[True] = True
    recommended_outcome: GovernanceDecisionOutcome
    rationale: str
    reason_codes: list[str]
    evidence_refs: list[str]

    @model_validator(mode="after")
    def _validate_entry(self) -> AgenticDeLocalEffectHardeningEntry:
        _assert_present_text(self.ticket_ref, field_name="ticket_ref")
        _assert_present_text(self.action_proposal_ref, field_name="action_proposal_ref")
        _assert_present_text(self.checkpoint_ref, field_name="checkpoint_ref")
        _assert_present_text(self.observation_ref, field_name="observation_ref")
        _assert_present_text(
            self.local_effect_conformance_ref,
            field_name="local_effect_conformance_ref",
        )
        _assert_present_text(self.restoration_ref, field_name="restoration_ref")
        _assert_present_text(
            self.selected_hardening_target_surface,
            field_name="selected_hardening_target_surface",
        )
        _assert_present_text(
            self.evidence_basis_summary,
            field_name="evidence_basis_summary",
        )
        _assert_present_text(
            self.boundedness_conformance_summary,
            field_name="boundedness_conformance_summary",
        )
        _assert_present_text(self.rationale, field_name="rationale")
        object.__setattr__(
            self,
            "reason_codes",
            _ordered_unique_texts(self.reason_codes, field_name="reason_codes"),
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _ordered_unique_texts(self.evidence_refs, field_name="evidence_refs"),
        )
        if self.recommended_outcome == "candidate_for_later_local_hardening":
            if self.observation_boundedness_verdict != "bounded":
                raise ValueError(
                    "candidate_for_later_local_hardening requires bounded observation verdict"
                )
            if self.restoration_boundedness_verdict != "bounded":
                raise ValueError(
                    "candidate_for_later_local_hardening requires bounded restoration verdict"
                )
            if "later_lock_required_for_scope" not in self.reason_codes:
                raise ValueError(
                    "candidate_for_later_local_hardening requires later_lock_required_for_scope"
                )
        object.__setattr__(
            self,
            "hardening_id",
            _assign_or_verify_content_addressed_id(
                value=self.hardening_id,
                field_name="hardening_id",
                prefix="agentic_de_local_effect_hardening",
                payload=self.model_dump(mode="json", exclude={"hardening_id"}),
            ),
        )
        return self


class AgenticDeLocalEffectHardeningRegister(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_LOCAL_EFFECT_HARDENING_REGISTER_SCHEMA] = (
        AGENTIC_DE_LOCAL_EFFECT_HARDENING_REGISTER_SCHEMA
    )
    register_id: str | None = None
    target_arc: str
    target_path: str
    advisory_only: Literal[True] = True
    candidate_only: Literal[True] = True
    path_level_only: Literal[True] = True
    exemplar_evidence_non_generalizing_by_default: Literal[True] = True
    changes_live_behavior_by_default: Literal[False] = False
    baseline_checker_version: str
    entry_count: int
    entries: list[AgenticDeLocalEffectHardeningEntry]

    @model_validator(mode="after")
    def _validate_register(self) -> AgenticDeLocalEffectHardeningRegister:
        _assert_present_text(self.target_arc, field_name="target_arc")
        _assert_present_text(self.target_path, field_name="target_path")
        _assert_present_text(
            self.baseline_checker_version,
            field_name="baseline_checker_version",
        )
        if self.advisory_only is not True:
            raise ValueError("advisory_only must remain true in V57-C")
        if self.candidate_only is not True:
            raise ValueError("candidate_only must remain true in V57-C")
        if self.path_level_only is not True:
            raise ValueError("path_level_only must remain true in V57-C")
        if self.exemplar_evidence_non_generalizing_by_default is not True:
            raise ValueError(
                "exemplar_evidence_non_generalizing_by_default must remain true in V57-C"
            )
        if self.changes_live_behavior_by_default is not False:
            raise ValueError("changes_live_behavior_by_default must remain false in V57-C")
        if self.entry_count != len(self.entries):
            raise ValueError("entry_count must equal len(entries)")
        target_surfaces = [entry.selected_hardening_target_surface for entry in self.entries]
        if len(set(target_surfaces)) != len(target_surfaces):
            raise ValueError("selected_hardening_target_surface values must be unique")
        object.__setattr__(
            self,
            "register_id",
            _assign_or_verify_content_addressed_id(
                value=self.register_id,
                field_name="register_id",
                prefix="agentic_de_local_effect_hardening_register",
                payload=self.model_dump(mode="json", exclude={"register_id"}),
            ),
        )
        return self


class AgenticDeLiveTurnAdmissionRecord(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_LIVE_TURN_ADMISSION_RECORD_SCHEMA] = (
        AGENTIC_DE_LIVE_TURN_ADMISSION_RECORD_SCHEMA
    )
    admission_id: str | None = None
    target_arc: str
    target_path: str
    evidence_only: Literal[True] = True
    changes_live_behavior_by_default: Literal[False] = False
    live_session_surface: Literal["urm_copilot_session_path"] = "urm_copilot_session_path"
    live_session_id: str
    live_turn_id: str
    session_status: str
    session_capability_snapshot: str
    approval_posture_snapshot: str
    admission_verdict: LiveTurnAdmissionVerdict
    admission_reason_codes: list[str]
    repo_root_path: str
    cwd_path: str
    designated_sandbox_root: str
    selected_live_path_identity: str
    observability_refs: list[str]
    evidence_refs: list[str]

    @model_validator(mode="after")
    def _validate_record(self) -> AgenticDeLiveTurnAdmissionRecord:
        _assert_present_text(self.target_arc, field_name="target_arc")
        _assert_present_text(self.target_path, field_name="target_path")
        _assert_present_text(self.live_session_id, field_name="live_session_id")
        _assert_present_text(self.live_turn_id, field_name="live_turn_id")
        _assert_present_text(self.session_status, field_name="session_status")
        _assert_present_text(
            self.session_capability_snapshot,
            field_name="session_capability_snapshot",
        )
        _assert_present_text(
            self.approval_posture_snapshot,
            field_name="approval_posture_snapshot",
        )
        _assert_present_text(self.repo_root_path, field_name="repo_root_path")
        _assert_present_text(self.cwd_path, field_name="cwd_path")
        _assert_present_text(
            self.designated_sandbox_root,
            field_name="designated_sandbox_root",
        )
        _assert_present_text(
            self.selected_live_path_identity,
            field_name="selected_live_path_identity",
        )
        object.__setattr__(
            self,
            "admission_reason_codes",
            _ordered_unique_texts(
                self.admission_reason_codes,
                field_name="admission_reason_codes",
            ),
        )
        object.__setattr__(
            self,
            "observability_refs",
            _ordered_unique_texts(self.observability_refs, field_name="observability_refs"),
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _ordered_unique_texts(self.evidence_refs, field_name="evidence_refs"),
        )
        if not self.admission_reason_codes:
            raise ValueError("admission_reason_codes must be non-empty")
        object.__setattr__(
            self,
            "admission_id",
            _assign_or_verify_content_addressed_id(
                value=self.admission_id,
                field_name="admission_id",
                prefix="agentic_de_live_turn_admission",
                payload=self.model_dump(mode="json", exclude={"admission_id"}),
            ),
        )
        return self


class AgenticDeLiveTurnHandoffRecord(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_LIVE_TURN_HANDOFF_RECORD_SCHEMA] = (
        AGENTIC_DE_LIVE_TURN_HANDOFF_RECORD_SCHEMA
    )
    handoff_id: str | None = None
    target_arc: str
    target_path: str
    evidence_only: Literal[True] = True
    changes_live_behavior_by_default: Literal[False] = False
    turn_admission_ref: str
    domain_packet_ref: str
    action_proposal_ref: str
    checkpoint_ref: str
    action_ticket_ref: str
    target_relative_path: str
    selected_effect_scope: str
    field_origin_tags: dict[str, LiveTurnFieldOriginTag]
    field_dependence_tags: dict[str, list[str]]
    root_origin_ids: list[str]
    evidence_refs: list[str]

    @model_validator(mode="after")
    def _validate_record(self) -> AgenticDeLiveTurnHandoffRecord:
        required_fields = (
            "turn_admission_ref",
            "domain_packet_ref",
            "action_proposal_ref",
            "checkpoint_ref",
            "action_ticket_ref",
            "target_relative_path",
            "selected_effect_scope",
        )
        _assert_present_text(self.target_arc, field_name="target_arc")
        _assert_present_text(self.target_path, field_name="target_path")
        for field_name in required_fields:
            _assert_present_text(getattr(self, field_name), field_name=field_name)
            if field_name not in self.field_origin_tags:
                raise ValueError(f"field_origin_tags missing required key {field_name}")
            if field_name not in self.field_dependence_tags:
                raise ValueError(f"field_dependence_tags missing required key {field_name}")
        normalized_dependence_tags: dict[str, list[str]] = {}
        for key, values in self.field_dependence_tags.items():
            normalized_dependence_tags[key] = _ordered_unique_texts(
                values,
                field_name=f"field_dependence_tags[{key}]",
            )
        object.__setattr__(self, "field_dependence_tags", normalized_dependence_tags)
        object.__setattr__(
            self,
            "root_origin_ids",
            _ordered_unique_texts(self.root_origin_ids, field_name="root_origin_ids"),
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _ordered_unique_texts(self.evidence_refs, field_name="evidence_refs"),
        )
        object.__setattr__(
            self,
            "handoff_id",
            _assign_or_verify_content_addressed_id(
                value=self.handoff_id,
                field_name="handoff_id",
                prefix="agentic_de_live_turn_handoff",
                payload=self.model_dump(mode="json", exclude={"handoff_id"}),
            ),
        )
        return self


class AgenticDeLiveTurnReintegrationReport(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_LIVE_TURN_REINTEGRATION_REPORT_SCHEMA] = (
        AGENTIC_DE_LIVE_TURN_REINTEGRATION_REPORT_SCHEMA
    )
    report_id: str | None = None
    target_arc: str
    target_path: str
    evidence_only: Literal[True] = True
    changes_live_behavior_by_default: Literal[False] = False
    turn_admission_ref: str
    turn_handoff_ref: str
    observation_ref: str
    local_effect_conformance_ref: str
    observed_effect_summary: str
    reintegration_status: LiveTurnReintegrationStatus
    reason_codes: list[str]
    reintegration_witness_basis_summary: str
    reintegration_certificate_ref_or_equivalent: str | None = None
    field_origin_tags: dict[str, LiveTurnFieldOriginTag]
    field_dependence_tags: dict[str, list[str]]
    root_origin_dedup_summary: str
    six_lane_closeout_posture: str
    evidence_refs: list[str]

    @model_validator(mode="after")
    def _validate_report(self) -> AgenticDeLiveTurnReintegrationReport:
        _assert_present_text(self.target_arc, field_name="target_arc")
        _assert_present_text(self.target_path, field_name="target_path")
        _assert_present_text(self.turn_admission_ref, field_name="turn_admission_ref")
        _assert_present_text(self.turn_handoff_ref, field_name="turn_handoff_ref")
        _assert_present_text(self.observation_ref, field_name="observation_ref")
        _assert_present_text(
            self.local_effect_conformance_ref,
            field_name="local_effect_conformance_ref",
        )
        _assert_present_text(
            self.observed_effect_summary,
            field_name="observed_effect_summary",
        )
        _assert_present_text(
            self.reintegration_witness_basis_summary,
            field_name="reintegration_witness_basis_summary",
        )
        _assert_present_text(
            self.root_origin_dedup_summary,
            field_name="root_origin_dedup_summary",
        )
        _assert_present_text(
            self.six_lane_closeout_posture,
            field_name="six_lane_closeout_posture",
        )
        required_fields = (
            "observed_effect_summary",
            "reintegration_witness_basis_summary",
            "six_lane_closeout_posture",
        )
        for field_name in required_fields:
            if field_name not in self.field_origin_tags:
                raise ValueError(f"field_origin_tags missing required key {field_name}")
            if field_name not in self.field_dependence_tags:
                raise ValueError(f"field_dependence_tags missing required key {field_name}")
        normalized_dependence_tags: dict[str, list[str]] = {}
        for key, values in self.field_dependence_tags.items():
            normalized_dependence_tags[key] = _ordered_unique_texts(
                values,
                field_name=f"field_dependence_tags[{key}]",
            )
        object.__setattr__(self, "field_dependence_tags", normalized_dependence_tags)
        object.__setattr__(
            self,
            "reason_codes",
            _ordered_unique_texts(self.reason_codes, field_name="reason_codes"),
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _ordered_unique_texts(self.evidence_refs, field_name="evidence_refs"),
        )
        if not self.reason_codes:
            raise ValueError("reason_codes must be non-empty")
        if self.reintegration_status == "reintegrated":
            if self.reintegration_certificate_ref_or_equivalent is None:
                raise ValueError(
                    "reintegrated status requires reintegration_certificate_ref_or_equivalent"
                )
            _assert_present_text(
                self.reintegration_certificate_ref_or_equivalent,
                field_name="reintegration_certificate_ref_or_equivalent",
            )
        elif self.reintegration_certificate_ref_or_equivalent is not None:
            _assert_present_text(
                self.reintegration_certificate_ref_or_equivalent,
                field_name="reintegration_certificate_ref_or_equivalent",
            )
        object.__setattr__(
            self,
            "report_id",
            _assign_or_verify_content_addressed_id(
                value=self.report_id,
                field_name="report_id",
                prefix="agentic_de_live_turn_reintegration_report",
                payload=self.model_dump(mode="json", exclude={"report_id"}),
            ),
        )
        return self


class AgenticDeLiveRestorationHandoffRecord(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_LIVE_RESTORATION_HANDOFF_RECORD_SCHEMA] = (
        AGENTIC_DE_LIVE_RESTORATION_HANDOFF_RECORD_SCHEMA
    )
    handoff_id: str | None = None
    target_arc: str
    target_path: str
    evidence_only: Literal[True] = True
    changes_live_behavior_by_default: Literal[False] = False
    turn_admission_ref: str
    turn_handoff_ref: str
    prior_reintegration_ref: str
    restoration_time_session_capability_snapshot: str
    restoration_time_approval_posture_snapshot: str
    restoration_time_continuation_verdict: LiveRestorationContinuationVerdict
    restoration_record_ref: str
    action_ticket_ref: str
    bounded_compensating_scope_derivation_summary: str
    target_relative_path: str
    selected_restoration_scope: str
    field_origin_tags: dict[str, LiveTurnFieldOriginTag]
    field_dependence_tags: dict[str, list[str]]
    root_origin_ids: list[str]
    evidence_refs: list[str]

    @model_validator(mode="after")
    def _validate_record(self) -> AgenticDeLiveRestorationHandoffRecord:
        required_fields = (
            "turn_admission_ref",
            "turn_handoff_ref",
            "prior_reintegration_ref",
            "restoration_time_session_capability_snapshot",
            "restoration_time_approval_posture_snapshot",
            "restoration_record_ref",
            "action_ticket_ref",
            "bounded_compensating_scope_derivation_summary",
            "target_relative_path",
            "selected_restoration_scope",
        )
        _assert_present_text(self.target_arc, field_name="target_arc")
        _assert_present_text(self.target_path, field_name="target_path")
        for field_name in required_fields:
            _assert_present_text(getattr(self, field_name), field_name=field_name)
            if field_name not in self.field_origin_tags:
                raise ValueError(f"field_origin_tags missing required key {field_name}")
            if field_name not in self.field_dependence_tags:
                raise ValueError(f"field_dependence_tags missing required key {field_name}")
        if "restoration_time_continuation_verdict" not in self.field_origin_tags:
            raise ValueError(
                "field_origin_tags missing required key restoration_time_continuation_verdict"
            )
        if "restoration_time_continuation_verdict" not in self.field_dependence_tags:
            raise ValueError(
                "field_dependence_tags missing required key restoration_time_continuation_verdict"
            )
        normalized_dependence_tags: dict[str, list[str]] = {}
        for key, values in self.field_dependence_tags.items():
            normalized_dependence_tags[key] = _ordered_unique_texts(
                values,
                field_name=f"field_dependence_tags[{key}]",
            )
        object.__setattr__(self, "field_dependence_tags", normalized_dependence_tags)
        object.__setattr__(
            self,
            "root_origin_ids",
            _ordered_unique_texts(self.root_origin_ids, field_name="root_origin_ids"),
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _ordered_unique_texts(self.evidence_refs, field_name="evidence_refs"),
        )
        object.__setattr__(
            self,
            "handoff_id",
            _assign_or_verify_content_addressed_id(
                value=self.handoff_id,
                field_name="handoff_id",
                prefix="agentic_de_live_restoration_handoff",
                payload=self.model_dump(mode="json", exclude={"handoff_id"}),
            ),
        )
        return self


class AgenticDeLiveRestorationReintegrationReport(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_LIVE_RESTORATION_REINTEGRATION_REPORT_SCHEMA] = (
        AGENTIC_DE_LIVE_RESTORATION_REINTEGRATION_REPORT_SCHEMA
    )
    report_id: str | None = None
    target_arc: str
    target_path: str
    evidence_only: Literal[True] = True
    changes_live_behavior_by_default: Literal[False] = False
    turn_admission_ref: str
    live_restoration_handoff_ref: str
    restoration_record_ref: str
    restoration_effect_summary: str
    restoration_reintegration_status: LiveTurnReintegrationStatus
    reason_codes: list[str]
    restoration_reintegration_witness_basis_summary: str
    restoration_reintegration_certificate_ref_or_equivalent: str | None = None
    replay_law_proof_summary: str
    field_origin_tags: dict[str, LiveTurnFieldOriginTag]
    field_dependence_tags: dict[str, list[str]]
    root_origin_dedup_summary: str
    six_lane_closeout_posture: str
    evidence_refs: list[str]

    @model_validator(mode="after")
    def _validate_report(self) -> AgenticDeLiveRestorationReintegrationReport:
        _assert_present_text(self.target_arc, field_name="target_arc")
        _assert_present_text(self.target_path, field_name="target_path")
        _assert_present_text(self.turn_admission_ref, field_name="turn_admission_ref")
        _assert_present_text(
            self.live_restoration_handoff_ref,
            field_name="live_restoration_handoff_ref",
        )
        _assert_present_text(
            self.restoration_record_ref,
            field_name="restoration_record_ref",
        )
        _assert_present_text(
            self.restoration_effect_summary,
            field_name="restoration_effect_summary",
        )
        _assert_present_text(
            self.restoration_reintegration_witness_basis_summary,
            field_name="restoration_reintegration_witness_basis_summary",
        )
        _assert_present_text(
            self.replay_law_proof_summary,
            field_name="replay_law_proof_summary",
        )
        _assert_present_text(
            self.root_origin_dedup_summary,
            field_name="root_origin_dedup_summary",
        )
        _assert_present_text(
            self.six_lane_closeout_posture,
            field_name="six_lane_closeout_posture",
        )
        required_fields = (
            "restoration_effect_summary",
            "restoration_reintegration_witness_basis_summary",
            "replay_law_proof_summary",
            "six_lane_closeout_posture",
        )
        for field_name in required_fields:
            if field_name not in self.field_origin_tags:
                raise ValueError(f"field_origin_tags missing required key {field_name}")
            if field_name not in self.field_dependence_tags:
                raise ValueError(f"field_dependence_tags missing required key {field_name}")
        normalized_dependence_tags: dict[str, list[str]] = {}
        for key, values in self.field_dependence_tags.items():
            normalized_dependence_tags[key] = _ordered_unique_texts(
                values,
                field_name=f"field_dependence_tags[{key}]",
            )
        object.__setattr__(self, "field_dependence_tags", normalized_dependence_tags)
        object.__setattr__(
            self,
            "reason_codes",
            _ordered_unique_texts(self.reason_codes, field_name="reason_codes"),
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _ordered_unique_texts(self.evidence_refs, field_name="evidence_refs"),
        )
        if not self.reason_codes:
            raise ValueError("reason_codes must be non-empty")
        if self.restoration_reintegration_status == "reintegrated":
            if self.restoration_reintegration_certificate_ref_or_equivalent is None:
                raise ValueError(
                    "reintegrated status requires "
                    "restoration_reintegration_certificate_ref_or_equivalent"
                )
            _assert_present_text(
                self.restoration_reintegration_certificate_ref_or_equivalent,
                field_name="restoration_reintegration_certificate_ref_or_equivalent",
            )
        elif self.restoration_reintegration_certificate_ref_or_equivalent is not None:
            _assert_present_text(
                self.restoration_reintegration_certificate_ref_or_equivalent,
                field_name="restoration_reintegration_certificate_ref_or_equivalent",
            )
        object.__setattr__(
            self,
            "report_id",
            _assign_or_verify_content_addressed_id(
                value=self.report_id,
                field_name="report_id",
                prefix="agentic_de_live_restoration_reintegration_report",
                payload=self.model_dump(mode="json", exclude={"report_id"}),
            ),
        )
        return self


class AgenticDeLiveHarnessHardeningEntry(BaseModel):
    model_config = MODEL_CONFIG

    hardening_id: str | None = None
    turn_admission_ref: str
    turn_handoff_ref: str
    turn_reintegration_ref: str
    live_restoration_handoff_ref: str
    restoration_ref: str
    live_restoration_reintegration_ref: str
    observation_ref: str
    local_effect_conformance_ref: str
    observation_boundedness_verdict: BoundednessVerdict
    restoration_boundedness_verdict: BoundednessVerdict
    turn_reintegration_status: LiveTurnReintegrationStatus
    restoration_reintegration_status: LiveTurnReintegrationStatus
    selected_hardening_target_surface: str
    evidence_basis_summary: str
    boundedness_reintegration_summary: str
    recommendation_scope_requires_later_lock: Literal[True] = True
    extensional_and_replayable_by_default: Literal[True] = True
    lineage_root_dedup_applied: Literal[True] = True
    root_origin_ids: list[str]
    root_origin_dedup_summary: str
    recommended_outcome: LiveHarnessHardeningOutcome
    rationale: str
    reason_codes: list[str]
    evidence_refs: list[str]

    @model_validator(mode="after")
    def _validate_entry(self) -> AgenticDeLiveHarnessHardeningEntry:
        required_fields = (
            "turn_admission_ref",
            "turn_handoff_ref",
            "turn_reintegration_ref",
            "live_restoration_handoff_ref",
            "restoration_ref",
            "live_restoration_reintegration_ref",
            "observation_ref",
            "local_effect_conformance_ref",
            "selected_hardening_target_surface",
            "evidence_basis_summary",
            "boundedness_reintegration_summary",
            "root_origin_dedup_summary",
            "rationale",
        )
        for field_name in required_fields:
            _assert_present_text(getattr(self, field_name), field_name=field_name)
        object.__setattr__(
            self,
            "root_origin_ids",
            _ordered_unique_texts(self.root_origin_ids, field_name="root_origin_ids"),
        )
        object.__setattr__(
            self,
            "reason_codes",
            _ordered_unique_texts(self.reason_codes, field_name="reason_codes"),
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _ordered_unique_texts(self.evidence_refs, field_name="evidence_refs"),
        )
        if not self.root_origin_ids:
            raise ValueError("root_origin_ids must be non-empty")
        if self.recommended_outcome == "candidate_for_later_harness_hardening":
            if self.observation_boundedness_verdict != "bounded":
                raise ValueError(
                    "candidate_for_later_harness_hardening requires bounded observation verdict"
                )
            if self.restoration_boundedness_verdict != "bounded":
                raise ValueError(
                    "candidate_for_later_harness_hardening requires bounded restoration verdict"
                )
            if self.turn_reintegration_status != "reintegrated":
                raise ValueError(
                    "candidate_for_later_harness_hardening requires reintegrated turn status"
                )
            if self.restoration_reintegration_status != "reintegrated":
                raise ValueError(
                    "candidate_for_later_harness_hardening requires reintegrated restoration status"
                )
            if "later_lock_required_for_scope" not in self.reason_codes:
                raise ValueError(
                    "candidate_for_later_harness_hardening requires later_lock_required_for_scope"
                )
        object.__setattr__(
            self,
            "hardening_id",
            _assign_or_verify_content_addressed_id(
                value=self.hardening_id,
                field_name="hardening_id",
                prefix="agentic_de_live_harness_hardening",
                payload=self.model_dump(mode="json", exclude={"hardening_id"}),
            ),
        )
        return self


class AgenticDeLiveHarnessHardeningRegister(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[AGENTIC_DE_LIVE_HARNESS_HARDENING_REGISTER_SCHEMA] = (
        AGENTIC_DE_LIVE_HARNESS_HARDENING_REGISTER_SCHEMA
    )
    register_id: str | None = None
    target_arc: str
    target_path: str
    advisory_only: Literal[True] = True
    candidate_only: Literal[True] = True
    path_level_only: Literal[True] = True
    exemplar_evidence_non_generalizing_by_default: Literal[True] = True
    changes_live_behavior_by_default: Literal[False] = False
    committed_lane_artifacts_outrank_narrative_docs: Literal[True] = True
    evidence_basis_distinct_from_recommendation: Literal[True] = True
    recommendation_function_extensional_and_replayable: Literal[True] = True
    lineage_root_non_independence_dedup_applied: Literal[True] = True
    baseline_checker_version: str
    entry_count: int
    entries: list[AgenticDeLiveHarnessHardeningEntry]

    @model_validator(mode="after")
    def _validate_register(self) -> AgenticDeLiveHarnessHardeningRegister:
        _assert_present_text(self.target_arc, field_name="target_arc")
        _assert_present_text(self.target_path, field_name="target_path")
        _assert_present_text(
            self.baseline_checker_version,
            field_name="baseline_checker_version",
        )
        if self.entry_count != len(self.entries):
            raise ValueError("entry_count must equal len(entries)")
        target_surfaces = [entry.selected_hardening_target_surface for entry in self.entries]
        if len(set(target_surfaces)) != len(target_surfaces):
            raise ValueError("selected_hardening_target_surface values must be unique")
        object.__setattr__(
            self,
            "register_id",
            _assign_or_verify_content_addressed_id(
                value=self.register_id,
                field_name="register_id",
                prefix="agentic_de_live_harness_hardening_register",
                payload=self.model_dump(mode="json", exclude={"register_id"}),
            ),
        )
        return self


def compute_agentic_de_domain_packet_id(payload: dict[str, object]) -> str:
    return _compute_id("agentic_de_domain_packet", payload)


def compute_agentic_de_morph_ir_id(payload: dict[str, object]) -> str:
    return _compute_id("agentic_de_morph_ir", payload)


def compute_agentic_de_interaction_contract_id(payload: dict[str, object]) -> str:
    return _compute_id("agentic_de_interaction_contract", payload)


def compute_agentic_de_action_proposal_id(payload: dict[str, object]) -> str:
    return _compute_id("agentic_de_action_proposal", payload)


def compute_agentic_de_membrane_checkpoint_id(payload: dict[str, object]) -> str:
    return _compute_id("agentic_de_membrane_checkpoint", payload)


def compute_agentic_de_morph_diagnostics_id(payload: dict[str, object]) -> str:
    return _compute_id("agentic_de_morph_diagnostics", payload)


def compute_agentic_de_conformance_report_id(payload: dict[str, object]) -> str:
    return _compute_id("agentic_de_conformance_report", payload)


def compute_agentic_de_action_class_taxonomy_id(payload: dict[str, object]) -> str:
    return _compute_id("agentic_de_action_class_taxonomy", payload)


def compute_agentic_de_runtime_state_id(payload: dict[str, object]) -> str:
    return _compute_id("agentic_de_runtime_state", payload)


def compute_agentic_de_action_ticket_id(payload: dict[str, object]) -> str:
    return _compute_id("agentic_de_action_ticket", payload)


def compute_agentic_de_lane_drift_record_id(payload: dict[str, object]) -> str:
    return _compute_id("agentic_de_lane_drift", payload)


def compute_agentic_de_runtime_harvest_record_id(payload: dict[str, object]) -> str:
    return _compute_id("agentic_de_runtime_harvest", payload)


def compute_agentic_de_governance_calibration_entry_id(payload: dict[str, object]) -> str:
    return _compute_id("agentic_de_governance_calibration", payload)


def compute_agentic_de_governance_calibration_register_id(payload: dict[str, object]) -> str:
    return _compute_id("agentic_de_governance_calibration_register", payload)


def compute_agentic_de_migration_decision_entry_id(payload: dict[str, object]) -> str:
    return _compute_id("agentic_de_migration_decision", payload)


def compute_agentic_de_migration_decision_register_id(payload: dict[str, object]) -> str:
    return _compute_id("agentic_de_migration_decision_register", payload)


def compute_agentic_de_local_effect_observation_record_id(
    payload: dict[str, object],
) -> str:
    return _compute_id("agentic_de_local_effect_observation", payload)


def compute_agentic_de_local_effect_conformance_report_id(
    payload: dict[str, object],
) -> str:
    return _compute_id("agentic_de_local_effect_conformance_report", payload)


def compute_agentic_de_local_effect_restoration_record_id(
    payload: dict[str, object],
) -> str:
    return _compute_id("agentic_de_local_effect_restoration", payload)


def compute_agentic_de_local_effect_hardening_entry_id(payload: dict[str, object]) -> str:
    return _compute_id("agentic_de_local_effect_hardening", payload)


def compute_agentic_de_local_effect_hardening_register_id(
    payload: dict[str, object],
) -> str:
    return _compute_id("agentic_de_local_effect_hardening_register", payload)


def compute_agentic_de_live_turn_admission_record_id(payload: dict[str, object]) -> str:
    return _compute_id("agentic_de_live_turn_admission", payload)


def compute_agentic_de_live_turn_handoff_record_id(payload: dict[str, object]) -> str:
    return _compute_id("agentic_de_live_turn_handoff", payload)


def compute_agentic_de_live_turn_reintegration_report_id(
    payload: dict[str, object],
) -> str:
    return _compute_id("agentic_de_live_turn_reintegration_report", payload)


def compute_agentic_de_live_restoration_handoff_record_id(
    payload: dict[str, object],
) -> str:
    return _compute_id("agentic_de_live_restoration_handoff", payload)


def compute_agentic_de_live_restoration_reintegration_report_id(
    payload: dict[str, object],
) -> str:
    return _compute_id("agentic_de_live_restoration_reintegration_report", payload)


def compute_agentic_de_live_harness_hardening_entry_id(
    payload: dict[str, object],
) -> str:
    return _compute_id("agentic_de_live_harness_hardening", payload)


def compute_agentic_de_live_harness_hardening_register_id(
    payload: dict[str, object],
) -> str:
    return _compute_id("agentic_de_live_harness_hardening_register", payload)
