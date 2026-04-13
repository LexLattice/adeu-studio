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
