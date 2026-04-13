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

ACTION_CLASS_VOCABULARY = ("inspect", "write", "execute", "dispatch")
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

MODEL_CONFIG = ConfigDict(
    extra="forbid",
    frozen=True,
    populate_by_name=True,
    protected_namespaces=(),
)

ActionClass = Literal["inspect", "write", "execute", "dispatch"]
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
        raise ValueError(
            f"{field_name} mismatch: expected {computed_id}, got {normalized}"
        )
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
