from __future__ import annotations

from enum import Enum
from typing import Any

from pydantic import BaseModel, ConfigDict, Field


class Archetype(str, Enum):
    COOPERATOR = "cooperator"
    OPPORTUNIST = "opportunist"
    AUDITOR = "auditor"
    OFFICIAL = "official"
    AI_DEPENDENT = "ai_dependent"


class AIBiasMode(str, Enum):
    NONE = "none"
    ACCURATE = "accurate"
    SYCOPHANTIC = "sycophantic"


class ActionType(str, Enum):
    CONTRIBUTE = "contribute_to_commons"
    DEFECT = "defect_or_overextract"
    SHARE_CLAIM = "share_claim"
    MISREPORT = "misreport"
    VERIFY = "verify"
    AUDIT = "audit_institution"
    SANCTION = "sanction"
    APPEAL = "appeal"
    INVEST_E = "invest_in_public_epistemics"
    INVEST_D = "invest_in_institution"
    DO_NOTHING = "do_nothing"


class NormModality(str, Enum):
    OBLIGATION = "obligation"
    PROHIBITION = "prohibition"
    PERMISSION = "permission"
    ROLE_DUTY = "role_duty"


class DeonticStatus(str, Enum):
    REQUIRED = "required"
    PERMITTED = "permitted"
    FORBIDDEN = "forbidden"
    CONTESTABLE = "contestable"


class LaneDelta(BaseModel):
    model_config = ConfigDict(extra="forbid")

    O: float = 0.0
    E: float = 0.0
    D: float = 0.0
    U: float = 0.0


class OState(BaseModel):
    model_config = ConfigDict(extra="forbid")

    resources: float
    base_income: float
    evidence_access: float
    sanctioned_last_turn: bool = False
    pending_appeal: bool = False


class EState(BaseModel):
    model_config = ConfigDict(extra="forbid")

    belief_commons: float
    uncertainty: float
    evidence_access: float
    verification_capacity: float
    epistemic_vigilance: float
    trust_institution: float
    trust_ai: float
    peer_trust: dict[str, float] = Field(default_factory=dict)
    last_verified_turn: int = -1


class DState(BaseModel):
    model_config = ConfigDict(extra="forbid")

    norm_commitment: float
    legitimacy_belief: float
    role_duty_strength: float
    appeal_propensity: float
    compliance_bias: float


class UState(BaseModel):
    model_config = ConfigDict(extra="forbid")

    greed: float
    long_term_horizon: float
    fairness: float
    risk_tolerance: float
    sanction_aversion: float


class Agent(BaseModel):
    model_config = ConfigDict(extra="forbid")

    id: str
    archetype: Archetype
    o_state: OState
    e_state: EState
    d_state: DState
    u_state: UState
    memory: list[str] = Field(default_factory=list)
    reputation: float = 0.5
    last_action: str = ActionType.DO_NOTHING.value
    recent_observations: list[str] = Field(default_factory=list)
    recent_claim_ids: list[str] = Field(default_factory=list)
    lane_notes: dict[str, str] = Field(default_factory=dict)


class ResourcePool(BaseModel):
    model_config = ConfigDict(extra="forbid")

    id: str = "commons"
    stock: float
    capacity: float
    regeneration_rate: float
    extraction_damage: float = 1.0


class Observation(BaseModel):
    model_config = ConfigDict(extra="forbid")

    id: str
    turn: int
    observer_id: str
    source_action_id: str | None = None
    kind: str
    proposition: str
    value: float
    confidence: float
    visibility: float = 1.0
    raw_text: str


class EvidenceRecord(BaseModel):
    model_config = ConfigDict(extra="forbid")

    id: str
    turn: int
    kind: str
    proposition: str
    value: float
    confidence: float
    source_ids: list[str] = Field(default_factory=list)
    archived: bool = True
    target_agent_id: str | None = None


class Claim(BaseModel):
    model_config = ConfigDict(extra="forbid")

    id: str
    turn: int
    source_id: str
    proposition: str
    value: float
    confidence: float
    truthful: bool | None = None
    evidence_refs: list[str] = Field(default_factory=list)
    audience: list[str] = Field(default_factory=list)


class PublicReport(BaseModel):
    model_config = ConfigDict(extra="forbid")

    id: str
    turn: int
    source_type: str
    summary_stock: float
    reported_violation_rate: float
    confidence: float
    bias_note: str = ""
    evidence_refs: list[str] = Field(default_factory=list)
    truthful: bool | None = None


class AuditResult(BaseModel):
    model_config = ConfigDict(extra="forbid")

    id: str
    turn: int
    auditor_id: str
    target_institution_id: str
    fairness_score: float
    truth_alignment: float
    selective_enforcement_detected: bool
    notes: str


class Norm(BaseModel):
    model_config = ConfigDict(extra="forbid")

    id: str
    modality: NormModality
    subject_scope: str
    trigger_condition: str
    target_action: ActionType
    sanction_rule: str
    appeal_available: bool
    legitimacy_contribution: float
    enforcement_cost: float
    observability_dependency: float


class SanctionEvent(BaseModel):
    model_config = ConfigDict(extra="forbid")

    id: str
    turn: int
    actor_id: str
    target_id: str
    reason: str
    severity: float
    evidence_ref: str | None = None
    fair: bool = True
    appealed: bool = False
    upheld: bool | None = None


class ActionTemplate(BaseModel):
    model_config = ConfigDict(extra="forbid")

    action_type: ActionType
    actor_eligibility: list[str]
    material_cost: float
    observability: float
    evidence_emission: str
    base_deontic_status: DeonticStatus
    lane_impact: LaneDelta


class Action(BaseModel):
    model_config = ConfigDict(extra="forbid")

    id: str
    turn: int
    actor_id: str
    action_type: ActionType
    targets: list[str] = Field(default_factory=list)
    material_cost: float
    observability: float
    evidence_emission: str
    deontic_status: DeonticStatus
    lane_impact: LaneDelta
    rationale: str = ""


class Institution(BaseModel):
    model_config = ConfigDict(extra="forbid")

    id: str
    name: str
    legitimacy: float
    operativity: float
    formal_presence: float = 1.0
    enforcement_capacity: float
    enforcement_remaining: float
    sanction_consistency: float
    appeal_availability: float
    archive_capacity: float
    public_epistemics_level: float
    budget: float = 0.0
    capture_pressure: float = 0.0
    pending_case_ids: list[str] = Field(default_factory=list)


class MetricPoint(BaseModel):
    model_config = ConfigDict(extra="forbid")

    turn: int
    cooperation_rate: float
    commons_health: float
    average_belief_accuracy: float
    epistemic_integrity: float
    institution_legitimacy: float
    institution_operativity: float
    symbolic_gap: float
    sanction_consistency: float
    utility_concentration: float
    trust_fragmentation: float
    regime_label: str


class ScenarioConfig(BaseModel):
    model_config = ConfigDict(extra="forbid")

    name: str
    description: str
    num_agents: int = 48
    scarcity: float = 0.35
    regeneration_rate: float = 0.1
    misinformation: float = 0.15
    verification_capacity: float = 0.55
    enforcement_capacity: float = 0.6
    sanction_severity: float = 1.4
    initial_legitimacy: float = 0.65
    initial_operativity: float = 0.65
    sanction_consistency: float = 0.7
    archive_capacity: float = 0.55
    appeal_availability: float = 0.7
    public_epistemics_level: float = 0.55
    ai_mode: AIBiasMode = AIBiasMode.NONE
    ai_reliability: float = 0.0
    cooperator_share: float = 0.34
    opportunist_share: float = 0.28
    auditor_share: float = 0.18
    official_share: float = 0.08
    ai_dependent_share: float = 0.12
    max_turns: int = 200


class WorldState(BaseModel):
    model_config = ConfigDict(extra="forbid")

    seed: int
    turn: int = 0
    scenario: str
    config: ScenarioConfig
    resource_pool: ResourcePool
    institution: Institution
    norms: list[Norm]
    agents: list[Agent]
    observations: list[Observation] = Field(default_factory=list)
    evidence_records: list[EvidenceRecord] = Field(default_factory=list)
    claims: list[Claim] = Field(default_factory=list)
    public_reports: list[PublicReport] = Field(default_factory=list)
    audit_results: list[AuditResult] = Field(default_factory=list)
    sanction_events: list[SanctionEvent] = Field(default_factory=list)
    planned_actions: list[Action] = Field(default_factory=list)
    metrics_history: list[MetricPoint] = Field(default_factory=list)
    event_log: list[str] = Field(default_factory=list)
    pending_observations: list[Observation] = Field(default_factory=list)
    pending_claims: list[Claim] = Field(default_factory=list)
    pending_public_reports: list[PublicReport] = Field(default_factory=list)
    pending_evidence: list[EvidenceRecord] = Field(default_factory=list)
    pending_cases: list[EvidenceRecord] = Field(default_factory=list)
    last_run_summary: dict[str, Any] = Field(default_factory=dict)
