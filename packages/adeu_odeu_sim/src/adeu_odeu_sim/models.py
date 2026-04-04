from __future__ import annotations

import math
from enum import Enum
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

ADEU_ODEU_LANE_DELTA_SCHEMA = "adeu_odeu_lane_delta@1"
ADEU_ODEU_O_STATE_SCHEMA = "adeu_odeu_o_state@1"
ADEU_ODEU_E_STATE_SCHEMA = "adeu_odeu_e_state@1"
ADEU_ODEU_D_STATE_SCHEMA = "adeu_odeu_d_state@1"
ADEU_ODEU_U_STATE_SCHEMA = "adeu_odeu_u_state@1"
ADEU_ODEU_AGENT_SCHEMA = "adeu_odeu_agent@1"
ADEU_ODEU_RESOURCE_POOL_SCHEMA = "adeu_odeu_resource_pool@1"
ADEU_ODEU_INSTITUTION_SCHEMA = "adeu_odeu_institution@1"
ADEU_ODEU_NORM_SCHEMA = "adeu_odeu_norm@1"
ADEU_ODEU_OBSERVATION_SCHEMA = "adeu_odeu_observation@1"
ADEU_ODEU_EVIDENCE_RECORD_SCHEMA = "adeu_odeu_evidence_record@1"
ADEU_ODEU_CLAIM_SCHEMA = "adeu_odeu_claim@1"
ADEU_ODEU_PUBLIC_REPORT_SCHEMA = "adeu_odeu_public_report@1"
ADEU_ODEU_AUDIT_RESULT_SCHEMA = "adeu_odeu_audit_result@1"
ADEU_ODEU_SANCTION_EVENT_SCHEMA = "adeu_odeu_sanction_event@1"
ADEU_ODEU_ACTION_TEMPLATE_SCHEMA = "adeu_odeu_action_template@1"
ADEU_ODEU_ACTION_SCHEMA = "adeu_odeu_action@1"
ADEU_ODEU_LANE_CROSSING_CONTRACT_SCHEMA = "adeu_odeu_lane_crossing_contract@1"
ADEU_ODEU_SCENARIO_CONFIG_SCHEMA = "adeu_odeu_scenario_config@1"
ADEU_ODEU_METRIC_POINT_SCHEMA = "adeu_odeu_metric_point@1"
ADEU_ODEU_EVENT_RECORD_SCHEMA = "adeu_odeu_event_record@1"
ADEU_ODEU_WORLD_STATE_SCHEMA = "adeu_odeu_world_state@1"

MODEL_CONFIG = ConfigDict(extra="forbid", validate_assignment=True, populate_by_name=True)


def _ensure_finite(value: float, *, field_name: str) -> float:
    if not math.isfinite(value):
        raise ValueError(f"{field_name} must be finite")
    return value


def _ensure_non_empty_text(value: str, *, field_name: str) -> str:
    normalized = value.strip()
    if not normalized:
        raise ValueError(f"{field_name} must be non-empty")
    return normalized


def _ensure_probability(value: float, *, field_name: str) -> float:
    normalized = _ensure_finite(value, field_name=field_name)
    if normalized < 0.0 or normalized > 1.0:
        raise ValueError(f"{field_name} must be between 0.0 and 1.0")
    return normalized


def _sorted_unique_strings(values: list[str], *, field_name: str) -> list[str]:
    normalized = [_ensure_non_empty_text(value, field_name=field_name) for value in values]
    if normalized != sorted(normalized):
        raise ValueError(f"{field_name} must be sorted")
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must be unique")
    return normalized


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


class LaneName(str, Enum):
    O = "O"
    E = "E"
    D = "D"
    U = "U"


class LaneCrossingContractKind(str, Enum):
    O_TO_E_TRACE = "o_to_e_trace_contract"
    E_TO_D_LEGITIMACY = "e_to_d_legitimacy_contract"
    D_TO_O_ALLOCATION = "d_to_o_allocation_contract"
    U_TO_D_PRESSURE = "u_to_d_pressure_contract"


class EventRecordKind(str, Enum):
    SIMULATION_INITIALIZED = "simulation_initialized"
    TURN_STARTED = "turn_started"
    PLANNED_ACTION = "planned_action"
    TURN_COMPLETED = "turn_completed"
    REGIME_CLASSIFIED = "regime_classified"
    DIAGNOSTIC_NOTE = "diagnostic_note"


class RegimeLabel(str, Enum):
    COOPERATIVE_LEGIBLE_ORDER = "Cooperative Legible Order"
    COERCIVE_TRUTH_POOR_ORDER = "Coercive Truth-Poor Order"
    EPISTEMIC_CAPTURE_COLLAPSE = "Epistemic Capture Collapse"
    SYMBOLIC_INSTITUTION_DRIFT = "Symbolic Institution Drift"
    FRAGMENTED_OPPORTUNISM = "Fragmented Opportunism"
    CONTESTED_MIXED_REGIME = "Contested Mixed Regime"


class LaneDelta(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_LANE_DELTA_SCHEMA] = Field(
        default=ADEU_ODEU_LANE_DELTA_SCHEMA,
        alias="schema",
    )
    O: float = 0.0
    E: float = 0.0
    D: float = 0.0
    U: float = 0.0

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "LaneDelta":
        object.__setattr__(self, "O", _ensure_finite(self.O, field_name="O"))
        object.__setattr__(self, "E", _ensure_finite(self.E, field_name="E"))
        object.__setattr__(self, "D", _ensure_finite(self.D, field_name="D"))
        object.__setattr__(self, "U", _ensure_finite(self.U, field_name="U"))
        return self


class OState(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_O_STATE_SCHEMA] = Field(
        default=ADEU_ODEU_O_STATE_SCHEMA,
        alias="schema",
    )
    resources: float
    base_income: float
    evidence_access: float
    sanctioned_last_turn: bool = False
    pending_appeal: bool = False

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "OState":
        object.__setattr__(
            self, "resources", _ensure_finite(self.resources, field_name="resources")
        )
        object.__setattr__(
            self, "base_income", _ensure_finite(self.base_income, field_name="base_income")
        )
        object.__setattr__(
            self,
            "evidence_access",
            _ensure_probability(self.evidence_access, field_name="evidence_access"),
        )
        return self


class EState(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_E_STATE_SCHEMA] = Field(
        default=ADEU_ODEU_E_STATE_SCHEMA,
        alias="schema",
    )
    belief_commons: float
    uncertainty: float
    evidence_access: float
    verification_capacity: float
    epistemic_vigilance: float
    trust_institution: float
    trust_ai: float
    peer_trust: dict[str, float] = Field(default_factory=dict)
    last_verified_turn: int = -1

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "EState":
        object.__setattr__(
            self, "belief_commons", _ensure_finite(self.belief_commons, field_name="belief_commons")
        )
        object.__setattr__(
            self, "uncertainty", _ensure_probability(self.uncertainty, field_name="uncertainty")
        )
        object.__setattr__(
            self,
            "evidence_access",
            _ensure_probability(self.evidence_access, field_name="evidence_access"),
        )
        object.__setattr__(
            self,
            "verification_capacity",
            _ensure_probability(self.verification_capacity, field_name="verification_capacity"),
        )
        object.__setattr__(
            self,
            "epistemic_vigilance",
            _ensure_probability(self.epistemic_vigilance, field_name="epistemic_vigilance"),
        )
        object.__setattr__(
            self,
            "trust_institution",
            _ensure_probability(self.trust_institution, field_name="trust_institution"),
        )
        object.__setattr__(
            self, "trust_ai", _ensure_probability(self.trust_ai, field_name="trust_ai")
        )
        object.__setattr__(
            self,
            "peer_trust",
            {
                _ensure_non_empty_text(key, field_name="peer_trust key"): _ensure_probability(
                    value, field_name="peer_trust value"
                )
                for key, value in sorted(self.peer_trust.items())
            },
        )
        return self


class DState(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_D_STATE_SCHEMA] = Field(
        default=ADEU_ODEU_D_STATE_SCHEMA,
        alias="schema",
    )
    norm_commitment: float
    legitimacy_belief: float
    role_duty_strength: float
    appeal_propensity: float
    compliance_bias: float

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "DState":
        object.__setattr__(
            self,
            "norm_commitment",
            _ensure_probability(self.norm_commitment, field_name="norm_commitment"),
        )
        object.__setattr__(
            self,
            "legitimacy_belief",
            _ensure_probability(self.legitimacy_belief, field_name="legitimacy_belief"),
        )
        object.__setattr__(
            self,
            "role_duty_strength",
            _ensure_probability(self.role_duty_strength, field_name="role_duty_strength"),
        )
        object.__setattr__(
            self,
            "appeal_propensity",
            _ensure_probability(self.appeal_propensity, field_name="appeal_propensity"),
        )
        object.__setattr__(
            self,
            "compliance_bias",
            _ensure_probability(self.compliance_bias, field_name="compliance_bias"),
        )
        return self


class UState(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_U_STATE_SCHEMA] = Field(
        default=ADEU_ODEU_U_STATE_SCHEMA,
        alias="schema",
    )
    greed: float
    long_term_horizon: float
    fairness: float
    risk_tolerance: float
    sanction_aversion: float

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "UState":
        object.__setattr__(self, "greed", _ensure_probability(self.greed, field_name="greed"))
        object.__setattr__(
            self,
            "long_term_horizon",
            _ensure_probability(self.long_term_horizon, field_name="long_term_horizon"),
        )
        object.__setattr__(
            self, "fairness", _ensure_probability(self.fairness, field_name="fairness")
        )
        object.__setattr__(
            self,
            "risk_tolerance",
            _ensure_probability(self.risk_tolerance, field_name="risk_tolerance"),
        )
        object.__setattr__(
            self,
            "sanction_aversion",
            _ensure_probability(self.sanction_aversion, field_name="sanction_aversion"),
        )
        return self


class Agent(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_AGENT_SCHEMA] = Field(
        default=ADEU_ODEU_AGENT_SCHEMA,
        alias="schema",
    )
    id: str
    archetype: Archetype
    o_state: OState
    e_state: EState
    d_state: DState
    u_state: UState
    memory: list[str] = Field(default_factory=list)
    reputation: float = 0.5
    last_action: str = ActionType.DO_NOTHING.value

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "Agent":
        object.__setattr__(self, "id", _ensure_non_empty_text(self.id, field_name="id"))
        object.__setattr__(
            self,
            "memory",
            [_ensure_non_empty_text(item, field_name="memory") for item in self.memory],
        )
        object.__setattr__(
            self, "reputation", _ensure_probability(self.reputation, field_name="reputation")
        )
        object.__setattr__(
            self,
            "last_action",
            _ensure_non_empty_text(self.last_action, field_name="last_action"),
        )
        return self


class ResourcePool(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_RESOURCE_POOL_SCHEMA] = Field(
        default=ADEU_ODEU_RESOURCE_POOL_SCHEMA,
        alias="schema",
    )
    id: str = "commons"
    stock: float
    capacity: float
    regeneration_rate: float
    extraction_damage: float = 1.0

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "ResourcePool":
        object.__setattr__(self, "id", _ensure_non_empty_text(self.id, field_name="id"))
        object.__setattr__(self, "stock", _ensure_finite(self.stock, field_name="stock"))
        object.__setattr__(self, "capacity", _ensure_finite(self.capacity, field_name="capacity"))
        if self.capacity <= 0.0:
            raise ValueError("capacity must be positive")
        object.__setattr__(
            self,
            "regeneration_rate",
            _ensure_probability(self.regeneration_rate, field_name="regeneration_rate"),
        )
        object.__setattr__(
            self,
            "extraction_damage",
            _ensure_finite(self.extraction_damage, field_name="extraction_damage"),
        )
        if self.extraction_damage <= 0.0:
            raise ValueError("extraction_damage must be positive")
        return self


class Institution(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_INSTITUTION_SCHEMA] = Field(
        default=ADEU_ODEU_INSTITUTION_SCHEMA,
        alias="schema",
    )
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

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "Institution":
        object.__setattr__(self, "id", _ensure_non_empty_text(self.id, field_name="id"))
        object.__setattr__(self, "name", _ensure_non_empty_text(self.name, field_name="name"))
        object.__setattr__(
            self, "legitimacy", _ensure_probability(self.legitimacy, field_name="legitimacy")
        )
        object.__setattr__(
            self, "operativity", _ensure_probability(self.operativity, field_name="operativity")
        )
        object.__setattr__(
            self,
            "formal_presence",
            _ensure_probability(self.formal_presence, field_name="formal_presence"),
        )
        object.__setattr__(
            self,
            "enforcement_capacity",
            _ensure_probability(self.enforcement_capacity, field_name="enforcement_capacity"),
        )
        object.__setattr__(
            self,
            "enforcement_remaining",
            _ensure_probability(self.enforcement_remaining, field_name="enforcement_remaining"),
        )
        object.__setattr__(
            self,
            "sanction_consistency",
            _ensure_probability(self.sanction_consistency, field_name="sanction_consistency"),
        )
        object.__setattr__(
            self,
            "appeal_availability",
            _ensure_probability(self.appeal_availability, field_name="appeal_availability"),
        )
        object.__setattr__(
            self,
            "archive_capacity",
            _ensure_probability(self.archive_capacity, field_name="archive_capacity"),
        )
        object.__setattr__(
            self,
            "public_epistemics_level",
            _ensure_probability(self.public_epistemics_level, field_name="public_epistemics_level"),
        )
        object.__setattr__(self, "budget", _ensure_finite(self.budget, field_name="budget"))
        object.__setattr__(
            self,
            "capture_pressure",
            _ensure_probability(self.capture_pressure, field_name="capture_pressure"),
        )
        object.__setattr__(
            self,
            "pending_case_ids",
            _sorted_unique_strings(self.pending_case_ids, field_name="pending_case_ids"),
        )
        return self


class Observation(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_OBSERVATION_SCHEMA] = Field(
        default=ADEU_ODEU_OBSERVATION_SCHEMA,
        alias="schema",
    )
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

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "Observation":
        object.__setattr__(self, "id", _ensure_non_empty_text(self.id, field_name="id"))
        object.__setattr__(
            self, "observer_id", _ensure_non_empty_text(self.observer_id, field_name="observer_id")
        )
        if self.source_action_id is not None:
            object.__setattr__(
                self,
                "source_action_id",
                _ensure_non_empty_text(self.source_action_id, field_name="source_action_id"),
            )
        object.__setattr__(self, "kind", _ensure_non_empty_text(self.kind, field_name="kind"))
        object.__setattr__(
            self,
            "proposition",
            _ensure_non_empty_text(self.proposition, field_name="proposition"),
        )
        object.__setattr__(self, "value", _ensure_finite(self.value, field_name="value"))
        object.__setattr__(
            self, "confidence", _ensure_probability(self.confidence, field_name="confidence")
        )
        object.__setattr__(
            self, "visibility", _ensure_probability(self.visibility, field_name="visibility")
        )
        object.__setattr__(
            self, "raw_text", _ensure_non_empty_text(self.raw_text, field_name="raw_text")
        )
        return self


class EvidenceRecord(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_EVIDENCE_RECORD_SCHEMA] = Field(
        default=ADEU_ODEU_EVIDENCE_RECORD_SCHEMA,
        alias="schema",
    )
    id: str
    turn: int
    kind: str
    proposition: str
    value: float
    confidence: float
    source_ids: list[str] = Field(default_factory=list)
    archived: bool = True
    target_agent_id: str | None = None

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "EvidenceRecord":
        object.__setattr__(self, "id", _ensure_non_empty_text(self.id, field_name="id"))
        object.__setattr__(self, "kind", _ensure_non_empty_text(self.kind, field_name="kind"))
        object.__setattr__(
            self,
            "proposition",
            _ensure_non_empty_text(self.proposition, field_name="proposition"),
        )
        object.__setattr__(self, "value", _ensure_finite(self.value, field_name="value"))
        object.__setattr__(
            self, "confidence", _ensure_probability(self.confidence, field_name="confidence")
        )
        object.__setattr__(
            self, "source_ids", _sorted_unique_strings(self.source_ids, field_name="source_ids")
        )
        if self.target_agent_id is not None:
            object.__setattr__(
                self,
                "target_agent_id",
                _ensure_non_empty_text(self.target_agent_id, field_name="target_agent_id"),
            )
        return self


class Claim(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_CLAIM_SCHEMA] = Field(
        default=ADEU_ODEU_CLAIM_SCHEMA,
        alias="schema",
    )
    id: str
    turn: int
    source_id: str
    proposition: str
    value: float
    confidence: float
    truthful: bool | None = None
    evidence_refs: list[str] = Field(default_factory=list)
    audience: list[str] = Field(default_factory=list)

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "Claim":
        object.__setattr__(self, "id", _ensure_non_empty_text(self.id, field_name="id"))
        object.__setattr__(
            self, "source_id", _ensure_non_empty_text(self.source_id, field_name="source_id")
        )
        object.__setattr__(
            self,
            "proposition",
            _ensure_non_empty_text(self.proposition, field_name="proposition"),
        )
        object.__setattr__(self, "value", _ensure_finite(self.value, field_name="value"))
        object.__setattr__(
            self, "confidence", _ensure_probability(self.confidence, field_name="confidence")
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _sorted_unique_strings(self.evidence_refs, field_name="evidence_refs"),
        )
        object.__setattr__(
            self, "audience", _sorted_unique_strings(self.audience, field_name="audience")
        )
        return self


class PublicReport(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_PUBLIC_REPORT_SCHEMA] = Field(
        default=ADEU_ODEU_PUBLIC_REPORT_SCHEMA,
        alias="schema",
    )
    id: str
    turn: int
    source_type: str
    summary_stock: float
    reported_violation_rate: float
    confidence: float
    bias_note: str = ""
    evidence_refs: list[str] = Field(default_factory=list)
    truthful: bool | None = None

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "PublicReport":
        object.__setattr__(self, "id", _ensure_non_empty_text(self.id, field_name="id"))
        object.__setattr__(
            self,
            "source_type",
            _ensure_non_empty_text(self.source_type, field_name="source_type"),
        )
        object.__setattr__(
            self, "summary_stock", _ensure_finite(self.summary_stock, field_name="summary_stock")
        )
        object.__setattr__(
            self,
            "reported_violation_rate",
            _ensure_probability(self.reported_violation_rate, field_name="reported_violation_rate"),
        )
        object.__setattr__(
            self, "confidence", _ensure_probability(self.confidence, field_name="confidence")
        )
        object.__setattr__(
            self,
            "evidence_refs",
            _sorted_unique_strings(self.evidence_refs, field_name="evidence_refs"),
        )
        return self


class AuditResult(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_AUDIT_RESULT_SCHEMA] = Field(
        default=ADEU_ODEU_AUDIT_RESULT_SCHEMA,
        alias="schema",
    )
    id: str
    turn: int
    auditor_id: str
    target_institution_id: str
    fairness_score: float
    truth_alignment: float
    selective_enforcement_detected: bool
    notes: str

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "AuditResult":
        object.__setattr__(self, "id", _ensure_non_empty_text(self.id, field_name="id"))
        object.__setattr__(
            self, "auditor_id", _ensure_non_empty_text(self.auditor_id, field_name="auditor_id")
        )
        object.__setattr__(
            self,
            "target_institution_id",
            _ensure_non_empty_text(self.target_institution_id, field_name="target_institution_id"),
        )
        object.__setattr__(
            self,
            "fairness_score",
            _ensure_probability(self.fairness_score, field_name="fairness_score"),
        )
        object.__setattr__(
            self,
            "truth_alignment",
            _ensure_probability(self.truth_alignment, field_name="truth_alignment"),
        )
        object.__setattr__(self, "notes", _ensure_non_empty_text(self.notes, field_name="notes"))
        return self


class Norm(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_NORM_SCHEMA] = Field(
        default=ADEU_ODEU_NORM_SCHEMA,
        alias="schema",
    )
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

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "Norm":
        object.__setattr__(self, "id", _ensure_non_empty_text(self.id, field_name="id"))
        object.__setattr__(
            self,
            "subject_scope",
            _ensure_non_empty_text(self.subject_scope, field_name="subject_scope"),
        )
        object.__setattr__(
            self,
            "trigger_condition",
            _ensure_non_empty_text(self.trigger_condition, field_name="trigger_condition"),
        )
        object.__setattr__(
            self,
            "sanction_rule",
            _ensure_non_empty_text(self.sanction_rule, field_name="sanction_rule"),
        )
        object.__setattr__(
            self,
            "legitimacy_contribution",
            _ensure_probability(self.legitimacy_contribution, field_name="legitimacy_contribution"),
        )
        object.__setattr__(
            self,
            "enforcement_cost",
            _ensure_probability(self.enforcement_cost, field_name="enforcement_cost"),
        )
        object.__setattr__(
            self,
            "observability_dependency",
            _ensure_probability(
                self.observability_dependency, field_name="observability_dependency"
            ),
        )
        return self


class SanctionEvent(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_SANCTION_EVENT_SCHEMA] = Field(
        default=ADEU_ODEU_SANCTION_EVENT_SCHEMA,
        alias="schema",
    )
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

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "SanctionEvent":
        object.__setattr__(self, "id", _ensure_non_empty_text(self.id, field_name="id"))
        object.__setattr__(
            self, "actor_id", _ensure_non_empty_text(self.actor_id, field_name="actor_id")
        )
        object.__setattr__(
            self, "target_id", _ensure_non_empty_text(self.target_id, field_name="target_id")
        )
        object.__setattr__(self, "reason", _ensure_non_empty_text(self.reason, field_name="reason"))
        object.__setattr__(
            self, "severity", _ensure_probability(self.severity, field_name="severity")
        )
        if self.evidence_ref is not None:
            object.__setattr__(
                self,
                "evidence_ref",
                _ensure_non_empty_text(self.evidence_ref, field_name="evidence_ref"),
            )
        return self


class ActionTemplate(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_ACTION_TEMPLATE_SCHEMA] = Field(
        default=ADEU_ODEU_ACTION_TEMPLATE_SCHEMA,
        alias="schema",
    )
    action_type: ActionType
    actor_eligibility: tuple[str, ...]
    material_cost: float
    observability: float
    evidence_emission: str
    base_deontic_status: DeonticStatus
    lane_impact: LaneDelta

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "ActionTemplate":
        object.__setattr__(
            self,
            "actor_eligibility",
            tuple(
                _sorted_unique_strings(
                    list(self.actor_eligibility),
                    field_name="actor_eligibility",
                )
            ),
        )
        object.__setattr__(
            self,
            "material_cost",
            _ensure_finite(self.material_cost, field_name="material_cost"),
        )
        if self.material_cost < 0.0:
            raise ValueError("material_cost must be non-negative")
        object.__setattr__(
            self,
            "observability",
            _ensure_probability(self.observability, field_name="observability"),
        )
        object.__setattr__(
            self,
            "evidence_emission",
            _ensure_non_empty_text(self.evidence_emission, field_name="evidence_emission"),
        )
        return self


class Action(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_ACTION_SCHEMA] = Field(
        default=ADEU_ODEU_ACTION_SCHEMA,
        alias="schema",
    )
    id: str
    turn: int
    actor_id: str
    action_type: ActionType
    targets: tuple[str, ...] = ()
    material_cost: float
    observability: float
    evidence_emission: str
    deontic_status: DeonticStatus
    lane_impact: LaneDelta
    rationale: str = ""

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "Action":
        object.__setattr__(self, "id", _ensure_non_empty_text(self.id, field_name="id"))
        object.__setattr__(
            self, "actor_id", _ensure_non_empty_text(self.actor_id, field_name="actor_id")
        )
        object.__setattr__(
            self,
            "targets",
            tuple(_sorted_unique_strings(list(self.targets), field_name="targets")),
        )
        object.__setattr__(
            self, "material_cost", _ensure_finite(self.material_cost, field_name="material_cost")
        )
        if self.material_cost < 0.0:
            raise ValueError("material_cost must be non-negative")
        object.__setattr__(
            self,
            "observability",
            _ensure_probability(self.observability, field_name="observability"),
        )
        object.__setattr__(
            self,
            "evidence_emission",
            _ensure_non_empty_text(self.evidence_emission, field_name="evidence_emission"),
        )
        return self


class LaneCrossingContract(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_LANE_CROSSING_CONTRACT_SCHEMA] = Field(
        default=ADEU_ODEU_LANE_CROSSING_CONTRACT_SCHEMA,
        alias="schema",
    )
    contract_kind: LaneCrossingContractKind
    source_lane: LaneName
    target_lane: LaneName
    trigger_surface: str
    effect_surface: str
    diagnostic_posture: str

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "LaneCrossingContract":
        object.__setattr__(
            self,
            "trigger_surface",
            _ensure_non_empty_text(self.trigger_surface, field_name="trigger_surface"),
        )
        object.__setattr__(
            self,
            "effect_surface",
            _ensure_non_empty_text(self.effect_surface, field_name="effect_surface"),
        )
        object.__setattr__(
            self,
            "diagnostic_posture",
            _ensure_non_empty_text(self.diagnostic_posture, field_name="diagnostic_posture"),
        )
        expected = {
            LaneCrossingContractKind.O_TO_E_TRACE: (LaneName.O, LaneName.E),
            LaneCrossingContractKind.E_TO_D_LEGITIMACY: (LaneName.E, LaneName.D),
            LaneCrossingContractKind.D_TO_O_ALLOCATION: (LaneName.D, LaneName.O),
            LaneCrossingContractKind.U_TO_D_PRESSURE: (LaneName.U, LaneName.D),
        }[self.contract_kind]
        if (self.source_lane, self.target_lane) != expected:
            raise ValueError("contract_kind must match the frozen source/target lane pair")
        return self


class ScenarioConfig(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_SCENARIO_CONFIG_SCHEMA] = Field(
        default=ADEU_ODEU_SCENARIO_CONFIG_SCHEMA,
        alias="schema",
    )
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

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "ScenarioConfig":
        object.__setattr__(self, "name", _ensure_non_empty_text(self.name, field_name="name"))
        object.__setattr__(
            self,
            "description",
            _ensure_non_empty_text(self.description, field_name="description"),
        )
        if self.num_agents <= 0:
            raise ValueError("num_agents must be positive")
        if self.max_turns <= 0:
            raise ValueError("max_turns must be positive")
        for field_name in (
            "scarcity",
            "regeneration_rate",
            "misinformation",
            "verification_capacity",
            "enforcement_capacity",
            "initial_legitimacy",
            "initial_operativity",
            "sanction_consistency",
            "archive_capacity",
            "appeal_availability",
            "public_epistemics_level",
            "ai_reliability",
            "cooperator_share",
            "opportunist_share",
            "auditor_share",
            "official_share",
            "ai_dependent_share",
        ):
            object.__setattr__(
                self,
                field_name,
                _ensure_probability(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "sanction_severity",
            _ensure_finite(self.sanction_severity, field_name="sanction_severity"),
        )
        if self.sanction_severity <= 0.0:
            raise ValueError("sanction_severity must be positive")
        total_share = (
            self.cooperator_share
            + self.opportunist_share
            + self.auditor_share
            + self.official_share
            + self.ai_dependent_share
        )
        if abs(total_share - 1.0) > 1e-9:
            raise ValueError("scenario shares must sum exactly to 1.0")
        return self


class MetricPoint(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_METRIC_POINT_SCHEMA] = Field(
        default=ADEU_ODEU_METRIC_POINT_SCHEMA,
        alias="schema",
    )
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
    regime_label: RegimeLabel

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "MetricPoint":
        if self.turn < 0:
            raise ValueError("turn must be non-negative")
        for field_name in (
            "cooperation_rate",
            "commons_health",
            "average_belief_accuracy",
            "epistemic_integrity",
            "institution_legitimacy",
            "institution_operativity",
            "symbolic_gap",
            "sanction_consistency",
            "utility_concentration",
            "trust_fragmentation",
        ):
            object.__setattr__(
                self,
                field_name,
                _ensure_probability(getattr(self, field_name), field_name=field_name),
            )
        return self


class EventRecord(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_EVENT_RECORD_SCHEMA] = Field(
        default=ADEU_ODEU_EVENT_RECORD_SCHEMA,
        alias="schema",
    )
    event_kind: EventRecordKind
    turn: int
    summary: str
    related_ids: tuple[str, ...] = ()

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "EventRecord":
        if self.turn < 0:
            raise ValueError("turn must be non-negative")
        object.__setattr__(
            self, "summary", _ensure_non_empty_text(self.summary, field_name="summary")
        )
        object.__setattr__(
            self,
            "related_ids",
            tuple(_sorted_unique_strings(list(self.related_ids), field_name="related_ids")),
        )
        return self


class WorldState(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_ODEU_WORLD_STATE_SCHEMA] = Field(
        default=ADEU_ODEU_WORLD_STATE_SCHEMA,
        alias="schema",
    )
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
    event_records: list[EventRecord] = Field(default_factory=list)

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "WorldState":
        if self.seed < 0:
            raise ValueError("seed must be non-negative")
        if self.turn < 0:
            raise ValueError("turn must be non-negative")
        if not self.agents:
            raise ValueError("agents must be non-empty")
        object.__setattr__(
            self,
            "scenario",
            _ensure_non_empty_text(self.scenario, field_name="scenario"),
        )
        self._assert_sorted_ids(self.norms, "norms")
        self._assert_sorted_ids(self.agents, "agents")
        self._assert_sorted_ids(self.observations, "observations")
        self._assert_sorted_ids(self.evidence_records, "evidence_records")
        self._assert_sorted_ids(self.claims, "claims")
        self._assert_sorted_ids(self.public_reports, "public_reports")
        self._assert_sorted_ids(self.audit_results, "audit_results")
        self._assert_sorted_ids(self.sanction_events, "sanction_events")
        self._assert_sorted_ids(self.planned_actions, "planned_actions")
        turns = [metric.turn for metric in self.metrics_history]
        if turns != sorted(turns):
            raise ValueError("metrics_history must be sorted by turn")
        event_turns = [event.turn for event in self.event_records]
        if event_turns != sorted(event_turns):
            raise ValueError("event_records must be sorted by turn")
        return self

    @staticmethod
    def _assert_sorted_ids(items: list[BaseModel], field_name: str) -> None:
        ids: list[str] = []
        for item in items:
            item_id = getattr(item, "id", None)
            if item_id is None:
                continue
            ids.append(item_id)
        if ids and ids != sorted(ids):
            raise ValueError(f"{field_name} must be sorted by id")
        if len(ids) != len(set(ids)):
            raise ValueError(f"{field_name} must be unique by id")
