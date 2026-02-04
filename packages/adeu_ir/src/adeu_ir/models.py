from __future__ import annotations

from datetime import datetime
from typing import Annotated, Any, Literal, Optional, Union

from pydantic import BaseModel, ConfigDict, Field, model_validator

from .reason_codes import ReasonCode, ReasonSeverity

SchemaVersion = Literal["adeu.ir.v0"]

Channel = Literal["O", "D_phys", "D_norm", "E", "U"]

NormKind = Literal["obligation", "prohibition", "permission"]
EvidenceKind = Literal["obs", "def", "testimony", "infer"]
GoalKind = Literal["moral", "pref", "policy", "valence"]

BridgeType = Literal["interpretation", "u_to_dnorm", "u_to_e", "e_to_dnorm", "o_to_dnorm"]
BridgeStatus = Literal["provisional", "certified", "revoked"]

TimeKind = Literal["between", "before", "after", "at", "during", "unspecified"]
ExceptionEffect = Literal["defeats", "narrows", "clarifies"]
ConditionKind = Literal["text_only", "predicate"]


class SourceSpan(BaseModel):
    model_config = ConfigDict(extra="forbid")
    start: int = Field(ge=0)
    end: int = Field(gt=0)

    @model_validator(mode="after")
    def _check_span_order(self) -> "SourceSpan":
        if self.start >= self.end:
            raise ValueError("end must be greater than start")
        return self


class ProvenanceRef(BaseModel):
    model_config = ConfigDict(extra="forbid")
    doc_ref: Optional[str] = Field(
        default=None, description="E.g., 'MSA-2026#§3.2' or 'doc123#clause17'"
    )
    span: Optional[SourceSpan] = None
    quote: Optional[str] = None


def _normalize_feature_tokens(tokens: list[str]) -> list[str]:
    normalized = [t.strip().lower() for t in tokens]
    normalized = [t for t in normalized if t]
    return sorted(set(normalized))


class SourceFeatures(BaseModel):
    model_config = ConfigDict(extra="forbid")
    modals: list[str] = Field(default_factory=list)
    connectives: list[str] = Field(default_factory=list)
    has_time_vagueness: bool = False

    @model_validator(mode="after")
    def _normalize(self) -> "SourceFeatures":
        self.modals = _normalize_feature_tokens(self.modals)
        self.connectives = _normalize_feature_tokens(self.connectives)
        return self


class Context(BaseModel):
    model_config = ConfigDict(extra="forbid")
    doc_id: str
    jurisdiction: str
    time_eval: datetime
    source_features: SourceFeatures = Field(default_factory=SourceFeatures)


class Entity(BaseModel):
    model_config = ConfigDict(extra="forbid")
    id: str
    name: str
    kind: Optional[str] = Field(default=None, description="party|role|org|person|system|other")
    provenance: Optional[ProvenanceRef] = None


class Definition(BaseModel):
    model_config = ConfigDict(extra="forbid")
    id: str
    term: str
    meaning: str
    provenance: Optional[ProvenanceRef] = None


class EntityRef(BaseModel):
    model_config = ConfigDict(extra="forbid")
    ref_type: Literal["entity"] = "entity"
    entity_id: str


class DefinitionRef(BaseModel):
    model_config = ConfigDict(extra="forbid")
    ref_type: Literal["def"] = "def"
    def_id: str


class DocRef(BaseModel):
    model_config = ConfigDict(extra="forbid")
    ref_type: Literal["doc"] = "doc"
    doc_ref: str


class TextRef(BaseModel):
    model_config = ConfigDict(extra="forbid")
    ref_type: Literal["text"] = "text"
    text: str


Ref = Annotated[Union[EntityRef, DefinitionRef, DocRef, TextRef], Field(discriminator="ref_type")]


class Action(BaseModel):
    model_config = ConfigDict(extra="forbid")
    verb: str
    object: Optional[Ref] = None
    qualifiers: list[str] = Field(default_factory=list)


class TimeScope(BaseModel):
    model_config = ConfigDict(extra="forbid")
    kind: TimeKind
    start: Optional[datetime] = None
    end: Optional[datetime] = None


class Scope(BaseModel):
    model_config = ConfigDict(extra="forbid")
    jurisdiction: str
    time_about: TimeScope


class NormCondition(BaseModel):
    model_config = ConfigDict(extra="forbid")
    kind: ConditionKind
    text: str
    predicate: Optional[str] = None


class NormStatement(BaseModel):
    model_config = ConfigDict(extra="forbid")
    id: str
    kind: NormKind
    subject: Ref
    action: Action
    scope: Scope
    provenance: ProvenanceRef
    condition: Optional[NormCondition] = None


class ExceptionCondition(BaseModel):
    model_config = ConfigDict(extra="forbid")
    kind: ConditionKind
    text: str
    predicate: Optional[str] = None


class ExceptionClause(BaseModel):
    model_config = ConfigDict(extra="forbid")
    id: str
    applies_to: list[str] = Field(description="NormStatement.id targets")
    priority: int = 0
    condition: ExceptionCondition
    effect: ExceptionEffect
    provenance: ProvenanceRef


class EvidenceClaim(BaseModel):
    model_config = ConfigDict(extra="forbid")
    id: str
    kind: EvidenceKind
    statement: str
    provenance: Optional[ProvenanceRef] = None


class Goal(BaseModel):
    model_config = ConfigDict(extra="forbid")
    id: str
    kind: GoalKind
    statement: str
    provenance: Optional[ProvenanceRef] = None


class ValidatorRef(BaseModel):
    model_config = ConfigDict(extra="forbid")
    kind: Literal["authority_doc", "calibration", "experiment_log", "policy"]
    ref: str


class Bridge(BaseModel):
    model_config = ConfigDict(extra="forbid")
    id: str
    status: BridgeStatus
    from_channel: Channel
    to_channel: Channel
    bridge_type: BridgeType
    justification_text: str
    provenance: ProvenanceRef
    scope: Optional[Scope] = None
    validator: Optional[ValidatorRef] = None
    authority_ref: Optional[str] = None
    calibration_tag: Optional[str] = None


class JsonPatchOp(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)
    op: Literal["add", "remove", "replace", "move", "copy", "test"]
    path: str
    from_path: Optional[str] = Field(default=None, alias="from")
    value: Optional[Any] = None


class AmbiguityOption(BaseModel):
    model_config = ConfigDict(extra="forbid")
    option_id: str
    label: str
    effect: str
    variant_ir_id: Optional[str] = None
    patch: list[JsonPatchOp] = Field(default_factory=list)

    @model_validator(mode="after")
    def _one_of_variant_or_patch(self) -> "AmbiguityOption":
        has_variant = bool(self.variant_ir_id)
        has_patch = bool(self.patch)
        if has_variant == has_patch:
            raise ValueError("must provide exactly one of variant_ir_id or patch")
        return self


class Ambiguity(BaseModel):
    model_config = ConfigDict(extra="forbid")
    id: str
    span: SourceSpan
    issue: str
    options: list[AmbiguityOption]


class OChannel(BaseModel):
    model_config = ConfigDict(extra="forbid")
    entities: list[Entity] = Field(default_factory=list)
    definitions: list[Definition] = Field(default_factory=list)


class DPhysConstraint(BaseModel):
    model_config = ConfigDict(extra="forbid")
    id: str
    kind: Literal["mechanism", "resource_limit", "invariant", "law", "assumption"]
    statement: str
    provenance: Optional[ProvenanceRef] = None


class DPhysChannel(BaseModel):
    model_config = ConfigDict(extra="forbid")
    constraints: list[DPhysConstraint] = Field(default_factory=list)


class DNormChannel(BaseModel):
    model_config = ConfigDict(extra="forbid")
    statements: list[NormStatement] = Field(default_factory=list)
    exceptions: list[ExceptionClause] = Field(default_factory=list)


class EChannel(BaseModel):
    model_config = ConfigDict(extra="forbid")
    claims: list[EvidenceClaim] = Field(default_factory=list)


class UChannel(BaseModel):
    model_config = ConfigDict(extra="forbid")
    goals: list[Goal] = Field(default_factory=list)


class AdeuIR(BaseModel):
    model_config = ConfigDict(extra="forbid")
    schema_version: SchemaVersion = "adeu.ir.v0"
    ir_id: str
    context: Context

    O: OChannel = Field(default_factory=OChannel)
    D_phys: DPhysChannel = Field(default_factory=DPhysChannel)
    D_norm: DNormChannel = Field(default_factory=DNormChannel)
    E: EChannel = Field(default_factory=EChannel)
    U: UChannel = Field(default_factory=UChannel)

    bridges: list[Bridge] = Field(default_factory=list)
    ambiguity: list[Ambiguity] = Field(default_factory=list)


CheckStatus = Literal["PASS", "WARN", "REFUSE"]


class CheckReason(BaseModel):
    model_config = ConfigDict(extra="forbid")
    code: ReasonCode
    severity: ReasonSeverity
    message: str
    object_id: Optional[str] = None
    json_path: Optional[str] = None
    provenance: Optional[ProvenanceRef] = None


class TraceItem(BaseModel):
    model_config = ConfigDict(extra="forbid")
    rule_id: str
    because: list[str] = Field(default_factory=list)
    affected_ids: list[str] = Field(default_factory=list)
    notes: Optional[str] = None


class CheckMetrics(BaseModel):
    model_config = ConfigDict(extra="forbid")
    num_statements: int
    num_exceptions: int
    num_bridges: int
    num_ambiguities: int


class CheckReport(BaseModel):
    model_config = ConfigDict(extra="forbid")
    status: CheckStatus
    reason_codes: list[CheckReason] = Field(default_factory=list)
    trace: list[TraceItem] = Field(default_factory=list)
    metrics: CheckMetrics
