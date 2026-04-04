from __future__ import annotations

from typing import Literal

from adeu_semantic_forms import sha256_canonical_json
from pydantic import BaseModel, ConfigDict, Field, model_validator

ADEU_PAPER_SOURCE_ARTIFACT_SCHEMA = "adeu_paper_source_artifact@1"
ADEU_PAPER_SOURCE_SPAN_SCHEMA = "adeu_paper_source_span@1"
ADEU_PAPER_SEMANTIC_CLAIM_SCHEMA = "adeu_paper_semantic_claim@1"
ADEU_PAPER_SEMANTIC_LANE_FRAGMENT_SCHEMA = "adeu_paper_semantic_lane_fragment@1"
ADEU_PAPER_SEMANTIC_INFERENCE_BRIDGE_SCHEMA = "adeu_paper_semantic_inference_bridge@1"
ADEU_PAPER_SEMANTIC_DIAGNOSTIC_SCHEMA = "adeu_paper_semantic_diagnostic@1"
ADEU_PAPER_SEMANTIC_PROJECTION_SCHEMA = "adeu_paper_semantic_projection@1"
ADEU_PAPER_SEMANTIC_ARTIFACT_SCHEMA = "adeu_paper_semantic_artifact@1"
ADEU_PAPER_SEMANTIC_WORKER_REQUEST_SCHEMA = "adeu_paper_semantic_worker_request@1"

SOURCE_AUTHORITY_POSTURE = "source_text_and_explicit_span_anchors_authoritative"
INTERPRETATION_AUTHORITY_POSTURE = "advisory_only"
SEMANTIC_IDENTITY_MODE = "v49_hash_law_with_explicit_paper_domain_delta"
IDENTITY_FIELD_NAMES = (
    "source",
    "spans",
    "claims",
    "lane_fragments",
    "inference_bridges",
    "semantic_identity_mode",
)
PROJECTION_FIELD_NAMES = (
    "source_metadata",
    "diagnostics",
    "projections",
    "confidence_and_warrant_fields",
)
LANE_ORDER = ("O", "E", "D", "U")
DIAGNOSTIC_SEVERITY_ORDER = ("critical", "warning", "advisory")

MODEL_CONFIG = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

SourceArtifactKind = Literal["paper.abstract", "pasted.paragraph"]
LaneId = Literal["O", "E", "D", "U"]
RequestedDepth = Literal[1, 2]
FragmentSourceKind = Literal["explicit", "inferred"]
FragmentStatus = Literal["explicit", "inferred", "contested", "underdetermined", "missing"]
ClaimStatus = Literal["stable", "contested", "underdetermined"]
BridgeKind = Literal[
    "canonical_bridge",
    "supporting_bridge",
    "missing_bridge",
    "contested_bridge",
    "projection_bridge",
    "contradiction_bridge",
]
DiagnosticKind = Literal[
    "contradiction",
    "underdetermination",
    "missing_bridge",
    "overloaded_term",
    "implicit_assumption",
    "u_overreach",
]
DiagnosticSeverity = Literal["critical", "warning", "advisory"]
ProjectionSurface = Literal["artifact", "local"]
AnalysisMode = Literal["evidence-first"]
AuthorityMode = Literal["advisory-only"]
ReturnSchema = Literal["adeu_paper_semantic_artifact@1"]
IdentityFieldName = Literal[
    "source",
    "spans",
    "claims",
    "lane_fragments",
    "inference_bridges",
    "semantic_identity_mode",
]
ProjectionFieldName = Literal[
    "source_metadata",
    "diagnostics",
    "projections",
    "confidence_and_warrant_fields",
]


def _assert_non_empty_text(value: str, *, field_name: str) -> str:
    normalized = value.strip()
    if not normalized:
        raise ValueError(f"{field_name} must be non-empty")
    return normalized


def _assert_non_negative_int(value: int, *, field_name: str) -> int:
    if value < 0:
        raise ValueError(f"{field_name} must be non-negative")
    return value


def _assert_probability(value: float, *, field_name: str) -> float:
    if value < 0.0 or value > 1.0:
        raise ValueError(f"{field_name} must be between 0.0 and 1.0")
    return value


def _assert_optional_probability(value: float | None, *, field_name: str) -> float | None:
    if value is None:
        return None
    return _assert_probability(value, field_name=field_name)


def _assert_sorted_unique_texts(
    values: list[str], *, field_name: str, sort_values: bool = True
) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must be unique")
    return sorted(normalized) if sort_values else normalized


def _assert_author_list(values: list[str]) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name="authors") for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError("authors must be unique")
    return normalized


def _sorted_lane_ids(values: list[LaneId], *, field_name: str) -> list[LaneId]:
    normalized = list(values)
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must be unique")
    lane_order = {lane: index for index, lane in enumerate(LANE_ORDER)}
    return sorted(normalized, key=lambda item: lane_order[item])


def _compute_source_text_hash(source_text: str) -> str:
    return sha256_canonical_json({"source_text": source_text})


def compute_paper_source_id(
    *, artifact_kind: SourceArtifactKind, source_text_hash: str, paragraph_index: int | None
) -> str:
    digest = sha256_canonical_json(
        {
            "artifact_kind": artifact_kind,
            "paragraph_index": paragraph_index,
            "source_text_hash": source_text_hash,
        }
    )
    return f"paper_source:{digest[:16]}"


def compute_paper_request_id(request_hash: str) -> str:
    return f"paper_semantic_request:{request_hash[:16]}"


def compute_paper_artifact_id(semantic_hash: str) -> str:
    return f"paper_semantic:{semantic_hash[:16]}"


def _expected_nested_id(prefix: str, basis: dict[str, object]) -> str:
    return f"{prefix}:{sha256_canonical_json(basis)[:16]}"


class PaperSourceArtifact(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_PAPER_SOURCE_ARTIFACT_SCHEMA] = Field(
        default=ADEU_PAPER_SOURCE_ARTIFACT_SCHEMA,
        alias="schema",
    )
    source_id: str
    artifact_kind: SourceArtifactKind
    title: str
    authors: list[str]
    year: int | None = None
    venue: str | None = None
    source_text: str
    source_text_hash: str
    paragraph_index: int | None = None
    source_notes: list[str] = Field(default_factory=list)

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "PaperSourceArtifact":
        object.__setattr__(self, "title", _assert_non_empty_text(self.title, field_name="title"))
        object.__setattr__(self, "authors", _assert_author_list(self.authors))
        object.__setattr__(
            self, "source_text", _assert_non_empty_text(self.source_text, field_name="source_text")
        )
        object.__setattr__(
            self,
            "source_notes",
            _assert_sorted_unique_texts(self.source_notes, field_name="source_notes"),
        )
        if self.venue is not None:
            object.__setattr__(
                self, "venue", _assert_non_empty_text(self.venue, field_name="venue")
            )
        if self.year is not None:
            if self.year <= 0:
                raise ValueError("year must be positive when provided")
        if self.paragraph_index is not None:
            object.__setattr__(
                self,
                "paragraph_index",
                _assert_non_negative_int(self.paragraph_index, field_name="paragraph_index"),
            )
        if self.artifact_kind == "pasted.paragraph" and self.paragraph_index is None:
            raise ValueError("pasted.paragraph requires paragraph_index")
        expected_source_text_hash = _compute_source_text_hash(self.source_text)
        if self.source_text_hash != expected_source_text_hash:
            raise ValueError("source_text_hash must match source_text")
        expected_source_id = compute_paper_source_id(
            artifact_kind=self.artifact_kind,
            source_text_hash=self.source_text_hash,
            paragraph_index=self.paragraph_index,
        )
        if self.source_id != expected_source_id:
            raise ValueError("source_id must match canonical source identity")
        return self

    def identity_basis(self) -> dict[str, object]:
        return {
            "artifact_kind": self.artifact_kind,
            "paragraph_index": self.paragraph_index,
            "source_text_hash": self.source_text_hash,
        }


class PaperSourceSpan(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_PAPER_SOURCE_SPAN_SCHEMA] = Field(
        default=ADEU_PAPER_SOURCE_SPAN_SCHEMA,
        alias="schema",
    )
    span_id: str
    start: int
    end: int
    quote: str
    sentence_index: int
    paragraph_index: int

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "PaperSourceSpan":
        object.__setattr__(self, "start", _assert_non_negative_int(self.start, field_name="start"))
        object.__setattr__(self, "end", _assert_non_negative_int(self.end, field_name="end"))
        object.__setattr__(self, "quote", _assert_non_empty_text(self.quote, field_name="quote"))
        object.__setattr__(
            self,
            "sentence_index",
            _assert_non_negative_int(self.sentence_index, field_name="sentence_index"),
        )
        object.__setattr__(
            self,
            "paragraph_index",
            _assert_non_negative_int(self.paragraph_index, field_name="paragraph_index"),
        )
        if self.end <= self.start:
            raise ValueError("end must be greater than start")
        expected_span_id = _expected_nested_id(
            "span",
            {
                "start": self.start,
                "end": self.end,
                "quote": self.quote,
                "sentence_index": self.sentence_index,
                "paragraph_index": self.paragraph_index,
            },
        )
        if self.span_id != expected_span_id:
            raise ValueError("span_id must match canonical span identity")
        return self

    def identity_basis(self) -> dict[str, object]:
        return {
            "start": self.start,
            "end": self.end,
            "quote": self.quote,
            "sentence_index": self.sentence_index,
            "paragraph_index": self.paragraph_index,
        }


class PaperSemanticClaim(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_PAPER_SEMANTIC_CLAIM_SCHEMA] = Field(
        default=ADEU_PAPER_SEMANTIC_CLAIM_SCHEMA,
        alias="schema",
    )
    claim_id: str
    claim_text: str
    status: ClaimStatus
    span_ids: list[str] = Field(min_length=1)
    lane_fragment_ids: list[str] = Field(min_length=1)
    summary: str | None = None
    confidence: float | None = None

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "PaperSemanticClaim":
        object.__setattr__(
            self, "claim_text", _assert_non_empty_text(self.claim_text, field_name="claim_text")
        )
        object.__setattr__(
            self, "span_ids", _assert_sorted_unique_texts(self.span_ids, field_name="span_ids")
        )
        object.__setattr__(
            self,
            "lane_fragment_ids",
            _assert_sorted_unique_texts(self.lane_fragment_ids, field_name="lane_fragment_ids"),
        )
        if self.summary is not None:
            object.__setattr__(
                self, "summary", _assert_non_empty_text(self.summary, field_name="summary")
            )
        object.__setattr__(
            self,
            "confidence",
            _assert_optional_probability(self.confidence, field_name="confidence"),
        )
        expected_claim_id = _expected_nested_id("claim", self.identity_basis())
        if self.claim_id != expected_claim_id:
            raise ValueError("claim_id must match canonical claim identity")
        return self

    def identity_basis(self) -> dict[str, object]:
        return {
            "claim_text": self.claim_text,
            "lane_fragment_ids": self.lane_fragment_ids,
            "span_ids": self.span_ids,
            "status": self.status,
        }


class PaperSemanticLaneFragment(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_PAPER_SEMANTIC_LANE_FRAGMENT_SCHEMA] = Field(
        default=ADEU_PAPER_SEMANTIC_LANE_FRAGMENT_SCHEMA,
        alias="schema",
    )
    fragment_id: str
    claim_id: str
    lane_id: LaneId
    short_label: str
    fragment_text: str
    source_kind: FragmentSourceKind
    status: FragmentStatus
    confidence: float
    warrant: str
    span_ids: list[str] = Field(min_length=1)
    bridge_ids: list[str] = Field(default_factory=list)
    diagnostic_ids: list[str] = Field(default_factory=list)

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "PaperSemanticLaneFragment":
        object.__setattr__(
            self, "claim_id", _assert_non_empty_text(self.claim_id, field_name="claim_id")
        )
        object.__setattr__(
            self, "short_label", _assert_non_empty_text(self.short_label, field_name="short_label")
        )
        object.__setattr__(
            self,
            "fragment_text",
            _assert_non_empty_text(self.fragment_text, field_name="fragment_text"),
        )
        object.__setattr__(
            self, "confidence", _assert_probability(self.confidence, field_name="confidence")
        )
        object.__setattr__(
            self, "warrant", _assert_non_empty_text(self.warrant, field_name="warrant")
        )
        object.__setattr__(
            self, "span_ids", _assert_sorted_unique_texts(self.span_ids, field_name="span_ids")
        )
        object.__setattr__(
            self,
            "bridge_ids",
            _assert_sorted_unique_texts(self.bridge_ids, field_name="bridge_ids"),
        )
        object.__setattr__(
            self,
            "diagnostic_ids",
            _assert_sorted_unique_texts(self.diagnostic_ids, field_name="diagnostic_ids"),
        )
        expected_fragment_id = _expected_nested_id(
            "fragment",
            {
                "fragment_text": self.fragment_text,
                "lane_id": self.lane_id,
                "source_kind": self.source_kind,
                "span_ids": self.span_ids,
                "status": self.status,
            },
        )
        if self.fragment_id != expected_fragment_id:
            raise ValueError("fragment_id must match canonical fragment identity")
        return self

    def identity_basis(self) -> dict[str, object]:
        return {
            "bridge_ids": self.bridge_ids,
            "claim_id": self.claim_id,
            "fragment_text": self.fragment_text,
            "lane_id": self.lane_id,
            "source_kind": self.source_kind,
            "span_ids": self.span_ids,
            "status": self.status,
        }


class PaperSemanticInferenceBridge(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_PAPER_SEMANTIC_INFERENCE_BRIDGE_SCHEMA] = Field(
        default=ADEU_PAPER_SEMANTIC_INFERENCE_BRIDGE_SCHEMA,
        alias="schema",
    )
    bridge_id: str
    bridge_kind: BridgeKind
    from_fragment_ids: list[str] = Field(min_length=1)
    to_fragment_ids: list[str] = Field(min_length=1)
    rationale: str
    confidence: float
    diagnostic_ids: list[str] = Field(default_factory=list)

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "PaperSemanticInferenceBridge":
        object.__setattr__(
            self,
            "from_fragment_ids",
            _assert_sorted_unique_texts(self.from_fragment_ids, field_name="from_fragment_ids"),
        )
        object.__setattr__(
            self,
            "to_fragment_ids",
            _assert_sorted_unique_texts(self.to_fragment_ids, field_name="to_fragment_ids"),
        )
        object.__setattr__(
            self, "rationale", _assert_non_empty_text(self.rationale, field_name="rationale")
        )
        object.__setattr__(
            self, "confidence", _assert_probability(self.confidence, field_name="confidence")
        )
        object.__setattr__(
            self,
            "diagnostic_ids",
            _assert_sorted_unique_texts(self.diagnostic_ids, field_name="diagnostic_ids"),
        )
        expected_bridge_id = _expected_nested_id(
            "bridge",
            {
                "bridge_kind": self.bridge_kind,
                "from_fragment_ids": self.from_fragment_ids,
                "to_fragment_ids": self.to_fragment_ids,
            },
        )
        if self.bridge_id != expected_bridge_id:
            raise ValueError("bridge_id must match canonical bridge identity")
        return self

    def identity_basis(self) -> dict[str, object]:
        return {
            "bridge_kind": self.bridge_kind,
            "from_fragment_ids": self.from_fragment_ids,
            "to_fragment_ids": self.to_fragment_ids,
        }


class PaperSemanticDiagnostic(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_PAPER_SEMANTIC_DIAGNOSTIC_SCHEMA] = Field(
        default=ADEU_PAPER_SEMANTIC_DIAGNOSTIC_SCHEMA,
        alias="schema",
    )
    diagnostic_id: str
    diagnostic_kind: DiagnosticKind
    severity: DiagnosticSeverity
    summary: str
    lane_ids: list[LaneId] = Field(default_factory=list)
    related_fragment_ids: list[str] = Field(default_factory=list)
    span_ids: list[str] = Field(default_factory=list)

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "PaperSemanticDiagnostic":
        object.__setattr__(
            self, "summary", _assert_non_empty_text(self.summary, field_name="summary")
        )
        object.__setattr__(self, "lane_ids", _sorted_lane_ids(self.lane_ids, field_name="lane_ids"))
        object.__setattr__(
            self,
            "related_fragment_ids",
            _assert_sorted_unique_texts(
                self.related_fragment_ids, field_name="related_fragment_ids"
            ),
        )
        object.__setattr__(
            self, "span_ids", _assert_sorted_unique_texts(self.span_ids, field_name="span_ids")
        )
        expected_diagnostic_id = _expected_nested_id(
            "diagnostic",
            {
                "diagnostic_kind": self.diagnostic_kind,
                "lane_ids": self.lane_ids,
                "related_fragment_ids": self.related_fragment_ids,
                "severity": self.severity,
                "span_ids": self.span_ids,
                "summary": self.summary,
            },
        )
        if self.diagnostic_id != expected_diagnostic_id:
            raise ValueError("diagnostic_id must match canonical diagnostic identity")
        return self


class PaperSemanticProjection(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_PAPER_SEMANTIC_PROJECTION_SCHEMA] = Field(
        default=ADEU_PAPER_SEMANTIC_PROJECTION_SCHEMA,
        alias="schema",
    )
    projection_id: str
    surface: ProjectionSurface
    lane_order: list[LaneId] = Field(default_factory=lambda: list(LANE_ORDER))
    claim_order: list[str] = Field(default_factory=list)
    recommended_focus_claim_id: str | None = None
    diagnostic_summary: dict[DiagnosticSeverity, int] = Field(default_factory=dict)

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "PaperSemanticProjection":
        object.__setattr__(
            self, "lane_order", _sorted_lane_ids(self.lane_order, field_name="lane_order")
        )
        if tuple(self.lane_order) != LANE_ORDER:
            raise ValueError("lane_order must match the frozen O/E/D/U order")
        object.__setattr__(
            self,
            "claim_order",
            _assert_sorted_unique_texts(self.claim_order, field_name="claim_order"),
        )
        if self.recommended_focus_claim_id is not None:
            object.__setattr__(
                self,
                "recommended_focus_claim_id",
                _assert_non_empty_text(
                    self.recommended_focus_claim_id,
                    field_name="recommended_focus_claim_id",
                ),
            )
        normalized_summary: dict[DiagnosticSeverity, int] = {}
        for severity in DIAGNOSTIC_SEVERITY_ORDER:
            value = self.diagnostic_summary.get(severity, 0)
            if value < 0:
                raise ValueError("diagnostic_summary counts must be non-negative")
            normalized_summary[severity] = int(value)
        object.__setattr__(self, "diagnostic_summary", normalized_summary)
        expected_projection_id = _expected_nested_id(
            "projection",
            {
                "claim_order": self.claim_order,
                "diagnostic_summary": self.diagnostic_summary,
                "lane_order": self.lane_order,
                "recommended_focus_claim_id": self.recommended_focus_claim_id,
                "surface": self.surface,
            },
        )
        if self.projection_id != expected_projection_id:
            raise ValueError("projection_id must match canonical projection identity")
        return self


class PaperSemanticRequestOperatorPosture(BaseModel):
    model_config = MODEL_CONFIG

    analysis_mode: AnalysisMode = "evidence-first"
    authority_mode: AuthorityMode = "advisory-only"
    preserve_source_anchor: Literal[True] = True


class PaperSemanticRequestConstraints(BaseModel):
    model_config = MODEL_CONFIG

    anchor_explicit_claims_to_source_spans: Literal[True] = True
    infer_missing_odeu_lanes: Literal[True] = True
    mark_inferred_and_contested_content: Literal[True] = True
    include_diagnostics: Literal[True] = True
    max_top_level_claims: int
    max_subclaims_per_claim: int

    @model_validator(mode="after")
    def _validate(self) -> "PaperSemanticRequestConstraints":
        if self.max_top_level_claims < 1 or self.max_top_level_claims > 12:
            raise ValueError("max_top_level_claims must be between 1 and 12")
        if self.max_subclaims_per_claim < 0 or self.max_subclaims_per_claim > 8:
            raise ValueError("max_subclaims_per_claim must be between 0 and 8")
        return self


class PaperSemanticWorkerRequest(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_PAPER_SEMANTIC_WORKER_REQUEST_SCHEMA] = Field(
        default=ADEU_PAPER_SEMANTIC_WORKER_REQUEST_SCHEMA,
        alias="schema",
    )
    request_id: str
    title: str | None = None
    source_text: str
    source_kind: SourceArtifactKind
    requested_depth: RequestedDepth
    return_schema: ReturnSchema = ADEU_PAPER_SEMANTIC_ARTIFACT_SCHEMA
    operator_posture: PaperSemanticRequestOperatorPosture
    constraints: PaperSemanticRequestConstraints
    request_hash: str

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "PaperSemanticWorkerRequest":
        if self.title is not None:
            object.__setattr__(
                self, "title", _assert_non_empty_text(self.title, field_name="title")
            )
        object.__setattr__(
            self, "source_text", _assert_non_empty_text(self.source_text, field_name="source_text")
        )
        basis = self.model_dump(
            mode="json",
            by_alias=True,
            exclude={"request_id", "request_hash"},
            exclude_none=True,
        )
        expected_request_hash = sha256_canonical_json(basis)
        if self.request_hash != expected_request_hash:
            raise ValueError("request_hash must match canonical request payload")
        expected_request_id = compute_paper_request_id(self.request_hash)
        if self.request_id != expected_request_id:
            raise ValueError("request_id must match canonical request identity")
        return self


class PaperSemanticArtifact(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_PAPER_SEMANTIC_ARTIFACT_SCHEMA] = Field(
        default=ADEU_PAPER_SEMANTIC_ARTIFACT_SCHEMA,
        alias="schema",
    )
    artifact_id: str
    source: PaperSourceArtifact
    spans: list[PaperSourceSpan] = Field(min_length=1)
    claims: list[PaperSemanticClaim] = Field(min_length=1)
    lane_fragments: list[PaperSemanticLaneFragment] = Field(min_length=1)
    inference_bridges: list[PaperSemanticInferenceBridge] = Field(default_factory=list)
    diagnostics: list[PaperSemanticDiagnostic] = Field(default_factory=list)
    projections: list[PaperSemanticProjection] = Field(default_factory=list)
    source_authority_posture: Literal[SOURCE_AUTHORITY_POSTURE] = SOURCE_AUTHORITY_POSTURE
    interpretation_authority_posture: Literal[INTERPRETATION_AUTHORITY_POSTURE] = (
        INTERPRETATION_AUTHORITY_POSTURE
    )
    semantic_identity_mode: Literal[SEMANTIC_IDENTITY_MODE] = SEMANTIC_IDENTITY_MODE
    identity_field_names: list[IdentityFieldName] = Field(
        default_factory=lambda: list(IDENTITY_FIELD_NAMES)
    )
    projection_field_names: list[ProjectionFieldName] = Field(
        default_factory=lambda: list(PROJECTION_FIELD_NAMES)
    )
    semantic_hash: str

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "PaperSemanticArtifact":
        if tuple(self.identity_field_names) != IDENTITY_FIELD_NAMES:
            raise ValueError("identity_field_names must match the frozen V52-A identity law")
        if tuple(self.projection_field_names) != PROJECTION_FIELD_NAMES:
            raise ValueError("projection_field_names must match the frozen V52-A projection law")

        spans = sorted(self.spans, key=lambda item: (item.start, item.end, item.span_id))
        claims = sorted(self.claims, key=lambda item: item.claim_id)
        lane_fragments = sorted(
            self.lane_fragments, key=lambda item: (item.claim_id, item.lane_id, item.fragment_id)
        )
        inference_bridges = sorted(self.inference_bridges, key=lambda item: item.bridge_id)
        diagnostics = sorted(self.diagnostics, key=lambda item: item.diagnostic_id)
        projections = sorted(self.projections, key=lambda item: item.projection_id)

        for field_name, items, attr_name in (
            ("spans", spans, "span_id"),
            ("claims", claims, "claim_id"),
            ("lane_fragments", lane_fragments, "fragment_id"),
            ("inference_bridges", inference_bridges, "bridge_id"),
            ("diagnostics", diagnostics, "diagnostic_id"),
            ("projections", projections, "projection_id"),
        ):
            ids = [getattr(item, attr_name) for item in items]
            if len(ids) != len(set(ids)):
                raise ValueError(f"{field_name} must be unique by {attr_name}")

        object.__setattr__(self, "spans", spans)
        object.__setattr__(self, "claims", claims)
        object.__setattr__(self, "lane_fragments", lane_fragments)
        object.__setattr__(self, "inference_bridges", inference_bridges)
        object.__setattr__(self, "diagnostics", diagnostics)
        object.__setattr__(self, "projections", projections)

        source_text = self.source.source_text
        for span in self.spans:
            if span.end > len(source_text):
                raise ValueError("span end must not exceed source_text length")
            if source_text[span.start : span.end] != span.quote:
                raise ValueError("span quote must match the anchored source_text slice")
            if self.source.artifact_kind == "pasted.paragraph":
                if span.paragraph_index != self.source.paragraph_index:
                    raise ValueError("pasted.paragraph spans must match the source paragraph_index")

        span_ids = {item.span_id for item in self.spans}
        claim_ids = {item.claim_id for item in self.claims}
        fragment_ids = {item.fragment_id for item in self.lane_fragments}
        bridge_ids = {item.bridge_id for item in self.inference_bridges}
        diagnostic_ids = {item.diagnostic_id for item in self.diagnostics}

        for claim in self.claims:
            if not set(claim.span_ids).issubset(span_ids):
                raise ValueError("claim span_ids must resolve to released spans")
            if not set(claim.lane_fragment_ids).issubset(fragment_ids):
                raise ValueError("claim lane_fragment_ids must resolve to released fragments")

        for fragment in self.lane_fragments:
            if fragment.claim_id not in claim_ids:
                raise ValueError("fragment claim_id must resolve to a released claim")
            if not set(fragment.span_ids).issubset(span_ids):
                raise ValueError("fragment span_ids must resolve to released spans")
            if not set(fragment.bridge_ids).issubset(bridge_ids):
                raise ValueError("fragment bridge_ids must resolve to released bridges")
            if not set(fragment.diagnostic_ids).issubset(diagnostic_ids):
                raise ValueError("fragment diagnostic_ids must resolve to released diagnostics")

        for bridge in self.inference_bridges:
            if not set(bridge.from_fragment_ids).issubset(fragment_ids):
                raise ValueError("bridge from_fragment_ids must resolve to released fragments")
            if not set(bridge.to_fragment_ids).issubset(fragment_ids):
                raise ValueError("bridge to_fragment_ids must resolve to released fragments")
            if not set(bridge.diagnostic_ids).issubset(diagnostic_ids):
                raise ValueError("bridge diagnostic_ids must resolve to released diagnostics")

        for diagnostic in self.diagnostics:
            if not set(diagnostic.related_fragment_ids).issubset(fragment_ids):
                raise ValueError(
                    "diagnostic related_fragment_ids must resolve to released fragments"
                )
            if not set(diagnostic.span_ids).issubset(span_ids):
                raise ValueError("diagnostic span_ids must resolve to released spans")

        for projection in self.projections:
            if not set(projection.claim_order).issubset(claim_ids):
                raise ValueError("projection claim_order must resolve to released claims")
            if (
                projection.recommended_focus_claim_id is not None
                and projection.recommended_focus_claim_id not in claim_ids
            ):
                raise ValueError(
                    "projection recommended_focus_claim_id must resolve to a released claim"
                )

        basis = {
            "schema": self.schema,
            "source": self.source.identity_basis(),
            "spans": [item.identity_basis() for item in self.spans],
            "claims": [item.identity_basis() for item in self.claims],
            "lane_fragments": [item.identity_basis() for item in self.lane_fragments],
            "inference_bridges": [item.identity_basis() for item in self.inference_bridges],
            "source_authority_posture": self.source_authority_posture,
            "interpretation_authority_posture": self.interpretation_authority_posture,
            "semantic_identity_mode": self.semantic_identity_mode,
        }
        expected_semantic_hash = sha256_canonical_json(basis)
        if self.semantic_hash != expected_semantic_hash:
            raise ValueError("semantic_hash must match canonical artifact identity basis")
        expected_artifact_id = compute_paper_artifact_id(self.semantic_hash)
        if self.artifact_id != expected_artifact_id:
            raise ValueError("artifact_id must match canonical artifact identity")
        return self


__all__ = [
    "ADEU_PAPER_SEMANTIC_ARTIFACT_SCHEMA",
    "ADEU_PAPER_SEMANTIC_CLAIM_SCHEMA",
    "ADEU_PAPER_SEMANTIC_DIAGNOSTIC_SCHEMA",
    "ADEU_PAPER_SEMANTIC_INFERENCE_BRIDGE_SCHEMA",
    "ADEU_PAPER_SEMANTIC_LANE_FRAGMENT_SCHEMA",
    "ADEU_PAPER_SEMANTIC_PROJECTION_SCHEMA",
    "ADEU_PAPER_SEMANTIC_WORKER_REQUEST_SCHEMA",
    "ADEU_PAPER_SOURCE_ARTIFACT_SCHEMA",
    "ADEU_PAPER_SOURCE_SPAN_SCHEMA",
    "IDENTITY_FIELD_NAMES",
    "INTERPRETATION_AUTHORITY_POSTURE",
    "LANE_ORDER",
    "PROJECTION_FIELD_NAMES",
    "SEMANTIC_IDENTITY_MODE",
    "SOURCE_AUTHORITY_POSTURE",
    "PaperSemanticArtifact",
    "PaperSemanticClaim",
    "PaperSemanticDiagnostic",
    "PaperSemanticInferenceBridge",
    "PaperSemanticLaneFragment",
    "PaperSemanticProjection",
    "PaperSemanticRequestConstraints",
    "PaperSemanticRequestOperatorPosture",
    "PaperSemanticWorkerRequest",
    "PaperSourceArtifact",
    "PaperSourceSpan",
    "compute_paper_artifact_id",
    "compute_paper_request_id",
    "compute_paper_source_id",
]
