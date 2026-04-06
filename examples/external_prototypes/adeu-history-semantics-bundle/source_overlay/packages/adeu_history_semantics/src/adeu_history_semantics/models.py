from __future__ import annotations

from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from .hashing import canonical_json, sha256_canonical_json

ADEU_HISTORY_SOURCE_ARTIFACT_SCHEMA = "adeu_history_source_artifact@1"
ADEU_HISTORY_TEXT_SHAPE_SIGNALS_SCHEMA = "adeu_history_text_shape_signals@1"
ADEU_HISTORY_PRECLASSIFICATION_SCHEMA = "adeu_history_preclassification@1"
ADEU_HISTORY_LEDGER_ENTRY_SCHEMA = "adeu_history_ledger_entry@1"
ADEU_HISTORY_LEDGER_SCHEMA = "adeu_history_ledger@1"
ADEU_HISTORY_SLICE_SCHEMA = "adeu_history_slice@1"
ADEU_HISTORY_THEME_ANCHOR_SCHEMA = "adeu_history_theme_anchor@1"
ADEU_HISTORY_EVIDENCE_REF_SCHEMA = "adeu_history_evidence_ref@1"
ADEU_HISTORY_ODEU_LANE_RECONSTRUCTION_SCHEMA = "adeu_history_odeu_lane_reconstruction@1"
ADEU_HISTORY_ODEU_RECONSTRUCTION_PACKET_SCHEMA = "adeu_history_odeu_reconstruction_packet@1"
ADEU_HISTORY_WORKSPACE_QUESTION_SCHEMA = "adeu_history_workspace_question@1"
ADEU_HISTORY_WORKSPACE_THEME_FRAME_SCHEMA = "adeu_history_workspace_theme_frame@1"
ADEU_HISTORY_WORKSPACE_SNAPSHOT_SCHEMA = "adeu_history_workspace_snapshot@1"
ADEU_HISTORY_SEMANTIC_BUNDLE_SCHEMA = "adeu_history_semantic_bundle@1"

SOURCE_AUTHORITY_POSTURE = "raw_source_text_authoritative"
INTERPRETATION_AUTHORITY_POSTURE = "advisory_overlay_only"
THEME_SELECTION_POSTURE = "user_messages_first_order_when_available"
ASSISTANT_EXPLICATION_POSTURE = (
    "assistant_second_order_for_theme_first_order_for_explication_when_attached"
)
SEMANTIC_IDENTITY_MODE = "adeu_history_semantics_v0_hash_law"
LANE_ORDER = ("O", "E", "D", "U")
INFERENTIAL_MATURITY_ORDER = ("emergent", "developing", "explicit", "consolidated")

MODEL_CONFIG = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

InputKind = Literal["conversation_history", "abstract_like"]
RoleKind = Literal["user", "assistant", "system", "unknown"]
OriginType = Literal[
    "user_native",
    "assistant_reply",
    "system_instruction",
    "external_paste_like",
    "abstract_paragraph",
    "unclassified_block",
]
UnitKind = Literal["message", "abstract_paragraph", "conversation_block"]
SourceDeclarationHint = Literal[
    "timestamp_header_detected",
    "quote_marker_present",
    "code_fence_present",
    "url_present",
    "citation_marker_present",
    "external_source_phrase_present",
    "abstract_header_present",
]
StructuralMarker = Literal[
    "role_header_detected",
    "question_mark_present",
    "imperative_signal_present",
    "list_like_lines_present",
    "odeu_marker_present",
    "definition_pattern_present",
    "negation_guard_present",
]
CorpusWavePosture = Literal[
    "unassigned",
    "wave_0_bootstrap_candidate",
    "later_wave_candidate",
]
InferentialMaturityBand = Literal["emergent", "developing", "explicit", "consolidated"]
ThemeSelectionPosture = Literal["user_message_primary", "source_fallback_primary"]
LaneId = Literal["O", "E", "D", "U"]
LanePresenceStatus = Literal["present", "weakly_present", "underdetermined", "not_salient"]
LaneExplicitationStatus = Literal[
    "locally_explicit",
    "dialogically_explicitated",
    "contextually_reconstructed",
    "underdetermined",
]
DominantRolePosture = Literal[
    "user_primary",
    "assistant_explication",
    "mixed",
    "source_primary",
    "none",
]
WorkspaceQuestionReasonKind = Literal["weak_lane", "underdetermined_lane"]


def _assert_non_empty_text(value: str, *, field_name: str) -> str:
    normalized = value.strip()
    if not normalized:
        raise ValueError(f"{field_name} must be non-empty")
    return normalized


def _assert_non_negative_int(value: int, *, field_name: str) -> int:
    if value < 0:
        raise ValueError(f"{field_name} must be non-negative")
    return value


def _assert_positive_int(value: int, *, field_name: str) -> int:
    if value <= 0:
        raise ValueError(f"{field_name} must be positive")
    return value


def _ordered_unique(values: list[str]) -> list[str]:
    seen: set[str] = set()
    ordered: list[str] = []
    for value in values:
        if value not in seen:
            seen.add(value)
            ordered.append(value)
    return ordered


def _normalize_unique_texts(
    values: list[str], *, field_name: str, sort_values: bool = False
) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    ordered = _ordered_unique(normalized)
    return sorted(ordered) if sort_values else ordered


def _normalize_lane_ids(values: list[LaneId], *, field_name: str) -> list[LaneId]:
    normalized = list(values)
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must be unique")
    order = {lane: index for index, lane in enumerate(LANE_ORDER)}
    return sorted(normalized, key=lambda item: order[item])


def compute_source_text_hash(source_text: str) -> str:
    return sha256_canonical_json({"source_text": source_text})


def compute_history_source_id(*, input_kind: InputKind, source_text_hash: str) -> str:
    digest = sha256_canonical_json(
        {"input_kind": input_kind, "source_text_hash": source_text_hash}
    )
    return f"history_source:{digest[:16]}"


def compute_history_entry_text_hash(entry_text: str) -> str:
    return sha256_canonical_json({"entry_text": entry_text})


def compute_history_entry_id(
    *,
    source_id: str,
    unit_kind: UnitKind,
    order_index: int,
    entry_text_hash: str,
) -> str:
    digest = sha256_canonical_json(
        {
            "source_id": source_id,
            "unit_kind": unit_kind,
            "order_index": order_index,
            "entry_text_hash": entry_text_hash,
        }
    )
    return f"history_entry:{digest[:16]}"


def compute_history_ledger_id(*, source_id: str, entry_ids: list[str]) -> str:
    digest = sha256_canonical_json({"source_id": source_id, "entry_ids": entry_ids})
    return f"history_ledger:{digest[:16]}"


def compute_history_slice_id(
    *,
    source_id: str,
    slice_index: int,
    primary_entry_ids: list[str],
    support_entry_ids: list[str],
) -> str:
    digest = sha256_canonical_json(
        {
            "source_id": source_id,
            "slice_index": slice_index,
            "primary_entry_ids": primary_entry_ids,
            "support_entry_ids": support_entry_ids,
        }
    )
    return f"history_slice:{digest[:16]}"


def compute_theme_key(anchor_terms: list[str]) -> str:
    normalized = _normalize_unique_texts(anchor_terms, field_name="anchor_terms")
    return "__".join(normalized[:3]) if normalized else "untitled_theme"


def compute_history_theme_anchor_id(
    *,
    source_id: str,
    theme_key: str,
    primary_entry_ids: list[str],
    slice_ids: list[str],
) -> str:
    digest = sha256_canonical_json(
        {
            "source_id": source_id,
            "theme_key": theme_key,
            "primary_entry_ids": primary_entry_ids,
            "slice_ids": slice_ids,
        }
    )
    return f"history_theme:{digest[:16]}"


class HistoryTextShapeSignals(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_HISTORY_TEXT_SHAPE_SIGNALS_SCHEMA] = Field(
        default=ADEU_HISTORY_TEXT_SHAPE_SIGNALS_SCHEMA,
        alias="schema",
    )
    char_count: int
    word_count: int
    sentence_count: int
    line_count: int
    question_count: int
    bullet_line_count: int
    quoted_line_count: int
    code_fence_count: int

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "HistoryTextShapeSignals":
        for field_name in (
            "char_count",
            "word_count",
            "sentence_count",
            "line_count",
            "question_count",
            "bullet_line_count",
            "quoted_line_count",
            "code_fence_count",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_negative_int(getattr(self, field_name), field_name=field_name),
            )
        return self


class HistoryPreclassification(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_HISTORY_PRECLASSIFICATION_SCHEMA] = Field(
        default=ADEU_HISTORY_PRECLASSIFICATION_SCHEMA,
        alias="schema",
    )
    role: RoleKind
    origin_type: OriginType
    source_declaration_hints: list[SourceDeclarationHint] = Field(default_factory=list)
    timestamp_text: str | None = None
    structural_markers: list[StructuralMarker] = Field(default_factory=list)
    text_shape_signals: HistoryTextShapeSignals
    local_group_id: str
    suggested_slice_boundary_before: bool = False
    order_index: int

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "HistoryPreclassification":
        object.__setattr__(
            self,
            "source_declaration_hints",
            _normalize_unique_texts(
                list(self.source_declaration_hints),
                field_name="source_declaration_hints",
                sort_values=True,
            ),
        )
        object.__setattr__(
            self,
            "structural_markers",
            _normalize_unique_texts(
                list(self.structural_markers),
                field_name="structural_markers",
                sort_values=True,
            ),
        )
        object.__setattr__(
            self,
            "local_group_id",
            _assert_non_empty_text(self.local_group_id, field_name="local_group_id"),
        )
        object.__setattr__(
            self,
            "order_index",
            _assert_non_negative_int(self.order_index, field_name="order_index"),
        )
        if self.timestamp_text is not None:
            object.__setattr__(
                self,
                "timestamp_text",
                _assert_non_empty_text(self.timestamp_text, field_name="timestamp_text"),
            )
        return self


class HistorySourceArtifact(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_HISTORY_SOURCE_ARTIFACT_SCHEMA] = Field(
        default=ADEU_HISTORY_SOURCE_ARTIFACT_SCHEMA,
        alias="schema",
    )
    source_id: str
    input_kind: InputKind
    source_label: str
    source_text: str
    source_text_hash: str
    corpus_wave_posture: CorpusWavePosture = "unassigned"
    source_authority_posture: Literal[SOURCE_AUTHORITY_POSTURE] = SOURCE_AUTHORITY_POSTURE
    source_notes: list[str] = Field(default_factory=list)

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "HistorySourceArtifact":
        object.__setattr__(
            self,
            "source_label",
            _assert_non_empty_text(self.source_label, field_name="source_label"),
        )
        object.__setattr__(
            self,
            "source_text",
            self.source_text.replace("\r\n", "\n").replace("\r", "\n"),
        )
        object.__setattr__(
            self,
            "source_notes",
            _normalize_unique_texts(self.source_notes, field_name="source_notes", sort_values=True),
        )
        expected_source_text_hash = compute_source_text_hash(self.source_text)
        if self.source_text_hash != expected_source_text_hash:
            raise ValueError("source_text_hash must match source_text")
        expected_source_id = compute_history_source_id(
            input_kind=self.input_kind,
            source_text_hash=self.source_text_hash,
        )
        if self.source_id != expected_source_id:
            raise ValueError("source_id must match canonical source identity")
        return self

    def identity_basis(self) -> dict[str, object]:
        return {
            "input_kind": self.input_kind,
            "source_text_hash": self.source_text_hash,
        }


class HistoryLedgerEntry(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_HISTORY_LEDGER_ENTRY_SCHEMA] = Field(
        default=ADEU_HISTORY_LEDGER_ENTRY_SCHEMA,
        alias="schema",
    )
    entry_id: str
    source_id: str
    unit_kind: UnitKind
    entry_text: str
    entry_text_hash: str
    source_line_start: int
    source_line_end: int
    preclassification: HistoryPreclassification

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "HistoryLedgerEntry":
        object.__setattr__(
            self,
            "entry_text",
            _assert_non_empty_text(self.entry_text, field_name="entry_text"),
        )
        object.__setattr__(
            self,
            "source_line_start",
            _assert_positive_int(self.source_line_start, field_name="source_line_start"),
        )
        object.__setattr__(
            self,
            "source_line_end",
            _assert_positive_int(self.source_line_end, field_name="source_line_end"),
        )
        if self.source_line_end < self.source_line_start:
            raise ValueError("source_line_end must be >= source_line_start")
        expected_text_hash = compute_history_entry_text_hash(self.entry_text)
        if self.entry_text_hash != expected_text_hash:
            raise ValueError("entry_text_hash must match entry_text")
        expected_entry_id = compute_history_entry_id(
            source_id=self.source_id,
            unit_kind=self.unit_kind,
            order_index=self.preclassification.order_index,
            entry_text_hash=self.entry_text_hash,
        )
        if self.entry_id != expected_entry_id:
            raise ValueError("entry_id must match canonical entry identity")
        if (
            self.unit_kind == "abstract_paragraph"
            and self.preclassification.origin_type != "abstract_paragraph"
        ):
            raise ValueError(
                "abstract_paragraph entries require abstract_paragraph origin_type"
            )
        return self


class HistoryLedger(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_HISTORY_LEDGER_SCHEMA] = Field(
        default=ADEU_HISTORY_LEDGER_SCHEMA,
        alias="schema",
    )
    ledger_id: str
    source_id: str
    input_kind: InputKind
    entries: list[HistoryLedgerEntry]
    entry_count: int

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "HistoryLedger":
        ordered_entries = sorted(
            self.entries,
            key=lambda entry: entry.preclassification.order_index,
        )
        object.__setattr__(self, "entries", ordered_entries)
        object.__setattr__(
            self,
            "entry_count",
            _assert_non_negative_int(self.entry_count, field_name="entry_count"),
        )
        if self.entry_count != len(self.entries):
            raise ValueError("entry_count must match entries")
        for entry in self.entries:
            if entry.source_id != self.source_id:
                raise ValueError("all ledger entries must reference the ledger source_id")
        entry_ids = [entry.entry_id for entry in self.entries]
        if len(entry_ids) != len(set(entry_ids)):
            raise ValueError("ledger entries must be unique")
        expected_ledger_id = compute_history_ledger_id(
            source_id=self.source_id,
            entry_ids=entry_ids,
        )
        if self.ledger_id != expected_ledger_id:
            raise ValueError("ledger_id must match canonical ledger identity")
        return self


class HistorySlice(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_HISTORY_SLICE_SCHEMA] = Field(
        default=ADEU_HISTORY_SLICE_SCHEMA,
        alias="schema",
    )
    slice_id: str
    source_id: str
    slice_index: int
    primary_entry_ids: list[str]
    support_entry_ids: list[str] = Field(default_factory=list)
    chronology_start_index: int
    chronology_end_index: int
    suggested_theme_terms: list[str]
    suggested_theme_label: str
    inferential_maturity_score: int
    inferential_maturity_band: InferentialMaturityBand
    slice_notes: list[str] = Field(default_factory=list)

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "HistorySlice":
        object.__setattr__(
            self,
            "slice_index",
            _assert_non_negative_int(self.slice_index, field_name="slice_index"),
        )
        object.__setattr__(
            self,
            "primary_entry_ids",
            _normalize_unique_texts(self.primary_entry_ids, field_name="primary_entry_ids"),
        )
        if not self.primary_entry_ids:
            raise ValueError("primary_entry_ids must be non-empty")
        object.__setattr__(
            self,
            "support_entry_ids",
            _normalize_unique_texts(self.support_entry_ids, field_name="support_entry_ids"),
        )
        object.__setattr__(
            self,
            "suggested_theme_terms",
            _normalize_unique_texts(
                self.suggested_theme_terms,
                field_name="suggested_theme_terms",
            ),
        )
        if not self.suggested_theme_terms:
            raise ValueError("suggested_theme_terms must be non-empty")
        object.__setattr__(
            self,
            "suggested_theme_label",
            _assert_non_empty_text(self.suggested_theme_label, field_name="suggested_theme_label"),
        )
        object.__setattr__(
            self,
            "chronology_start_index",
            _assert_non_negative_int(
                self.chronology_start_index,
                field_name="chronology_start_index",
            ),
        )
        object.__setattr__(
            self,
            "chronology_end_index",
            _assert_non_negative_int(self.chronology_end_index, field_name="chronology_end_index"),
        )
        if self.chronology_end_index < self.chronology_start_index:
            raise ValueError("chronology_end_index must be >= chronology_start_index")
        object.__setattr__(
            self,
            "inferential_maturity_score",
            _assert_non_negative_int(
                self.inferential_maturity_score,
                field_name="inferential_maturity_score",
            ),
        )
        object.__setattr__(
            self,
            "slice_notes",
            _normalize_unique_texts(self.slice_notes, field_name="slice_notes", sort_values=True),
        )
        expected_slice_id = compute_history_slice_id(
            source_id=self.source_id,
            slice_index=self.slice_index,
            primary_entry_ids=self.primary_entry_ids,
            support_entry_ids=self.support_entry_ids,
        )
        if self.slice_id != expected_slice_id:
            raise ValueError("slice_id must match canonical slice identity")
        return self


class HistoryThemeAnchor(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_HISTORY_THEME_ANCHOR_SCHEMA] = Field(
        default=ADEU_HISTORY_THEME_ANCHOR_SCHEMA,
        alias="schema",
    )
    theme_anchor_id: str
    source_id: str
    theme_key: str
    display_label: str
    selection_posture: ThemeSelectionPosture
    anchor_terms: list[str]
    primary_entry_ids: list[str]
    support_entry_ids: list[str] = Field(default_factory=list)
    slice_ids: list[str]

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "HistoryThemeAnchor":
        object.__setattr__(
            self,
            "display_label",
            _assert_non_empty_text(self.display_label, field_name="display_label"),
        )
        object.__setattr__(
            self,
            "anchor_terms",
            _normalize_unique_texts(self.anchor_terms, field_name="anchor_terms"),
        )
        if not self.anchor_terms:
            raise ValueError("anchor_terms must be non-empty")
        object.__setattr__(
            self,
            "primary_entry_ids",
            _normalize_unique_texts(self.primary_entry_ids, field_name="primary_entry_ids"),
        )
        if not self.primary_entry_ids:
            raise ValueError("primary_entry_ids must be non-empty")
        object.__setattr__(
            self,
            "support_entry_ids",
            _normalize_unique_texts(self.support_entry_ids, field_name="support_entry_ids"),
        )
        object.__setattr__(
            self,
            "slice_ids",
            _normalize_unique_texts(self.slice_ids, field_name="slice_ids"),
        )
        if not self.slice_ids:
            raise ValueError("slice_ids must be non-empty")
        expected_theme_key = compute_theme_key(self.anchor_terms)
        if self.theme_key != expected_theme_key:
            raise ValueError("theme_key must match anchor_terms")
        expected_anchor_id = compute_history_theme_anchor_id(
            source_id=self.source_id,
            theme_key=self.theme_key,
            primary_entry_ids=self.primary_entry_ids,
            slice_ids=self.slice_ids,
        )
        if self.theme_anchor_id != expected_anchor_id:
            raise ValueError("theme_anchor_id must match canonical theme identity")
        return self


class HistoryEvidenceRef(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_HISTORY_EVIDENCE_REF_SCHEMA] = Field(
        default=ADEU_HISTORY_EVIDENCE_REF_SCHEMA,
        alias="schema",
    )
    entry_id: str
    role: RoleKind
    excerpt: str

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "HistoryEvidenceRef":
        object.__setattr__(
            self,
            "entry_id",
            _assert_non_empty_text(self.entry_id, field_name="entry_id"),
        )
        object.__setattr__(
            self,
            "excerpt",
            _assert_non_empty_text(self.excerpt, field_name="excerpt"),
        )
        return self


class HistoryODEULaneReconstruction(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_HISTORY_ODEU_LANE_RECONSTRUCTION_SCHEMA] = Field(
        default=ADEU_HISTORY_ODEU_LANE_RECONSTRUCTION_SCHEMA,
        alias="schema",
    )
    lane_id: LaneId
    presence_status: LanePresenceStatus
    explicitation_status: LaneExplicitationStatus
    dominant_role_posture: DominantRolePosture
    reconstruction_text: str | None = None
    evidence_refs: list[HistoryEvidenceRef] = Field(default_factory=list)

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "HistoryODEULaneReconstruction":
        deduped_refs = _ordered_unique(
            [
                canonical_json(item.model_dump(mode="json", by_alias=True))
                for item in self.evidence_refs
            ]
        )
        evidence_refs = [HistoryEvidenceRef.model_validate_json(value) for value in deduped_refs]
        object.__setattr__(self, "evidence_refs", evidence_refs)
        if self.reconstruction_text is not None:
            object.__setattr__(
                self,
                "reconstruction_text",
                _assert_non_empty_text(self.reconstruction_text, field_name="reconstruction_text"),
            )
        if self.presence_status in {"present", "weakly_present"}:
            if self.reconstruction_text is None:
                raise ValueError("present or weakly_present lanes require reconstruction_text")
            if not self.evidence_refs:
                raise ValueError("present or weakly_present lanes require evidence_refs")
        if self.presence_status in {"underdetermined", "not_salient"} and self.evidence_refs:
            raise ValueError("absent lanes may not carry evidence_refs")
        if self.presence_status in {"underdetermined", "not_salient"}:
            if self.explicitation_status != "underdetermined":
                raise ValueError("absent lanes must use explicitation_status=underdetermined")
            if self.dominant_role_posture != "none":
                raise ValueError("absent lanes must use dominant_role_posture=none")
        return self


class HistoryODEUReconstructionPacket(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_HISTORY_ODEU_RECONSTRUCTION_PACKET_SCHEMA] = Field(
        default=ADEU_HISTORY_ODEU_RECONSTRUCTION_PACKET_SCHEMA,
        alias="schema",
    )
    packet_id: str
    source_id: str
    slice_id: str
    theme_anchor_id: str
    lane_reconstructions: list[HistoryODEULaneReconstruction]
    reintegrated_summary: str | None = None
    interpretation_authority_posture: Literal[INTERPRETATION_AUTHORITY_POSTURE] = (
        INTERPRETATION_AUTHORITY_POSTURE
    )
    semantic_identity_mode: Literal[SEMANTIC_IDENTITY_MODE] = SEMANTIC_IDENTITY_MODE
    semantic_hash: str

    @property
    def schema(self) -> str:
        return self.schema_id

    def identity_basis(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "source_id": self.source_id,
            "slice_id": self.slice_id,
            "theme_anchor_id": self.theme_anchor_id,
            "lane_reconstructions": [
                {
                    "lane_id": lane.lane_id,
                    "presence_status": lane.presence_status,
                    "explicitation_status": lane.explicitation_status,
                    "dominant_role_posture": lane.dominant_role_posture,
                    "reconstruction_text": lane.reconstruction_text,
                    "evidence_refs": [
                        {
                            "entry_id": item.entry_id,
                            "role": item.role,
                            "excerpt": item.excerpt,
                        }
                        for item in lane.evidence_refs
                    ],
                }
                for lane in self.lane_reconstructions
            ],
            "reintegrated_summary": self.reintegrated_summary,
            "semantic_identity_mode": self.semantic_identity_mode,
        }

    @model_validator(mode="after")
    def _validate(self) -> "HistoryODEUReconstructionPacket":
        order = {lane: index for index, lane in enumerate(LANE_ORDER)}
        normalized_lanes = sorted(self.lane_reconstructions, key=lambda item: order[item.lane_id])
        if [item.lane_id for item in normalized_lanes] != list(LANE_ORDER):
            raise ValueError("lane_reconstructions must contain exactly one O/E/D/U lane")
        object.__setattr__(self, "lane_reconstructions", normalized_lanes)
        if self.reintegrated_summary is not None:
            object.__setattr__(
                self,
                "reintegrated_summary",
                _assert_non_empty_text(
                    self.reintegrated_summary,
                    field_name="reintegrated_summary",
                ),
            )
        expected_semantic_hash = sha256_canonical_json(self.identity_basis())
        if self.semantic_hash != expected_semantic_hash:
            raise ValueError("semantic_hash must match canonical packet identity basis")
        expected_packet_id = f"history_packet:{self.semantic_hash[:16]}"
        if self.packet_id != expected_packet_id:
            raise ValueError("packet_id must match canonical packet identity")
        return self


class HistoryWorkspaceQuestion(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_HISTORY_WORKSPACE_QUESTION_SCHEMA] = Field(
        default=ADEU_HISTORY_WORKSPACE_QUESTION_SCHEMA,
        alias="schema",
    )
    question_id: str
    lane_id: LaneId
    reason_kind: WorkspaceQuestionReasonKind
    question_text: str

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "HistoryWorkspaceQuestion":
        object.__setattr__(
            self,
            "question_text",
            _assert_non_empty_text(self.question_text, field_name="question_text"),
        )
        basis = {
            "lane_id": self.lane_id,
            "reason_kind": self.reason_kind,
            "question_text": self.question_text,
        }
        expected_question_id = f"history_question:{sha256_canonical_json(basis)[:16]}"
        if self.question_id != expected_question_id:
            raise ValueError("question_id must match canonical workspace question identity")
        return self


class HistoryWorkspaceThemeFrame(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_HISTORY_WORKSPACE_THEME_FRAME_SCHEMA] = Field(
        default=ADEU_HISTORY_WORKSPACE_THEME_FRAME_SCHEMA,
        alias="schema",
    )
    frame_id: str
    theme_anchor_id: str
    theme_display_label: str
    slice_ids: list[str]
    packet_ids: list[str]
    chronology_start_index: int
    chronology_end_index: int
    inferential_maturity_band: InferentialMaturityBand
    underdeveloped_lane_ids: list[LaneId] = Field(default_factory=list)
    provenance_entry_ids: list[str] = Field(default_factory=list)
    open_questions: list[HistoryWorkspaceQuestion] = Field(default_factory=list)

    @property
    def schema(self) -> str:
        return self.schema_id

    def identity_basis(self) -> dict[str, object]:
        return {
            "theme_anchor_id": self.theme_anchor_id,
            "slice_ids": self.slice_ids,
            "packet_ids": self.packet_ids,
            "chronology_start_index": self.chronology_start_index,
            "chronology_end_index": self.chronology_end_index,
            "inferential_maturity_band": self.inferential_maturity_band,
            "underdeveloped_lane_ids": self.underdeveloped_lane_ids,
            "provenance_entry_ids": self.provenance_entry_ids,
            "open_questions": [
                {
                    "lane_id": question.lane_id,
                    "reason_kind": question.reason_kind,
                    "question_text": question.question_text,
                }
                for question in self.open_questions
            ],
        }

    @model_validator(mode="after")
    def _validate(self) -> "HistoryWorkspaceThemeFrame":
        object.__setattr__(
            self,
            "theme_anchor_id",
            _assert_non_empty_text(self.theme_anchor_id, field_name="theme_anchor_id"),
        )
        object.__setattr__(
            self,
            "theme_display_label",
            _assert_non_empty_text(self.theme_display_label, field_name="theme_display_label"),
        )
        object.__setattr__(
            self,
            "slice_ids",
            _normalize_unique_texts(self.slice_ids, field_name="slice_ids"),
        )
        object.__setattr__(
            self,
            "packet_ids",
            _normalize_unique_texts(self.packet_ids, field_name="packet_ids"),
        )
        object.__setattr__(
            self,
            "provenance_entry_ids",
            _normalize_unique_texts(self.provenance_entry_ids, field_name="provenance_entry_ids"),
        )
        object.__setattr__(
            self,
            "underdeveloped_lane_ids",
            _normalize_lane_ids(self.underdeveloped_lane_ids, field_name="underdeveloped_lane_ids"),
        )
        object.__setattr__(
            self,
            "chronology_start_index",
            _assert_non_negative_int(
                self.chronology_start_index,
                field_name="chronology_start_index",
            ),
        )
        object.__setattr__(
            self,
            "chronology_end_index",
            _assert_non_negative_int(self.chronology_end_index, field_name="chronology_end_index"),
        )
        if self.chronology_end_index < self.chronology_start_index:
            raise ValueError("chronology_end_index must be >= chronology_start_index")
        expected_frame_id = f"history_frame:{sha256_canonical_json(self.identity_basis())[:16]}"
        if self.frame_id != expected_frame_id:
            raise ValueError("frame_id must match canonical frame identity")
        return self


class HistoryWorkspaceSnapshot(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_HISTORY_WORKSPACE_SNAPSHOT_SCHEMA] = Field(
        default=ADEU_HISTORY_WORKSPACE_SNAPSHOT_SCHEMA,
        alias="schema",
    )
    workspace_snapshot_id: str
    source_id: str
    ledger_id: str
    chronology_slice_order: list[str]
    inferential_slice_order: list[str]
    theme_frames: list[HistoryWorkspaceThemeFrame]
    lane_order: list[LaneId] = Field(default_factory=lambda: list(LANE_ORDER))
    source_authority_posture: Literal[SOURCE_AUTHORITY_POSTURE] = SOURCE_AUTHORITY_POSTURE
    interpretation_authority_posture: Literal[INTERPRETATION_AUTHORITY_POSTURE] = (
        INTERPRETATION_AUTHORITY_POSTURE
    )
    theme_selection_posture: Literal[THEME_SELECTION_POSTURE] = THEME_SELECTION_POSTURE
    assistant_explication_posture: Literal[ASSISTANT_EXPLICATION_POSTURE] = (
        ASSISTANT_EXPLICATION_POSTURE
    )
    semantic_identity_mode: Literal[SEMANTIC_IDENTITY_MODE] = SEMANTIC_IDENTITY_MODE
    semantic_hash: str

    @property
    def schema(self) -> str:
        return self.schema_id

    def identity_basis(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "source_id": self.source_id,
            "ledger_id": self.ledger_id,
            "chronology_slice_order": self.chronology_slice_order,
            "inferential_slice_order": self.inferential_slice_order,
            "theme_frames": [
                {
                    "theme_anchor_id": frame.theme_anchor_id,
                    "slice_ids": frame.slice_ids,
                    "packet_ids": frame.packet_ids,
                    "chronology_start_index": frame.chronology_start_index,
                    "chronology_end_index": frame.chronology_end_index,
                    "inferential_maturity_band": frame.inferential_maturity_band,
                    "underdeveloped_lane_ids": frame.underdeveloped_lane_ids,
                    "provenance_entry_ids": frame.provenance_entry_ids,
                    "open_questions": [
                        {
                            "lane_id": question.lane_id,
                            "reason_kind": question.reason_kind,
                            "question_text": question.question_text,
                        }
                        for question in frame.open_questions
                    ],
                }
                for frame in self.theme_frames
            ],
            "lane_order": self.lane_order,
            "semantic_identity_mode": self.semantic_identity_mode,
        }

    @model_validator(mode="after")
    def _validate(self) -> "HistoryWorkspaceSnapshot":
        object.__setattr__(
            self,
            "chronology_slice_order",
            _normalize_unique_texts(
                self.chronology_slice_order,
                field_name="chronology_slice_order",
            ),
        )
        object.__setattr__(
            self,
            "inferential_slice_order",
            _normalize_unique_texts(
                self.inferential_slice_order,
                field_name="inferential_slice_order",
            ),
        )
        object.__setattr__(
            self,
            "lane_order",
            _normalize_lane_ids(self.lane_order, field_name="lane_order"),
        )
        ordered_frames = sorted(self.theme_frames, key=lambda frame: frame.theme_anchor_id)
        object.__setattr__(self, "theme_frames", ordered_frames)
        expected_semantic_hash = sha256_canonical_json(self.identity_basis())
        if self.semantic_hash != expected_semantic_hash:
            raise ValueError("semantic_hash must match canonical workspace identity basis")
        expected_snapshot_id = f"history_workspace:{self.semantic_hash[:16]}"
        if self.workspace_snapshot_id != expected_snapshot_id:
            raise ValueError("workspace_snapshot_id must match canonical workspace identity")
        return self


class HistorySemanticBundle(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_HISTORY_SEMANTIC_BUNDLE_SCHEMA] = Field(
        default=ADEU_HISTORY_SEMANTIC_BUNDLE_SCHEMA,
        alias="schema",
    )
    bundle_id: str
    compiler_version: str
    source: HistorySourceArtifact
    ledger: HistoryLedger
    slices: list[HistorySlice]
    theme_anchors: list[HistoryThemeAnchor]
    reconstruction_packets: list[HistoryODEUReconstructionPacket]
    workspace_snapshot: HistoryWorkspaceSnapshot

    @property
    def schema(self) -> str:
        return self.schema_id

    def identity_basis(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "compiler_version": self.compiler_version,
            "source_id": self.source.source_id,
            "ledger_id": self.ledger.ledger_id,
            "slice_ids": [item.slice_id for item in self.slices],
            "theme_anchor_ids": [item.theme_anchor_id for item in self.theme_anchors],
            "packet_ids": [item.packet_id for item in self.reconstruction_packets],
            "workspace_snapshot_id": self.workspace_snapshot.workspace_snapshot_id,
        }

    @model_validator(mode="after")
    def _validate(self) -> "HistorySemanticBundle":
        object.__setattr__(
            self,
            "compiler_version",
            _assert_non_empty_text(self.compiler_version, field_name="compiler_version"),
        )
        ordered_slices = sorted(self.slices, key=lambda item: item.slice_index)
        object.__setattr__(self, "slices", ordered_slices)
        ordered_anchors = sorted(self.theme_anchors, key=lambda item: item.theme_key)
        object.__setattr__(self, "theme_anchors", ordered_anchors)
        ordered_packets = sorted(self.reconstruction_packets, key=lambda item: item.slice_id)
        object.__setattr__(self, "reconstruction_packets", ordered_packets)
        if self.ledger.source_id != self.source.source_id:
            raise ValueError("ledger.source_id must match source.source_id")
        if self.workspace_snapshot.source_id != self.source.source_id:
            raise ValueError("workspace_snapshot.source_id must match source.source_id")
        if self.workspace_snapshot.ledger_id != self.ledger.ledger_id:
            raise ValueError("workspace_snapshot.ledger_id must match ledger.ledger_id")
        entry_ids = {entry.entry_id for entry in self.ledger.entries}
        slice_ids = {item.slice_id for item in self.slices}
        theme_anchor_ids = {item.theme_anchor_id for item in self.theme_anchors}
        packet_ids = {item.packet_id for item in self.reconstruction_packets}
        for item in self.slices:
            if any(
                entry_id not in entry_ids
                for entry_id in item.primary_entry_ids + item.support_entry_ids
            ):
                raise ValueError("slice entry references must resolve into the ledger")
        for item in self.theme_anchors:
            if any(
                entry_id not in entry_ids
                for entry_id in item.primary_entry_ids + item.support_entry_ids
            ):
                raise ValueError(
                    "theme anchor entry references must resolve into the ledger"
                )
            if any(slice_id not in slice_ids for slice_id in item.slice_ids):
                raise ValueError("theme anchor slice references must resolve")
        for packet in self.reconstruction_packets:
            if packet.slice_id not in slice_ids:
                raise ValueError("packet slice_id must resolve")
            if packet.theme_anchor_id not in theme_anchor_ids:
                raise ValueError("packet theme_anchor_id must resolve")
            for lane in packet.lane_reconstructions:
                if any(ref.entry_id not in entry_ids for ref in lane.evidence_refs):
                    raise ValueError("packet evidence refs must resolve into the ledger")
        for frame in self.workspace_snapshot.theme_frames:
            if frame.theme_anchor_id not in theme_anchor_ids:
                raise ValueError("workspace theme frame must resolve a theme anchor")
            if any(slice_id not in slice_ids for slice_id in frame.slice_ids):
                raise ValueError("workspace theme frame slice_ids must resolve")
            if any(packet_id not in packet_ids for packet_id in frame.packet_ids):
                raise ValueError("workspace theme frame packet_ids must resolve")
            if any(entry_id not in entry_ids for entry_id in frame.provenance_entry_ids):
                raise ValueError("workspace theme frame provenance entries must resolve")
        expected_bundle_id = f"history_bundle:{sha256_canonical_json(self.identity_basis())[:16]}"
        if self.bundle_id != expected_bundle_id:
            raise ValueError("bundle_id must match canonical bundle identity")
        return self


__all__ = [
    "ADEU_HISTORY_EVIDENCE_REF_SCHEMA",
    "ADEU_HISTORY_LEDGER_ENTRY_SCHEMA",
    "ADEU_HISTORY_LEDGER_SCHEMA",
    "ADEU_HISTORY_ODEU_LANE_RECONSTRUCTION_SCHEMA",
    "ADEU_HISTORY_ODEU_RECONSTRUCTION_PACKET_SCHEMA",
    "ADEU_HISTORY_PRECLASSIFICATION_SCHEMA",
    "ADEU_HISTORY_SEMANTIC_BUNDLE_SCHEMA",
    "ADEU_HISTORY_SLICE_SCHEMA",
    "ADEU_HISTORY_SOURCE_ARTIFACT_SCHEMA",
    "ADEU_HISTORY_TEXT_SHAPE_SIGNALS_SCHEMA",
    "ADEU_HISTORY_THEME_ANCHOR_SCHEMA",
    "ADEU_HISTORY_WORKSPACE_QUESTION_SCHEMA",
    "ADEU_HISTORY_WORKSPACE_SNAPSHOT_SCHEMA",
    "ADEU_HISTORY_WORKSPACE_THEME_FRAME_SCHEMA",
    "ASSISTANT_EXPLICATION_POSTURE",
    "INTERPRETATION_AUTHORITY_POSTURE",
    "LANE_ORDER",
    "SEMANTIC_IDENTITY_MODE",
    "SOURCE_AUTHORITY_POSTURE",
    "THEME_SELECTION_POSTURE",
    "HistoryEvidenceRef",
    "HistoryLedger",
    "HistoryLedgerEntry",
    "HistoryODEULaneReconstruction",
    "HistoryODEUReconstructionPacket",
    "HistoryPreclassification",
    "HistorySemanticBundle",
    "HistorySlice",
    "HistorySourceArtifact",
    "HistoryTextShapeSignals",
    "HistoryThemeAnchor",
    "HistoryWorkspaceQuestion",
    "HistoryWorkspaceSnapshot",
    "HistoryWorkspaceThemeFrame",
    "canonical_json",
    "compute_history_entry_id",
    "compute_history_entry_text_hash",
    "compute_history_ledger_id",
    "compute_history_slice_id",
    "compute_history_source_id",
    "compute_history_theme_anchor_id",
    "compute_source_text_hash",
    "compute_theme_key",
    "sha256_canonical_json",
]
