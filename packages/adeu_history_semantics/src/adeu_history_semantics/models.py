from __future__ import annotations

import re
from datetime import datetime
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import canonical_json, sha256_canonical_json

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

SOURCE_AUTHORITY_POSTURE = "normalized_source_text_authoritative"
HISTORY_ODEU_INTERPRETATION_AUTHORITY_POSTURE = "advisory_overlay_only"
HISTORY_ODEU_PACKET_SEMANTIC_IDENTITY_MODE = "v54c_history_packet_hash_law"
INPUT_KIND_VOCABULARY = ("conversation_history",)
ROLE_VOCABULARY = ("user", "assistant", "system")
ORIGIN_TYPE_VOCABULARY = ("user_native", "assistant_reply", "system_instruction")
CORPUS_WAVE_POSTURE_VOCABULARY = (
    "unassigned",
    "wave_0_bootstrap_candidate",
    "later_wave_candidate",
)
SOURCE_DECLARATION_HINT_VOCABULARY = (
    "full_role_header_present",
    "timestamp_prefix_present",
    "timestamp_prefix_absent",
)
STRUCTURAL_MARKER_VOCABULARY = (
    "single_line_message",
    "multi_line_message",
    "blank_line_present",
    "bullet_line_present",
    "quoted_line_present",
    "code_fence_present",
    "question_mark_present",
)
ODEU_LANE_ORDER = ("O", "E", "D", "U")
LANE_PRESENCE_STATUS_VOCABULARY = (
    "present",
    "weakly_present",
    "underdetermined",
    "not_salient",
)
LANE_EXPLICATION_STATUS_VOCABULARY = (
    "locally_explicit",
    "dialogically_explicitated",
    "contextually_reconstructed",
    "underdetermined",
)
DOMINANT_ROLE_POSTURE_VOCABULARY = (
    "user_primary",
    "assistant_explication",
    "mixed",
    "source_primary",
    "none",
)
SLICE_BOUNDARY_TAG_VOCABULARY = (
    "conversation_start",
    "conversation_end",
    "contains_multi_line_message",
    "contains_blank_line_present",
    "contains_bullet_line_present",
    "contains_quoted_line_present",
    "contains_code_fence_present",
    "contains_question_mark_present",
)
ROLE_TO_ORIGIN_TYPE = {
    "user": "user_native",
    "assistant": "assistant_reply",
    "system": "system_instruction",
}

MODEL_CONFIG = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

InputKind = Literal["conversation_history"]
SourceAuthorityPosture = Literal["normalized_source_text_authoritative"]
RoleKind = Literal["user", "assistant", "system"]
OriginType = Literal["user_native", "assistant_reply", "system_instruction"]
CorpusWavePosture = Literal[
    "unassigned",
    "wave_0_bootstrap_candidate",
    "later_wave_candidate",
]
SourceDeclarationHint = Literal[
    "full_role_header_present",
    "timestamp_prefix_present",
    "timestamp_prefix_absent",
]
StructuralMarker = Literal[
    "single_line_message",
    "multi_line_message",
    "blank_line_present",
    "bullet_line_present",
    "quoted_line_present",
    "code_fence_present",
    "question_mark_present",
]
SliceBoundaryTag = Literal[
    "conversation_start",
    "conversation_end",
    "contains_multi_line_message",
    "contains_blank_line_present",
    "contains_bullet_line_present",
    "contains_quoted_line_present",
    "contains_code_fence_present",
    "contains_question_mark_present",
]
LaneId = Literal["O", "E", "D", "U"]
LanePresenceStatus = Literal[
    "present",
    "weakly_present",
    "underdetermined",
    "not_salient",
]
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
HistoryODEUInterpretationAuthorityPosture = Literal["advisory_overlay_only"]
HistoryODEUPacketSemanticIdentityMode = Literal["v54c_history_packet_hash_law"]

_THEME_TERM_RE = re.compile(r"^[a-z0-9]+$")


def _assert_present_text(value: str, *, field_name: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{field_name} must be non-empty")
    return value


def _assert_non_negative_int(value: int, *, field_name: str) -> int:
    if value < 0:
        raise ValueError(f"{field_name} must be non-negative")
    return value


def _assert_positive_int(value: int, *, field_name: str) -> int:
    if value <= 0:
        raise ValueError(f"{field_name} must be positive")
    return value


def _ordered_unique_texts(values: list[str], *, field_name: str) -> list[str]:
    seen: set[str] = set()
    ordered: list[str] = []
    for value in values:
        normalized = _assert_present_text(value, field_name=field_name)
        if normalized in seen:
            raise ValueError(f"{field_name} must be unique")
        seen.add(normalized)
        ordered.append(normalized)
    return ordered


def _validated_theme_terms(values: list[str], *, field_name: str) -> list[str]:
    ordered = _ordered_unique_texts(values, field_name=field_name)
    if not ordered:
        raise ValueError(f"{field_name} must be non-empty")
    for value in ordered:
        if value != value.lower():
            raise ValueError(f"{field_name} must use lowercase terms only")
        if _THEME_TERM_RE.fullmatch(value) is None:
            raise ValueError(f"{field_name} must contain alphanumeric terms only")
        if value.isdigit():
            raise ValueError(f"{field_name} must discard pure-digit terms")
        if len(value) < 4:
            raise ValueError(f"{field_name} must discard terms shorter than 4 chars")
        if value in ROLE_VOCABULARY:
            raise ValueError(f"{field_name} must discard role tokens")
    return ordered


def _ordered_unique_models(values: list[BaseModel], *, field_name: str) -> list[BaseModel]:
    seen: set[str] = set()
    ordered: list[BaseModel] = []
    for value in values:
        payload = canonical_json(value.model_dump(by_alias=True))
        if payload in seen:
            raise ValueError(f"{field_name} must be unique")
        seen.add(payload)
        ordered.append(value)
    return ordered


def _validate_timestamp_text(value: str) -> str:
    parsed = datetime.strptime(value, "%Y-%m-%d %H:%M")
    if parsed.strftime("%Y-%m-%d %H:%M") != value:
        raise ValueError("timestamp_text must match YYYY-MM-DD HH:MM exactly")
    return value


def compute_source_text_hash(source_text: str) -> str:
    return sha256_canonical_json({"source_text": source_text})


def compute_history_source_id(*, input_kind: str, source_text_hash: str) -> str:
    digest = sha256_canonical_json(
        {
            "input_kind": input_kind,
            "source_text_hash": source_text_hash,
        }
    )
    return f"history_source:{digest[:16]}"


def compute_history_preclassification_id(*, source_id: str, order_index: int) -> str:
    digest = sha256_canonical_json(
        {
            "source_id": source_id,
            "order_index": order_index,
        }
    )
    return f"history_preclassification:{digest[:16]}"


def compute_history_entry_text_hash(entry_text: str) -> str:
    return sha256_canonical_json({"entry_text": entry_text})


def compute_history_ledger_entry_id(*, source_id: str, preclassification_id: str) -> str:
    digest = sha256_canonical_json(
        {
            "source_id": source_id,
            "preclassification_id": preclassification_id,
        }
    )
    return f"history_ledger_entry:{digest[:16]}"


def compute_history_ledger_id(*, source_id: str, entry_ids: list[str]) -> str:
    digest = sha256_canonical_json(
        {
            "source_id": source_id,
            "entry_ids": entry_ids,
        }
    )
    return f"history_ledger:{digest[:16]}"


def compute_history_theme_label(*, theme_terms: list[str]) -> str:
    normalized_terms = _validated_theme_terms(list(theme_terms), field_name="theme_terms")
    return " ".join(normalized_terms[:3])


def compute_history_theme_key(*, theme_terms: list[str]) -> str:
    normalized_terms = _validated_theme_terms(list(theme_terms), field_name="theme_terms")
    return "::".join(normalized_terms[:5])


def compute_history_slice_id(*, source_id: str, slice_index: int, entry_ids: list[str]) -> str:
    digest = sha256_canonical_json(
        {
            "source_id": source_id,
            "slice_index": slice_index,
            "entry_ids": entry_ids,
        }
    )
    return f"history_slice:{digest[:16]}"


def compute_history_theme_anchor_id(
    *,
    source_id: str,
    theme_key: str,
    slice_ids: list[str],
) -> str:
    digest = sha256_canonical_json(
        {
            "source_id": source_id,
            "theme_key": theme_key,
            "slice_ids": slice_ids,
        }
    )
    return f"history_theme_anchor:{digest[:16]}"


def build_history_odeu_packet_identity_basis(
    *,
    source_id: str,
    slice_id: str,
    theme_anchor_id: str,
    lane_reconstructions: list[HistoryODEULaneReconstruction],
    semantic_identity_mode: str = HISTORY_ODEU_PACKET_SEMANTIC_IDENTITY_MODE,
) -> dict[str, object]:
    order = {lane_id: index for index, lane_id in enumerate(ODEU_LANE_ORDER)}
    ordered_lanes = sorted(lane_reconstructions, key=lambda item: order[item.lane_id])
    return {
        "schema": ADEU_HISTORY_ODEU_RECONSTRUCTION_PACKET_SCHEMA,
        "source_id": source_id,
        "slice_id": slice_id,
        "theme_anchor_id": theme_anchor_id,
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
            for lane in ordered_lanes
        ],
        "semantic_identity_mode": semantic_identity_mode,
    }


def compute_history_odeu_packet_semantic_hash(
    *,
    source_id: str,
    slice_id: str,
    theme_anchor_id: str,
    lane_reconstructions: list[HistoryODEULaneReconstruction],
    semantic_identity_mode: str = HISTORY_ODEU_PACKET_SEMANTIC_IDENTITY_MODE,
) -> str:
    return sha256_canonical_json(
        build_history_odeu_packet_identity_basis(
            source_id=source_id,
            slice_id=slice_id,
            theme_anchor_id=theme_anchor_id,
            lane_reconstructions=lane_reconstructions,
            semantic_identity_mode=semantic_identity_mode,
        )
    )


def compute_history_odeu_packet_id(*, semantic_hash: str) -> str:
    return f"history_packet:{semantic_hash[:16]}"


class HistoryTextShapeSignals(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_HISTORY_TEXT_SHAPE_SIGNALS_SCHEMA] = Field(
        default=ADEU_HISTORY_TEXT_SHAPE_SIGNALS_SCHEMA,
        alias="schema",
    )
    char_count: int
    word_count: int
    line_count: int
    nonempty_line_count: int
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
            "line_count",
            "nonempty_line_count",
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
        if self.line_count <= 0:
            raise ValueError("line_count must be positive")
        if self.nonempty_line_count > self.line_count:
            raise ValueError("nonempty_line_count must not exceed line_count")
        if self.bullet_line_count > self.line_count:
            raise ValueError("bullet_line_count must not exceed line_count")
        if self.quoted_line_count > self.line_count:
            raise ValueError("quoted_line_count must not exceed line_count")
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
    corpus_wave_posture: CorpusWavePosture
    source_authority_posture: SourceAuthorityPosture = SOURCE_AUTHORITY_POSTURE
    source_notes: list[str] = Field(default_factory=list)

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "HistorySourceArtifact":
        object.__setattr__(
            self,
            "source_label",
            _assert_present_text(self.source_label, field_name="source_label"),
        )
        object.__setattr__(
            self,
            "source_text",
            _assert_present_text(self.source_text, field_name="source_text"),
        )
        if "\r" in self.source_text:
            raise ValueError("source_text must use LF line endings only")
        object.__setattr__(
            self,
            "source_notes",
            _ordered_unique_texts(self.source_notes, field_name="source_notes"),
        )
        expected_hash = compute_source_text_hash(self.source_text)
        if self.source_text_hash != expected_hash:
            raise ValueError("source_text_hash must match normalized source_text")
        expected_source_id = compute_history_source_id(
            input_kind=self.input_kind,
            source_text_hash=self.source_text_hash,
        )
        if self.source_id != expected_source_id:
            raise ValueError("source_id must match canonical starter identity")
        return self


class HistoryPreclassification(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_HISTORY_PRECLASSIFICATION_SCHEMA] = Field(
        default=ADEU_HISTORY_PRECLASSIFICATION_SCHEMA,
        alias="schema",
    )
    preclassification_id: str
    source_id: str
    order_index: int
    message_text: str
    source_line_start: int
    source_line_end: int
    role: RoleKind
    origin_type: OriginType
    source_declaration_hints: list[SourceDeclarationHint]
    timestamp_text: str | None = None
    structural_markers: list[StructuralMarker]
    text_shape_signals: HistoryTextShapeSignals

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "HistoryPreclassification":
        object.__setattr__(
            self,
            "order_index",
            _assert_non_negative_int(self.order_index, field_name="order_index"),
        )
        object.__setattr__(
            self,
            "message_text",
            _assert_present_text(self.message_text, field_name="message_text"),
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
            raise ValueError("source_line_end must be greater than or equal to source_line_start")
        object.__setattr__(
            self,
            "source_declaration_hints",
            _ordered_unique_texts(
                list(self.source_declaration_hints),
                field_name="source_declaration_hints",
            ),
        )
        object.__setattr__(
            self,
            "structural_markers",
            _ordered_unique_texts(
                self.structural_markers,
                field_name="structural_markers",
            ),
        )
        if self.timestamp_text is not None:
            object.__setattr__(
                self,
                "timestamp_text",
                _validate_timestamp_text(self.timestamp_text),
            )

        expected_hints = [
            "full_role_header_present",
            (
                "timestamp_prefix_present"
                if self.timestamp_text is not None
                else "timestamp_prefix_absent"
            ),
        ]
        if self.source_declaration_hints != expected_hints:
            raise ValueError(
                "source_declaration_hints must reflect full role header "
                "plus timestamp presence"
            )

        expected_origin_type = ROLE_TO_ORIGIN_TYPE[self.role]
        if self.origin_type != expected_origin_type:
            raise ValueError("origin_type must match the bounded starter role mapping")

        expected_preclassification_id = compute_history_preclassification_id(
            source_id=self.source_id,
            order_index=self.order_index,
        )
        if self.preclassification_id != expected_preclassification_id:
            raise ValueError("preclassification_id must derive from source_id and order_index")
        return self


class HistoryLedgerEntry(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_HISTORY_LEDGER_ENTRY_SCHEMA] = Field(
        default=ADEU_HISTORY_LEDGER_ENTRY_SCHEMA,
        alias="schema",
    )
    entry_id: str
    source_id: str
    preclassification_id: str
    order_index: int
    entry_text: str
    entry_text_hash: str
    role: RoleKind
    origin_type: OriginType
    source_line_start: int
    source_line_end: int
    structural_markers: list[StructuralMarker]

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "HistoryLedgerEntry":
        object.__setattr__(
            self,
            "entry_id",
            _assert_present_text(self.entry_id, field_name="entry_id"),
        )
        object.__setattr__(
            self,
            "source_id",
            _assert_present_text(self.source_id, field_name="source_id"),
        )
        object.__setattr__(
            self,
            "preclassification_id",
            _assert_present_text(self.preclassification_id, field_name="preclassification_id"),
        )
        object.__setattr__(
            self,
            "order_index",
            _assert_non_negative_int(self.order_index, field_name="order_index"),
        )
        object.__setattr__(
            self,
            "entry_text",
            _assert_present_text(self.entry_text, field_name="entry_text"),
        )
        object.__setattr__(
            self,
            "entry_text_hash",
            _assert_present_text(self.entry_text_hash, field_name="entry_text_hash"),
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
            raise ValueError("source_line_end must be greater than or equal to source_line_start")
        object.__setattr__(
            self,
            "structural_markers",
            _ordered_unique_texts(
                list(self.structural_markers),
                field_name="structural_markers",
            ),
        )

        expected_origin_type = ROLE_TO_ORIGIN_TYPE[self.role]
        if self.origin_type != expected_origin_type:
            raise ValueError("origin_type must match the bounded starter role mapping")

        expected_entry_text_hash = compute_history_entry_text_hash(self.entry_text)
        if self.entry_text_hash != expected_entry_text_hash:
            raise ValueError("entry_text_hash must match entry_text")

        expected_entry_id = compute_history_ledger_entry_id(
            source_id=self.source_id,
            preclassification_id=self.preclassification_id,
        )
        if self.entry_id != expected_entry_id:
            raise ValueError("entry_id must derive from source_id and preclassification_id")
        return self


class HistoryLedger(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_HISTORY_LEDGER_SCHEMA] = Field(
        default=ADEU_HISTORY_LEDGER_SCHEMA,
        alias="schema",
    )
    ledger_id: str
    source_id: str
    entries: list[HistoryLedgerEntry]
    entry_count: int

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "HistoryLedger":
        object.__setattr__(
            self,
            "ledger_id",
            _assert_present_text(self.ledger_id, field_name="ledger_id"),
        )
        object.__setattr__(
            self,
            "source_id",
            _assert_present_text(self.source_id, field_name="source_id"),
        )
        object.__setattr__(
            self,
            "entry_count",
            _assert_positive_int(self.entry_count, field_name="entry_count"),
        )
        if not self.entries:
            raise ValueError("entries must be non-empty")
        if self.entry_count != len(self.entries):
            raise ValueError("entry_count must match the number of entries")

        order_indexes = [entry.order_index for entry in self.entries]
        if order_indexes != list(range(len(self.entries))):
            raise ValueError("entries must cover a contiguous order_index range starting at 0")
        if len({entry.entry_id for entry in self.entries}) != len(self.entries):
            raise ValueError("entries must have unique entry_id values")
        if len({entry.preclassification_id for entry in self.entries}) != len(self.entries):
            raise ValueError("entries must have unique preclassification_id values")
        if any(entry.source_id != self.source_id for entry in self.entries):
            raise ValueError("entries must share the ledger source_id")

        expected_ledger_id = compute_history_ledger_id(
            source_id=self.source_id,
            entry_ids=[entry.entry_id for entry in self.entries],
        )
        if self.ledger_id != expected_ledger_id:
            raise ValueError("ledger_id must derive from source_id and entry_ids")
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
    entry_ids: list[str]
    chronology_start_order_index: int
    chronology_end_order_index: int
    boundary_tags: list[SliceBoundaryTag]
    theme_terms: list[str]
    theme_label: str
    theme_key: str

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "HistorySlice":
        object.__setattr__(
            self,
            "slice_id",
            _assert_present_text(self.slice_id, field_name="slice_id"),
        )
        object.__setattr__(
            self,
            "source_id",
            _assert_present_text(self.source_id, field_name="source_id"),
        )
        object.__setattr__(
            self,
            "slice_index",
            _assert_non_negative_int(self.slice_index, field_name="slice_index"),
        )
        object.__setattr__(
            self,
            "entry_ids",
            _ordered_unique_texts(list(self.entry_ids), field_name="entry_ids"),
        )
        object.__setattr__(
            self,
            "chronology_start_order_index",
            _assert_non_negative_int(
                self.chronology_start_order_index,
                field_name="chronology_start_order_index",
            ),
        )
        object.__setattr__(
            self,
            "chronology_end_order_index",
            _assert_non_negative_int(
                self.chronology_end_order_index,
                field_name="chronology_end_order_index",
            ),
        )
        if self.chronology_end_order_index < self.chronology_start_order_index:
            raise ValueError(
                "chronology_end_order_index must be greater than or equal to "
                "chronology_start_order_index"
            )
        if not self.entry_ids:
            raise ValueError("entry_ids must be non-empty")
        expected_entry_count = (
            self.chronology_end_order_index - self.chronology_start_order_index + 1
        )
        if len(self.entry_ids) != expected_entry_count:
            raise ValueError(
                "entry_ids must span a contiguous order_index range without gaps"
            )
        object.__setattr__(
            self,
            "boundary_tags",
            _ordered_unique_texts(list(self.boundary_tags), field_name="boundary_tags"),
        )
        object.__setattr__(
            self,
            "theme_terms",
            _validated_theme_terms(list(self.theme_terms), field_name="theme_terms"),
        )
        object.__setattr__(
            self,
            "theme_label",
            _assert_present_text(self.theme_label, field_name="theme_label"),
        )
        object.__setattr__(
            self,
            "theme_key",
            _assert_present_text(self.theme_key, field_name="theme_key"),
        )

        expected_theme_label = compute_history_theme_label(theme_terms=self.theme_terms)
        if self.theme_label != expected_theme_label:
            raise ValueError("theme_label must derive from theme_terms")

        expected_theme_key = compute_history_theme_key(theme_terms=self.theme_terms)
        if self.theme_key != expected_theme_key:
            raise ValueError("theme_key must derive from theme_terms")

        expected_slice_id = compute_history_slice_id(
            source_id=self.source_id,
            slice_index=self.slice_index,
            entry_ids=self.entry_ids,
        )
        if self.slice_id != expected_slice_id:
            raise ValueError("slice_id must derive from source_id, slice_index, and entry_ids")
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
    slice_ids: list[str]
    anchor_entry_ids: list[str]
    supporting_terms: list[str]

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "HistoryThemeAnchor":
        object.__setattr__(
            self,
            "theme_anchor_id",
            _assert_present_text(self.theme_anchor_id, field_name="theme_anchor_id"),
        )
        object.__setattr__(
            self,
            "source_id",
            _assert_present_text(self.source_id, field_name="source_id"),
        )
        object.__setattr__(
            self,
            "theme_key",
            _assert_present_text(self.theme_key, field_name="theme_key"),
        )
        object.__setattr__(
            self,
            "display_label",
            _assert_present_text(self.display_label, field_name="display_label"),
        )
        object.__setattr__(
            self,
            "slice_ids",
            _ordered_unique_texts(list(self.slice_ids), field_name="slice_ids"),
        )
        object.__setattr__(
            self,
            "anchor_entry_ids",
            _ordered_unique_texts(list(self.anchor_entry_ids), field_name="anchor_entry_ids"),
        )
        object.__setattr__(
            self,
            "supporting_terms",
            _validated_theme_terms(list(self.supporting_terms), field_name="supporting_terms"),
        )
        if not self.slice_ids:
            raise ValueError("slice_ids must be non-empty")
        if not self.anchor_entry_ids:
            raise ValueError("anchor_entry_ids must be non-empty")

        theme_key_terms = _validated_theme_terms(
            self.theme_key.split("::"),
            field_name="theme_key_terms",
        )
        if len(theme_key_terms) > 5:
            raise ValueError("theme_key must contain at most 5 terms")
        if self.theme_key != "::".join(theme_key_terms):
            raise ValueError("theme_key must use ::-joined lawful theme terms")

        expected_display_label = " ".join(theme_key_terms[:3])
        if self.display_label != expected_display_label:
            raise ValueError("display_label must match the theme_key prefix")
        if self.supporting_terms[: len(theme_key_terms)] != theme_key_terms:
            raise ValueError("supporting_terms must begin with the theme_key terms")

        expected_theme_anchor_id = compute_history_theme_anchor_id(
            source_id=self.source_id,
            theme_key=self.theme_key,
            slice_ids=self.slice_ids,
        )
        if self.theme_anchor_id != expected_theme_anchor_id:
            raise ValueError(
                "theme_anchor_id must derive from source_id, theme_key, and slice_ids"
            )
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
            _assert_present_text(self.entry_id, field_name="entry_id"),
        )
        object.__setattr__(
            self,
            "excerpt",
            _assert_present_text(self.excerpt, field_name="excerpt"),
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
        object.__setattr__(
            self,
            "evidence_refs",
            [
                HistoryEvidenceRef.model_validate(item.model_dump(by_alias=True))
                for item in _ordered_unique_models(
                    list(self.evidence_refs),
                    field_name="evidence_refs",
                )
            ],
        )
        if self.reconstruction_text is not None:
            object.__setattr__(
                self,
                "reconstruction_text",
                _assert_present_text(
                    self.reconstruction_text,
                    field_name="reconstruction_text",
                ),
            )
        if self.presence_status in {"present", "weakly_present"}:
            if self.reconstruction_text is None:
                raise ValueError("present or weakly_present lanes require reconstruction_text")
            if not self.evidence_refs:
                raise ValueError("present or weakly_present lanes require evidence_refs")
            return self
        if self.reconstruction_text is not None:
            raise ValueError("absent lanes must omit reconstruction_text")
        if self.evidence_refs:
            raise ValueError("absent lanes may not carry evidence_refs")
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
    interpretation_authority_posture: HistoryODEUInterpretationAuthorityPosture = (
        HISTORY_ODEU_INTERPRETATION_AUTHORITY_POSTURE
    )
    semantic_identity_mode: HistoryODEUPacketSemanticIdentityMode = (
        HISTORY_ODEU_PACKET_SEMANTIC_IDENTITY_MODE
    )
    semantic_hash: str

    @property
    def schema(self) -> str:
        return self.schema_id

    def identity_basis(self) -> dict[str, object]:
        return build_history_odeu_packet_identity_basis(
            source_id=self.source_id,
            slice_id=self.slice_id,
            theme_anchor_id=self.theme_anchor_id,
            lane_reconstructions=self.lane_reconstructions,
            semantic_identity_mode=self.semantic_identity_mode,
        )

    @model_validator(mode="after")
    def _validate(self) -> "HistoryODEUReconstructionPacket":
        object.__setattr__(
            self,
            "packet_id",
            _assert_present_text(self.packet_id, field_name="packet_id"),
        )
        object.__setattr__(
            self,
            "source_id",
            _assert_present_text(self.source_id, field_name="source_id"),
        )
        object.__setattr__(
            self,
            "slice_id",
            _assert_present_text(self.slice_id, field_name="slice_id"),
        )
        object.__setattr__(
            self,
            "theme_anchor_id",
            _assert_present_text(self.theme_anchor_id, field_name="theme_anchor_id"),
        )
        object.__setattr__(
            self,
            "semantic_hash",
            _assert_present_text(self.semantic_hash, field_name="semantic_hash"),
        )
        order = {lane_id: index for index, lane_id in enumerate(ODEU_LANE_ORDER)}
        normalized_lanes = sorted(self.lane_reconstructions, key=lambda item: order[item.lane_id])
        if [item.lane_id for item in normalized_lanes] != list(ODEU_LANE_ORDER):
            raise ValueError("lane_reconstructions must contain exactly one O/E/D/U lane")
        object.__setattr__(self, "lane_reconstructions", normalized_lanes)

        expected_semantic_hash = compute_history_odeu_packet_semantic_hash(
            source_id=self.source_id,
            slice_id=self.slice_id,
            theme_anchor_id=self.theme_anchor_id,
            lane_reconstructions=self.lane_reconstructions,
            semantic_identity_mode=self.semantic_identity_mode,
        )
        if self.semantic_hash != expected_semantic_hash:
            raise ValueError("semantic_hash must match canonical packet identity basis")
        expected_packet_id = compute_history_odeu_packet_id(semantic_hash=self.semantic_hash)
        if self.packet_id != expected_packet_id:
            raise ValueError("packet_id must match canonical packet identity")
        return self


__all__ = [
    "ADEU_HISTORY_EVIDENCE_REF_SCHEMA",
    "ADEU_HISTORY_LEDGER_ENTRY_SCHEMA",
    "ADEU_HISTORY_LEDGER_SCHEMA",
    "ADEU_HISTORY_ODEU_LANE_RECONSTRUCTION_SCHEMA",
    "ADEU_HISTORY_ODEU_RECONSTRUCTION_PACKET_SCHEMA",
    "ADEU_HISTORY_PRECLASSIFICATION_SCHEMA",
    "ADEU_HISTORY_SLICE_SCHEMA",
    "ADEU_HISTORY_SOURCE_ARTIFACT_SCHEMA",
    "ADEU_HISTORY_THEME_ANCHOR_SCHEMA",
    "ADEU_HISTORY_TEXT_SHAPE_SIGNALS_SCHEMA",
    "CORPUS_WAVE_POSTURE_VOCABULARY",
    "INPUT_KIND_VOCABULARY",
    "ORIGIN_TYPE_VOCABULARY",
    "ROLE_TO_ORIGIN_TYPE",
    "ROLE_VOCABULARY",
    "SLICE_BOUNDARY_TAG_VOCABULARY",
    "SOURCE_AUTHORITY_POSTURE",
    "SOURCE_DECLARATION_HINT_VOCABULARY",
    "SliceBoundaryTag",
    "STRUCTURAL_MARKER_VOCABULARY",
    "DOMINANT_ROLE_POSTURE_VOCABULARY",
    "HistoryEvidenceRef",
    "HistoryLedger",
    "HistoryLedgerEntry",
    "HistoryODEULaneReconstruction",
    "HistoryODEUReconstructionPacket",
    "HISTORY_ODEU_INTERPRETATION_AUTHORITY_POSTURE",
    "HISTORY_ODEU_PACKET_SEMANTIC_IDENTITY_MODE",
    "HistoryPreclassification",
    "HistorySlice",
    "HistorySourceArtifact",
    "HistoryThemeAnchor",
    "HistoryTextShapeSignals",
    "LANE_EXPLICATION_STATUS_VOCABULARY",
    "LANE_PRESENCE_STATUS_VOCABULARY",
    "ODEU_LANE_ORDER",
    "canonical_json",
    "compute_history_entry_text_hash",
    "compute_history_ledger_entry_id",
    "compute_history_ledger_id",
    "compute_history_odeu_packet_id",
    "compute_history_odeu_packet_semantic_hash",
    "compute_history_preclassification_id",
    "compute_history_source_id",
    "compute_history_slice_id",
    "compute_history_theme_anchor_id",
    "compute_history_theme_key",
    "compute_history_theme_label",
    "build_history_odeu_packet_identity_basis",
    "compute_source_text_hash",
    "sha256_canonical_json",
]
