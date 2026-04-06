from __future__ import annotations

from datetime import datetime
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import canonical_json, sha256_canonical_json

ADEU_HISTORY_SOURCE_ARTIFACT_SCHEMA = "adeu_history_source_artifact@1"
ADEU_HISTORY_TEXT_SHAPE_SIGNALS_SCHEMA = "adeu_history_text_shape_signals@1"
ADEU_HISTORY_PRECLASSIFICATION_SCHEMA = "adeu_history_preclassification@1"

SOURCE_AUTHORITY_POSTURE = "normalized_source_text_authoritative"
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
                list(self.structural_markers),
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

        expected_origin_type = {
            "user": "user_native",
            "assistant": "assistant_reply",
            "system": "system_instruction",
        }[self.role]
        if self.origin_type != expected_origin_type:
            raise ValueError("origin_type must match the bounded starter role mapping")

        expected_preclassification_id = compute_history_preclassification_id(
            source_id=self.source_id,
            order_index=self.order_index,
        )
        if self.preclassification_id != expected_preclassification_id:
            raise ValueError("preclassification_id must derive from source_id and order_index")
        return self


__all__ = [
    "ADEU_HISTORY_PRECLASSIFICATION_SCHEMA",
    "ADEU_HISTORY_SOURCE_ARTIFACT_SCHEMA",
    "ADEU_HISTORY_TEXT_SHAPE_SIGNALS_SCHEMA",
    "CORPUS_WAVE_POSTURE_VOCABULARY",
    "INPUT_KIND_VOCABULARY",
    "ORIGIN_TYPE_VOCABULARY",
    "ROLE_VOCABULARY",
    "SOURCE_AUTHORITY_POSTURE",
    "SOURCE_DECLARATION_HINT_VOCABULARY",
    "STRUCTURAL_MARKER_VOCABULARY",
    "HistoryPreclassification",
    "HistorySourceArtifact",
    "HistoryTextShapeSignals",
    "canonical_json",
    "compute_history_preclassification_id",
    "compute_history_source_id",
    "compute_source_text_hash",
    "sha256_canonical_json",
]
