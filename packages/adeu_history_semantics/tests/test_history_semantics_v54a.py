from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_history_semantics import (
    SOURCE_AUTHORITY_POSTURE,
    HistoryPreclassification,
    HistorySourceArtifact,
    HistoryTextShapeSignals,
    build_history_source_artifact,
    preclassify_history_source,
)
from pydantic import ValidationError

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v54a"


def _load_text(name: str) -> str:
    return (FIXTURE_ROOT / name).read_bytes().decode("utf-8")


def _load_json(name: str) -> object:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _build_reference_source(
    *,
    source_text: str,
    source_label: str = "starter fixture",
) -> HistorySourceArtifact:
    return build_history_source_artifact(
        source_text=source_text,
        source_label=source_label,
        corpus_wave_posture="wave_0_bootstrap_candidate",
        source_notes=[
            "starter_fixture",
            "projection_only_metadata",
        ],
    )


def test_reference_source_and_preclassifications_validate_against_committed_fixtures() -> None:
    source = _build_reference_source(
        source_text=_load_text("reference_conversation_history_lf.txt")
    )
    preclassifications = preclassify_history_source(source=source)

    expected_source_payload = _load_json("reference_history_source_artifact.json")
    expected_preclassifications_payload = _load_json("reference_history_preclassifications.json")

    assert source.model_dump(by_alias=True) == expected_source_payload
    assert [
        item.model_dump(by_alias=True) for item in preclassifications
    ] == expected_preclassifications_payload


def test_normalization_equivalence_keeps_source_identity_stable() -> None:
    lf_text = _load_text("reference_conversation_history_lf.txt")
    lf_source = _build_reference_source(
        source_text=lf_text
    )
    crlf_source = _build_reference_source(
        source_text=lf_text.replace("\n", "\r\n")
    )

    assert "\r\n" in lf_text.replace("\n", "\r\n")
    assert lf_source.source_text == crlf_source.source_text
    assert lf_source.source_text_hash == crlf_source.source_text_hash
    assert lf_source.source_id == crlf_source.source_id


def test_bracket_led_continuation_content_is_admitted_when_not_timestamp_like() -> None:
    source = _build_reference_source(
        source_text=(
            "User: Please keep this bounded.\n"
            "[docs](https://example.com) remains part of the same message.\n"
            "Assistant: Acknowledged."
        )
    )

    preclassifications = preclassify_history_source(source=source)

    assert len(preclassifications) == 2
    assert preclassifications[0].message_text.startswith("Please keep this bounded.\n[docs]")


def test_projection_only_metadata_does_not_mint_identity() -> None:
    source_text = _load_text("reference_conversation_history_lf.txt")
    baseline = _build_reference_source(source_text=source_text, source_label="starter fixture")
    mutated_projection = build_history_source_artifact(
        source_text=source_text,
        source_label="renamed starter fixture",
        corpus_wave_posture="later_wave_candidate",
        source_notes=[
            "projection_only_metadata_variant",
        ],
    )

    assert mutated_projection.source_id == baseline.source_id
    assert mutated_projection.source_text_hash == baseline.source_text_hash
    assert mutated_projection.source_label != baseline.source_label
    assert mutated_projection.corpus_wave_posture != baseline.corpus_wave_posture
    assert mutated_projection.source_notes != baseline.source_notes


@pytest.mark.parametrize(
    "fixture_name, error_match",
    [
        ("reject_unheadered_conversation_history.txt", "must start with an exact full role header"),
        ("reject_shorthand_aliases.txt", "unsupported or malformed role header placement"),
        ("reject_nonconforming_timestamp_prefix.txt", "unsupported timestamp placement"),
        (
            "reject_mixed_domain_and_malformed_block.txt",
            "unsupported or malformed role header placement",
        ),
    ],
)
def test_reject_invalid_source_texts_fail_closed(
    fixture_name: str,
    error_match: str,
) -> None:
    with pytest.raises(ValueError, match=error_match):
        build_history_source_artifact(
            source_text=_load_text(fixture_name),
            source_label="reject fixture",
        )


def test_reject_abstract_like_input_payload() -> None:
    with pytest.raises(ValidationError):
        build_history_source_artifact(
            source_text=_load_text("reference_conversation_history_lf.txt"),
            input_kind="abstract_like",
            source_label="reject abstract-like",
        )


def test_reject_attempted_raw_byte_authority_claim_payload() -> None:
    payload = _load_json("reject_raw_byte_authority_claim.json")
    with pytest.raises(ValidationError):
        HistorySourceArtifact.model_validate(payload)


def test_reject_attempted_widened_surface_payload() -> None:
    payload = _load_json("reject_attempted_widened_surface.json")
    with pytest.raises(ValueError, match="not released in V54-A"):
        _validate_v54a_payload(payload)


def test_reference_preclassifications_expose_bounded_starter_law() -> None:
    source = _build_reference_source(
        source_text=_load_text("reference_conversation_history_lf.txt")
    )
    system_message, user_message, assistant_message = preclassify_history_source(source=source)

    assert source.source_authority_posture == SOURCE_AUTHORITY_POSTURE
    assert system_message.role == "system"
    assert user_message.role == "user"
    assert assistant_message.role == "assistant"
    assert assistant_message.source_declaration_hints == [
        "full_role_header_present",
        "timestamp_prefix_present",
    ]
    assert assistant_message.structural_markers == [
        "multi_line_message",
        "bullet_line_present",
    ]
    assert assistant_message.text_shape_signals.line_count == 3
    assert assistant_message.text_shape_signals.bullet_line_count == 2
    assert assistant_message.text_shape_signals.question_count == 0


def _validate_v54a_payload(payload: object) -> object:
    if not isinstance(payload, dict):
        raise ValueError("starter payload must be an object")
    schema = payload.get("schema")
    if schema == "adeu_history_source_artifact@1":
        return HistorySourceArtifact.model_validate(payload)
    if schema == "adeu_history_preclassification@1":
        return HistoryPreclassification.model_validate(payload)
    if schema == "adeu_history_text_shape_signals@1":
        return HistoryTextShapeSignals.model_validate(payload)
    raise ValueError(f"{schema!r} is not released in V54-A")
