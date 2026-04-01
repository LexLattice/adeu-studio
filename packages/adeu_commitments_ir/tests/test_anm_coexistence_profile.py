from __future__ import annotations

import json
from pathlib import Path
from typing import get_args

import pytest
from adeu_commitments_ir import (
    ANM_MARKDOWN_COEXISTENCE_PROFILE_SCHEMA,
    AnmMarkdownCoexistenceProfile,
)
from adeu_commitments_ir.anm_models import (
    AdoptionBoundaryPosture,
    AllowedConstrainAction,
    CompanionEmbeddingPosture,
    CurrentMarkdownAuthorityRelation,
    MigrationPosture,
    SourcePosture,
)
from pydantic import ValidationError


def _fixture_path_v47c(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v47c" / name


def _read_json_v47c(name: str) -> dict[str, object]:
    return json.loads(_fixture_path_v47c(name).read_text(encoding="utf-8"))


def test_v47c_model_accepts_committed_reference_payload() -> None:
    profile = AnmMarkdownCoexistenceProfile.model_validate(
        _read_json_v47c("reference_anm_markdown_coexistence_profile.json")
    )

    assert profile.schema == ANM_MARKDOWN_COEXISTENCE_PROFILE_SCHEMA


def test_v47c_vocabularies_are_exact() -> None:
    assert get_args(SourcePosture) == ("standalone_anm", "companion_anm")
    assert get_args(CurrentMarkdownAuthorityRelation) == (
        "current_markdown_controlling",
        "coexisting_non_override",
        "later_lock_required_for_supersession",
    )
    assert get_args(MigrationPosture) == (
        "none",
        "prefer_companion",
        "prefer_standalone",
        "defer_to_later_lock",
    )
    assert get_args(CompanionEmbeddingPosture) == (
        "not_applicable",
        "embedded_in_host_markdown",
        "adjacent_companion_document",
    )
    assert get_args(AllowedConstrainAction) == (
        "reference_released_anm_artifact",
        "embed_authoritative_d1_block",
        "record_non_override_binding",
        "emit_migration_signal",
    )
    assert get_args(AdoptionBoundaryPosture) == (
        "allowed_now",
        "allowed_with_later_lock",
        "forbidden_in_v47c",
    )


def test_v47c_rejects_inconsistent_supersession_fields() -> None:
    payload = _read_json_v47c("reference_anm_markdown_coexistence_profile.json")
    payload["source_rows"][0]["requires_later_lock_for_supersession"] = True

    with pytest.raises(
        ValidationError,
        match="requires_later_lock_for_supersession must match",
    ):
        AnmMarkdownCoexistenceProfile.model_validate(payload)


def test_v47c_rejects_boundary_action_outside_frozen_vocabulary() -> None:
    payload = _read_json_v47c("reference_anm_markdown_coexistence_profile.json")
    payload["adoption_boundary_rows"][0]["allowed_now_actions"] = ["authorize_execution"]

    with pytest.raises(ValidationError):
        AnmMarkdownCoexistenceProfile.model_validate(payload)
