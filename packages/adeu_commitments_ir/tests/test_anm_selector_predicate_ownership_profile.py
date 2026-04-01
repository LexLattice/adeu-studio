from __future__ import annotations

import json
from pathlib import Path
from typing import get_args

import pytest
from adeu_commitments_ir import (
    ANM_SELECTOR_PREDICATE_OWNERSHIP_PROFILE_SCHEMA,
    AnmSelectorPredicateOwnershipProfile,
)
from adeu_commitments_ir.anm_models import (
    BootstrapRetirementPosture,
    OwnershipCompatibilityPosture,
    PredicateOwnershipOwnerLayer,
    PredicateOwnershipRefKind,
    SelectorOwnershipOwnerLayer,
    SelectorOwnershipRefKind,
)
from pydantic import ValidationError


def _fixture_path_v47d(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v47d" / name


def _read_json_v47d(name: str) -> dict[str, object]:
    return json.loads(_fixture_path_v47d(name).read_text(encoding="utf-8"))


def test_v47d_model_accepts_committed_reference_payload() -> None:
    profile = AnmSelectorPredicateOwnershipProfile.model_validate(
        _read_json_v47d("reference_anm_selector_predicate_ownership_profile.json")
    )

    assert profile.schema == ANM_SELECTOR_PREDICATE_OWNERSHIP_PROFILE_SCHEMA


def test_v47d_vocabularies_are_exact() -> None:
    assert get_args(SelectorOwnershipRefKind) == (
        "bootstrap_string_selector",
        "imported_o_owned_selector_handle",
    )
    assert get_args(SelectorOwnershipOwnerLayer) == ("bootstrap", "o_owned")
    assert get_args(PredicateOwnershipRefKind) == (
        "bootstrap_predicate_contract",
        "imported_e_owned_predicate_ref",
    )
    assert get_args(PredicateOwnershipOwnerLayer) == ("bootstrap", "e_owned")
    assert get_args(OwnershipCompatibilityPosture) == (
        "bootstrap_only",
        "bootstrap_compatible_with_owned_successor",
        "owned_preferred_bootstrap_still_allowed",
        "mixed_ownership_forbidden",
    )
    assert get_args(BootstrapRetirementPosture) == (
        "not_selected",
        "later_lock_required",
        "owned_successor_available_bootstrap_still_allowed",
    )


def test_v47d_rejects_selector_row_with_conflicting_bootstrap_and_imported_fields() -> None:
    payload = _read_json_v47d("reference_anm_selector_predicate_ownership_profile.json")
    payload["selector_rows"][0]["imported_selector_handle_ref"] = (
        "selector-handle:artifact-emitted:v1"
    )

    with pytest.raises(
        ValidationError,
        match="bootstrap_string_selector rows may not set imported_selector_handle_ref",
    ):
        AnmSelectorPredicateOwnershipProfile.model_validate(payload)


def test_v47d_rejects_incomplete_compatibility_matrix() -> None:
    payload = _read_json_v47d("reference_anm_selector_predicate_ownership_profile.json")
    payload["compatibility_rules"] = payload["compatibility_rules"][:-1]

    with pytest.raises(
        ValidationError,
        match="compatibility_rules must cover the four ownership combinations",
    ):
        AnmSelectorPredicateOwnershipProfile.model_validate(payload)
