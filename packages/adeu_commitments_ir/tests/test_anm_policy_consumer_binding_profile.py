from __future__ import annotations

import json
from pathlib import Path
from typing import get_args

import pytest
from adeu_commitments_ir import (
    ANM_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA,
    AnmPolicyConsumerBindingProfile,
)
from adeu_commitments_ir.anm_models import (
    AllowedConsumerAction,
    ConsumerAuthorityRelation,
    ConsumerRefKind,
    ConsumerWorldKind,
    PolicySourceRefKind,
)
from pydantic import ValidationError


def _fixture_path_v47e(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v47e" / name


def _read_json_v47e(name: str) -> dict[str, object]:
    return json.loads(_fixture_path_v47e(name).read_text(encoding="utf-8"))


def test_v47e_model_accepts_committed_reference_payload() -> None:
    profile = AnmPolicyConsumerBindingProfile.model_validate(
        _read_json_v47e("reference_anm_policy_consumer_binding_profile.json")
    )

    assert profile.schema == ANM_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA


def test_v47e_vocabularies_are_exact() -> None:
    assert get_args(ConsumerWorldKind) == (
        "released_v45_descriptive_artifact_world",
        "released_runtime_event_artifact_world",
    )
    assert get_args(ConsumerRefKind) == (
        "released_v45_artifact_ref",
        "released_runtime_event_stream_ref",
    )
    assert get_args(PolicySourceRefKind) == ("d1_clause_ref",)
    assert get_args(ConsumerAuthorityRelation) == (
        "constrain_only_non_executive",
        "later_lock_required_for_effective_action",
    )
    assert get_args(AllowedConsumerAction) == (
        "reference_released_policy_source",
        "emit_consumer_conformance_annotation",
        "record_fail_closed_consumer_block",
        "attach_traceable_policy_binding",
    )


def test_v47e_rejects_world_ref_kind_mismatch() -> None:
    payload = _read_json_v47e("reference_anm_policy_consumer_binding_profile.json")
    payload["consumer_rows"][0]["consumer_ref_kind"] = "released_runtime_event_stream_ref"

    with pytest.raises(
        ValidationError,
        match=(
            "released_v45_descriptive_artifact_world rows require "
            "consumer_ref_kind = released_v45_artifact_ref"
        ),
    ):
        AnmPolicyConsumerBindingProfile.model_validate(payload)


def test_v47e_rejects_overlapping_action_lists() -> None:
    payload = _read_json_v47e("reference_anm_policy_consumer_binding_profile.json")
    payload["consumer_rows"][0]["forbidden_actions"] = [
        "attach_traceable_policy_binding",
        "record_fail_closed_consumer_block",
    ]

    with pytest.raises(
        ValidationError,
        match="consumer action lists must not overlap",
    ):
        AnmPolicyConsumerBindingProfile.model_validate(payload)
