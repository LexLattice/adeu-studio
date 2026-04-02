from __future__ import annotations

import json
from pathlib import Path
from typing import get_args

import pytest
from adeu_commitments_ir import (
    ANM_BENCHMARK_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA,
    AnmBenchmarkPolicyConsumerBindingProfile,
)
from adeu_commitments_ir.anm_models import (
    AllowedBenchmarkConsumerAction,
    BenchmarkConsumerAuthorityRelation,
    BenchmarkConsumerRefKind,
    BenchmarkConsumerWorldKind,
    PolicySourceRefKind,
)
from pydantic import ValidationError


def _fixture_path_v47f(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v47f" / name


def _read_json_v47f(name: str) -> dict[str, object]:
    return json.loads(_fixture_path_v47f(name).read_text(encoding="utf-8"))


def test_v47f_model_accepts_committed_reference_payload() -> None:
    profile = AnmBenchmarkPolicyConsumerBindingProfile.model_validate(
        _read_json_v47f("reference_anm_benchmark_policy_consumer_binding_profile.json")
    )

    assert profile.schema == ANM_BENCHMARK_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA


def test_v47f_vocabularies_are_exact() -> None:
    assert get_args(BenchmarkConsumerWorldKind) == (
        "released_v42_local_eval_artifact_world",
        "released_v42_scorecard_artifact_world",
        "released_v42_behavior_evidence_artifact_world",
    )
    assert get_args(BenchmarkConsumerRefKind) == (
        "released_v42_local_eval_record_ref",
        "released_v42_scorecard_manifest_ref",
        "released_v42_behavior_evidence_bundle_ref",
    )
    assert get_args(PolicySourceRefKind) == ("d1_clause_ref",)
    assert get_args(BenchmarkConsumerAuthorityRelation) == (
        "constrain_only_non_executive",
        "later_lock_required_for_effective_action",
    )
    assert get_args(AllowedBenchmarkConsumerAction) == (
        "reference_released_policy_source",
        "emit_benchmark_conformance_annotation",
        "record_fail_closed_benchmark_consumer_block",
        "attach_traceable_benchmark_policy_binding",
    )


def test_v47f_rejects_world_ref_kind_mismatch() -> None:
    payload = _read_json_v47f("reference_anm_benchmark_policy_consumer_binding_profile.json")
    behavior_row = next(
        row
        for row in payload["benchmark_consumer_rows"]
        if row["benchmark_consumer_world_kind"] == "released_v42_behavior_evidence_artifact_world"
    )
    behavior_row["benchmark_consumer_ref_kind"] = (
        "released_v42_local_eval_record_ref"
    )

    with pytest.raises(
        ValidationError,
        match=(
            "released_v42_behavior_evidence_artifact_world rows require "
            "benchmark_consumer_ref_kind = released_v42_behavior_evidence_bundle_ref"
        ),
    ):
        AnmBenchmarkPolicyConsumerBindingProfile.model_validate(payload)


def test_v47f_rejects_overlapping_action_lists() -> None:
    payload = _read_json_v47f("reference_anm_benchmark_policy_consumer_binding_profile.json")
    payload["benchmark_consumer_rows"][0]["forbidden_actions"] = [
        "record_fail_closed_benchmark_consumer_block",
        "reference_released_policy_source",
    ]

    with pytest.raises(
        ValidationError,
        match="benchmark consumer action lists must not overlap",
    ):
        AnmBenchmarkPolicyConsumerBindingProfile.model_validate(payload)
