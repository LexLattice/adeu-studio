from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_core_ir import (
    DEFAULT_V39E_FIX_PLAN_REFERENCE_FIXTURE_PATH,
    DEFAULT_V39E_LOCAL_HYBRID_HUMAN_FIXTURE_PATH,
    DEFAULT_V39E_LOCAL_HYBRID_ORACLE_FIXTURE_PATH,
    SYNTHETIC_PRESSURE_MISMATCH_CHECKPOINT_TRACE_SCHEMA,
    SYNTHETIC_PRESSURE_MISMATCH_ORACLE_REQUEST_SCHEMA,
    SYNTHETIC_PRESSURE_MISMATCH_ORACLE_RESOLUTION_SCHEMA,
    SyntheticPressureMismatchCheckpointTrace,
    SyntheticPressureMismatchOracleRequest,
    SyntheticPressureMismatchOracleResolution,
    canonicalize_synthetic_pressure_mismatch_checkpoint_trace_payload,
    canonicalize_synthetic_pressure_mismatch_oracle_request_payload,
    canonicalize_synthetic_pressure_mismatch_oracle_resolution_payload,
    derive_v39e_checkpoint_trace,
    derive_v39e_oracle_request,
    derive_v39e_oracle_resolution,
)
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixtures_root() -> Path:
    return (
        _repo_root()
        / "apps"
        / "api"
        / "fixtures"
        / "synthetic_pressure_mismatch"
        / "vnext_plus76"
    )


def _load_json(name: str) -> dict[str, object]:
    return json.loads((_fixtures_root() / name).read_text(encoding="utf-8"))


def _load_exported_schema(name: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / name
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v39e_oracle_request_fixture_validates_and_replays() -> None:
    fixture = _load_json("synthetic_pressure_mismatch_oracle_request_v76_reference.json")
    request = SyntheticPressureMismatchOracleRequest.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert request.schema == SYNTHETIC_PRESSURE_MISMATCH_ORACLE_REQUEST_SCHEMA
    assert request.source_kind == "local_hybrid_fixture"
    assert request.resolution_route == "oracle_assisted"

    derived = derive_v39e_oracle_request(
        DEFAULT_V39E_LOCAL_HYBRID_ORACLE_FIXTURE_PATH,
        repository_root=_repo_root(),
    )
    assert (
        canonicalize_synthetic_pressure_mismatch_oracle_request_payload(
            derived.model_dump(mode="json", exclude_none=True),
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v39e_oracle_resolution_fixture_validates_and_replays() -> None:
    fixture = _load_json("synthetic_pressure_mismatch_oracle_resolution_v76_reference.json")
    resolution = SyntheticPressureMismatchOracleResolution.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert resolution.schema == SYNTHETIC_PRESSURE_MISMATCH_ORACLE_RESOLUTION_SCHEMA
    assert resolution.resolution_disposition == "advisory_support"

    derived = derive_v39e_oracle_resolution(
        "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus76/"
        "synthetic_pressure_mismatch_oracle_request_v76_reference.json",
        resolution_disposition="advisory_support",
        advisory_summary=(
            "The anchored comment repeats behavior already visible from the local return "
            "logic and adds no hidden invariant."
        ),
        raw_output_text=(
            "advisory_support: the anchored comment narrates code that is already "
            "evident from the local return path."
        ),
        repository_root=_repo_root(),
    )
    assert (
        canonicalize_synthetic_pressure_mismatch_oracle_resolution_payload(
            derived.model_dump(mode="json", exclude_none=True),
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v39e_deterministic_trace_fixture_validates_and_replays() -> None:
    fixture = _load_json("synthetic_pressure_mismatch_checkpoint_trace_v76_deterministic.json")
    trace = SyntheticPressureMismatchCheckpointTrace.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert trace.schema == SYNTHETIC_PRESSURE_MISMATCH_CHECKPOINT_TRACE_SCHEMA
    assert trace.source_kind == "released_fix_plan_projection"
    assert len(trace.checkpoints) == 2
    assert all(
        checkpoint.checkpoint_class == "deterministic_fail"
        for checkpoint in trace.checkpoints
    )

    derived = derive_v39e_checkpoint_trace(
        fix_plan_reference_fixture=DEFAULT_V39E_FIX_PLAN_REFERENCE_FIXTURE_PATH,
        repository_root=_repo_root(),
    )
    assert (
        canonicalize_synthetic_pressure_mismatch_checkpoint_trace_payload(
            derived.model_dump(mode="json", exclude_none=True),
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v39e_oracle_trace_fixture_validates_and_replays() -> None:
    fixture = _load_json("synthetic_pressure_mismatch_checkpoint_trace_v76_oracle.json")
    trace = SyntheticPressureMismatchCheckpointTrace.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert trace.source_kind == "local_hybrid_fixture"
    assert len(trace.checkpoints) == 1
    assert trace.checkpoints[0].checkpoint_class == "oracle_needed"
    assert trace.checkpoints[0].final_adjudication == "resolved_fail"

    derived = derive_v39e_checkpoint_trace(
        local_hybrid_fixture_reference=DEFAULT_V39E_LOCAL_HYBRID_ORACLE_FIXTURE_PATH,
        oracle_request_reference_fixture=(
            "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus76/"
            "synthetic_pressure_mismatch_oracle_request_v76_reference.json"
        ),
        oracle_resolution_reference_fixture=(
            "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus76/"
            "synthetic_pressure_mismatch_oracle_resolution_v76_reference.json"
        ),
        repository_root=_repo_root(),
    )
    assert (
        canonicalize_synthetic_pressure_mismatch_checkpoint_trace_payload(
            derived.model_dump(mode="json", exclude_none=True),
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v39e_human_trace_fixture_validates_and_replays() -> None:
    fixture = _load_json("synthetic_pressure_mismatch_checkpoint_trace_v76_human.json")
    trace = SyntheticPressureMismatchCheckpointTrace.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert trace.source_kind == "local_hybrid_fixture"
    assert trace.checkpoints[0].checkpoint_class == "human_needed"
    assert trace.checkpoints[0].final_adjudication == "escalated_human"

    derived = derive_v39e_checkpoint_trace(
        local_hybrid_fixture_reference=DEFAULT_V39E_LOCAL_HYBRID_HUMAN_FIXTURE_PATH,
        repository_root=_repo_root(),
    )
    assert (
        canonicalize_synthetic_pressure_mismatch_checkpoint_trace_payload(
            derived.model_dump(mode="json", exclude_none=True),
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v39e_oracle_trace_fails_closed_for_invalid_replay_identity_fixture() -> None:
    payload = _load_json(
        "synthetic_pressure_mismatch_oracle_resolution_v76_invalid_replay_identity.json"
    )

    with pytest.raises(
        ValidationError,
        match=(
            "request_replay_identity_sha256 must match the referenced request replay identity"
        ),
    ):
        SyntheticPressureMismatchOracleResolution.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v39e_contradictory_resolution_escalates_human() -> None:
    contradictory_resolution = derive_v39e_oracle_resolution(
        "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus76/"
        "synthetic_pressure_mismatch_oracle_request_v76_reference.json",
        resolution_disposition="contradictory",
        advisory_summary=(
            "The advisory output contradicts itself and cannot support a stable "
            "checkpoint disposition."
        ),
        raw_output_text=(
            "contradictory: the comment is both necessary domain context and also mere "
            "narration."
        ),
        repository_root=_repo_root(),
    )

    assert contradictory_resolution.resolution_disposition == "contradictory"
    assert contradictory_resolution.request_replay_identity_sha256


def test_v39e_can_bind_directly_to_released_conformance_findings() -> None:
    trace = derive_v39e_checkpoint_trace(
        conformance_report_reference_fixture=(
            "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/"
            "synthetic_pressure_mismatch_conformance_report_v74_reference.json"
        ),
        repository_root=_repo_root(),
    )

    assert trace.source_kind == "released_conformance_finding"
    assert len(trace.checkpoints) == 1
    assert trace.checkpoints[0].source_finding_id is not None


def test_v39e_exported_schemas_accept_reference_fixtures_and_reject_bad_transition() -> None:
    request_validator = _load_exported_schema("synthetic_pressure_mismatch_oracle_request.v1.json")
    resolution_validator = _load_exported_schema(
        "synthetic_pressure_mismatch_oracle_resolution.v1.json"
    )
    trace_validator = _load_exported_schema("synthetic_pressure_mismatch_checkpoint_trace.v1.json")

    request = _load_json("synthetic_pressure_mismatch_oracle_request_v76_reference.json")
    resolution = _load_json("synthetic_pressure_mismatch_oracle_resolution_v76_reference.json")
    deterministic_trace = _load_json(
        "synthetic_pressure_mismatch_checkpoint_trace_v76_deterministic.json"
    )
    oracle_trace = _load_json("synthetic_pressure_mismatch_checkpoint_trace_v76_oracle.json")
    human_trace = _load_json("synthetic_pressure_mismatch_checkpoint_trace_v76_human.json")

    assert request_validator.is_valid(request)
    assert resolution_validator.is_valid(resolution)
    assert trace_validator.is_valid(deterministic_trace)
    assert trace_validator.is_valid(oracle_trace)
    assert trace_validator.is_valid(human_trace)

    bad_transition = _load_json("synthetic_pressure_mismatch_checkpoint_trace_v76_human.json")
    bad_transition["checkpoints"][0]["final_adjudication"] = "resolved_fail"  # type: ignore[index]
    assert not trace_validator.is_valid(bad_transition)
