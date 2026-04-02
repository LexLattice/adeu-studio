from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_agent_harness.taskpack_binding import (
    AHK5603_CARDINALITY_VIOLATION,
    AHK5605_LINEAGE_MISMATCH,
    AHK5606_PROJECTION_CONFLICT,
    AHK5607_PROMPT_AUTHORITY_DRIFT,
    ANM_TASKPACK_BINDING_PROFILE_SCHEMA,
    AnmTaskpackBindingProfile,
    TaskpackBindingError,
    build_v48a_taskpack_binding_profile,
)
from adeu_ir.repo import repo_root


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v48a" / name


def _read_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _read_spec(name: str) -> dict[str, object]:
    return _read_json(_fixture_path(name))


def _read_reference_profile() -> dict[str, object]:
    return _read_json(_fixture_path("reference_anm_taskpack_binding_profile.json"))


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def test_v48a_reference_profile_replays_deterministically() -> None:
    spec = _read_spec("reference_taskpack_binding_spec.json")

    profile = build_v48a_taskpack_binding_profile(
        **spec,
        repo_root_path=_repo_root(),
    )

    assert profile.model_dump(mode="json", exclude_none=True) == _read_reference_profile()


def test_v48a_model_accepts_committed_reference_payload() -> None:
    profile = AnmTaskpackBindingProfile.model_validate(_read_reference_profile())

    assert profile.schema == ANM_TASKPACK_BINDING_PROFILE_SCHEMA
    assert profile.policy_authority_clause_ref == "release_surface:owner"


def test_v48a_rejects_multiple_policy_sources() -> None:
    spec = _read_spec("reject_multiple_policy_sources_spec.json")

    with pytest.raises(TaskpackBindingError, match=AHK5603_CARDINALITY_VIOLATION):
        build_v48a_taskpack_binding_profile(
            **spec,
            repo_root_path=_repo_root(),
        )


def test_v48a_rejects_mismatched_scope_binding_entry() -> None:
    spec = _read_spec("reject_scope_binding_entry_mismatch_spec.json")

    with pytest.raises(TaskpackBindingError, match=AHK5605_LINEAGE_MISMATCH):
        build_v48a_taskpack_binding_profile(
            **spec,
            repo_root_path=_repo_root(),
        )


def test_v48a_rejects_projection_conflicts() -> None:
    spec = _read_spec("reject_projection_conflict_spec.json")

    with pytest.raises(TaskpackBindingError, match=AHK5606_PROJECTION_CONFLICT):
        build_v48a_taskpack_binding_profile(
            **spec,
            repo_root_path=_repo_root(),
        )


def test_v48a_rejects_prompt_authority_drift() -> None:
    spec = _read_spec("reject_prompt_authority_drift_spec.json")

    with pytest.raises(TaskpackBindingError, match=AHK5607_PROMPT_AUTHORITY_DRIFT):
        build_v48a_taskpack_binding_profile(
            **spec,
            repo_root_path=_repo_root(),
        )
