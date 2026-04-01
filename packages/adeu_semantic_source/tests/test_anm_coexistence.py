from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_semantic_source import AnmCompileError, build_v47c_coexistence_profile


def _fixture_path_v47c(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v47c" / name


def _read_text_v47c(name: str) -> str:
    return _fixture_path_v47c(name).read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _read_spec(name: str) -> dict[str, object]:
    return _read_json(_fixture_path_v47c(name))


def _read_commitments_fixture_v47c(name: str) -> dict[str, object]:
    path = (
        Path(__file__).resolve().parents[2]
        / "adeu_commitments_ir"
        / "tests"
        / "fixtures"
        / "v47c"
        / name
    )
    return _read_json(path)


def _source_docs() -> dict[str, str]:
    base = "packages/adeu_semantic_source/tests/fixtures/v47c"
    return {
        f"{base}/standalone_policy.adeu.md": _read_text_v47c("standalone_policy.adeu.md"),
        f"{base}/companion_policy.md": _read_text_v47c("companion_policy.md"),
    }


def test_v47c_reference_profile_replays_deterministically() -> None:
    spec = _read_spec("reference_coexistence_spec.json")

    profile = build_v47c_coexistence_profile(
        snapshot_id=spec["snapshot_id"],
        source_scope_profile=spec["source_scope_profile"],
        released_stack_refs=spec["released_stack_refs"],
        source_docs=_source_docs(),
        source_row_specs=spec["source_row_specs"],
        migration_discipline=spec["migration_discipline"],
        adoption_boundary_rows=spec["adoption_boundary_rows"],
        host_registry=spec["host_registry"],
    )

    assert profile.model_dump(mode="json", exclude_none=True) == _read_commitments_fixture_v47c(
        "reference_anm_markdown_coexistence_profile.json"
    )


def test_v47c_rejects_inconsistent_supersession_spec() -> None:
    spec = _read_spec("reject_inconsistent_supersession_spec.json")

    with pytest.raises(
        AnmCompileError,
        match="requires_later_lock_for_supersession must match",
    ):
        build_v47c_coexistence_profile(
            snapshot_id=spec["snapshot_id"],
            source_scope_profile=spec["source_scope_profile"],
            released_stack_refs=spec["released_stack_refs"],
            source_docs=_source_docs(),
            source_row_specs=spec["source_row_specs"],
            migration_discipline=spec["migration_discipline"],
            adoption_boundary_rows=spec["adoption_boundary_rows"],
            host_registry=spec["host_registry"],
        )


def test_v47c_rejects_orphaned_host_linkage() -> None:
    spec = _read_spec("reject_orphaned_host_spec.json")

    with pytest.raises(AnmCompileError, match="host_or_companion_ref .* orphaned"):
        build_v47c_coexistence_profile(
            snapshot_id=spec["snapshot_id"],
            source_scope_profile=spec["source_scope_profile"],
            released_stack_refs=spec["released_stack_refs"],
            source_docs=_source_docs(),
            source_row_specs=spec["source_row_specs"],
            migration_discipline=spec["migration_discipline"],
            adoption_boundary_rows=spec["adoption_boundary_rows"],
            host_registry=spec["host_registry"],
        )


def test_v47c_rejects_stale_or_contradictory_host_linkage() -> None:
    spec = _read_spec("reject_stale_or_contradictory_host_spec.json")

    with pytest.raises(AnmCompileError, match="host_or_companion_ref .* stale"):
        build_v47c_coexistence_profile(
            snapshot_id=spec["snapshot_id"],
            source_scope_profile=spec["source_scope_profile"],
            released_stack_refs=spec["released_stack_refs"],
            source_docs=_source_docs(),
            source_row_specs=spec["source_row_specs"],
            migration_discipline=spec["migration_discipline"],
            adoption_boundary_rows=spec["adoption_boundary_rows"],
            host_registry=spec["host_registry"],
        )


def test_v47c_rejects_contradictory_host_authority_kind() -> None:
    spec = _read_spec("reference_coexistence_spec.json")
    spec["host_registry"][0]["authority_surface_kind"] = "anm_source"

    with pytest.raises(
        AnmCompileError,
        match="host_or_companion_ref .* incompatible authority posture",
    ):
        build_v47c_coexistence_profile(
            snapshot_id=spec["snapshot_id"],
            source_scope_profile=spec["source_scope_profile"],
            released_stack_refs=spec["released_stack_refs"],
            source_docs=_source_docs(),
            source_row_specs=spec["source_row_specs"],
            migration_discipline=spec["migration_discipline"],
            adoption_boundary_rows=spec["adoption_boundary_rows"],
            host_registry=spec["host_registry"],
        )


def test_v47c_rejects_boundary_action_drift_spec() -> None:
    spec = _read_spec("reject_boundary_action_drift_spec.json")

    with pytest.raises(AnmCompileError):
        build_v47c_coexistence_profile(
            snapshot_id=spec["snapshot_id"],
            source_scope_profile=spec["source_scope_profile"],
            released_stack_refs=spec["released_stack_refs"],
            source_docs=_source_docs(),
            source_row_specs=spec["source_row_specs"],
            migration_discipline=spec["migration_discipline"],
            adoption_boundary_rows=spec["adoption_boundary_rows"],
            host_registry=spec["host_registry"],
        )
