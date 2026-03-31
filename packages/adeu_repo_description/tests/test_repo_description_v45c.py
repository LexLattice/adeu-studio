from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_ARC_DEPENDENCY_REGISTER_SCHEMA,
    REPO_ARC_DEPENDENCY_REGISTER_V1_SCHEMA,
    RepoArcDependencyRegister,
    RepoArcDependencyRegisterV1,
    compute_repo_arc_dependency_register_id,
    compute_repo_arc_dependency_register_v1_id,
    default_v45c_source_paths,
    derive_v45c_repo_arc_dependency_register,
)
from adeu_repo_description.extract import (
    _extract_selected_v45_path,
    _extract_v45c_corrective_selected_path,
    _validate_v45c_corrective_planning_markers,
)
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v100_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / "vnext_plus100"


def _v102_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / "vnext_plus102"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v100(name: str) -> dict[str, Any]:
    return _load_json(_v100_root() / name)


def _load_v102(name: str) -> dict[str, Any]:
    return _load_json(_v102_root() / name)


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_repo_description" / "schema" / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v100_reference_dependency_register_fixture_still_validates_as_historical_baseline() -> (
    None
):
    accepted_register = _load_v100("repo_arc_dependency_register_v100_reference.json")
    validated = RepoArcDependencyRegisterV1.model_validate(accepted_register)
    assert validated.schema == REPO_ARC_DEPENDENCY_REGISTER_V1_SCHEMA


def test_v100_dependency_register_id_is_deterministic_for_historical_fixture() -> None:
    payload = _load_v100("repo_arc_dependency_register_v100_reference.json")
    without_id = deepcopy(payload)
    without_id.pop("repo_arc_dependency_register_id")
    assert (
        compute_repo_arc_dependency_register_v1_id(without_id)
        == payload["repo_arc_dependency_register_id"]
    )


def test_v100_exported_schema_accepts_reference_fixture() -> None:
    _schema_validator("repo_arc_dependency_register.v1.json").validate(
        _load_v100("repo_arc_dependency_register_v100_reference.json")
    )


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_arc_dependency_register_v100_reject_missing_snapshot_identity.json",
            "Field required",
        ),
        (
            "repo_arc_dependency_register_v100_reject_dangling_dependency_target_arc.json",
            "known open_arc_entries arc_id",
        ),
        (
            "repo_arc_dependency_register_v100_reject_duplicate_edge_identity.json",
            "dependency_edges edge_id values must be unique",
        ),
        (
            "repo_arc_dependency_register_v100_reject_unresolved_blocker_ready_posture.json",
            "ready/deferred readiness_posture may not coexist with unresolved hard blockers",
        ),
        (
            "repo_arc_dependency_register_v100_reject_authority_laundering_scheduling_entitlement.json",
            "register_scope may not carry scheduling or mutation entitlement claims",
        ),
    ],
)
def test_v100_rejects_invalid_reference_fixtures(fixture_name: str, match: str) -> None:
    payload = _load_v100(fixture_name)
    with pytest.raises(ValidationError, match=match):
        RepoArcDependencyRegisterV1.model_validate(payload)


def test_v102_reference_dependency_register_fixture_replays_and_validates() -> None:
    accepted_register = _load_v102("repo_arc_dependency_register_v102_reference.json")
    validated = RepoArcDependencyRegister.model_validate(accepted_register)
    assert validated.schema == REPO_ARC_DEPENDENCY_REGISTER_SCHEMA

    derived_register = derive_v45c_repo_arc_dependency_register(
        source_paths=default_v45c_source_paths(),
        snapshot_validity_posture=accepted_register["snapshot_validity_posture"],
    )
    for key in (
        "repo_arc_dependency_register_id",
        "repo_snapshot_id",
        "repo_snapshot_hash",
        "source_set_hash",
    ):
        accepted_register.pop(key)
        derived_register.pop(key)
    assert derived_register == accepted_register


def test_v102_dependency_register_id_is_deterministic() -> None:
    payload = _load_v102("repo_arc_dependency_register_v102_reference.json")
    without_id = deepcopy(payload)
    without_id.pop("repo_arc_dependency_register_id")
    assert (
        compute_repo_arc_dependency_register_id(without_id)
        == payload["repo_arc_dependency_register_id"]
    )


def test_v102_exported_schema_accepts_reference_fixture() -> None:
    _schema_validator("repo_arc_dependency_register.v2.json").validate(
        _load_v102("repo_arc_dependency_register_v102_reference.json")
    )


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_arc_dependency_register_v102_reject_missing_source_set_provenance.json",
            "Field required",
        ),
        (
            "repo_arc_dependency_register_v102_reject_missing_entry_derivation_posture.json",
            "Field required",
        ),
        (
            "repo_arc_dependency_register_v102_reject_missing_edge_source_artifact_refs.json",
            "Field required",
        ),
        (
            "repo_arc_dependency_register_v102_reject_source_artifact_ref_outside_source_set.json",
            "source_artifact_refs must resolve inside source_set",
        ),
        (
            "repo_arc_dependency_register_v102_reject_blocker_dependency_inconsistency.json",
            "blocked readiness_posture must match unresolved hard incoming dependencies",
        ),
        (
            "repo_arc_dependency_register_v102_reject_missing_cycle_posture.json",
            "Field required",
        ),
        (
            "repo_arc_dependency_register_v102_reject_undefined_pending_list_posture.json",
            "Input should be",
        ),
        (
            "repo_arc_dependency_register_v102_reject_supports_all_three_way_claim.json",
            "Extra inputs are not permitted",
        ),
        (
            "repo_arc_dependency_register_v102_reject_authority_laundering_scheduling_entitlement.json",
            "register_scope may not carry scheduling or mutation entitlement claims",
        ),
    ],
)
def test_v102_rejects_invalid_reference_fixtures(fixture_name: str, match: str) -> None:
    payload = _load_v102(fixture_name)
    with pytest.raises(ValidationError, match=match):
        RepoArcDependencyRegister.model_validate(payload)


def test_v100_selected_path_extraction_accepts_consistent_non_phrase_markers() -> None:
    text = """
## Recommended Family

- Recommended next path for this branch:
  - `V45-C`

## Suggested `V45` Path Ladder

| Path | Theme | Primary output | Status |
|---|---|---|---|
| `V45-B` | symbol catalog + typed dependency graph | candidate outputs | planned_not_selected_yet |
| `V45-C` | open arc/slice dependency register | candidate output | selected_next_branch_local |

## Recommended Next Path (`V45-C`)
"""
    assert _extract_selected_v45_path(text=text) == "V45-C"


def test_v102_corrective_selected_path_extraction_reads_bounded_followup_note() -> None:
    text = """
- Corrective follow-up note on this same planning surface:
  - if released `V45-C` hardening is selected before broader `V45-B` consumers rely on
    `repo_arc_dependency_register@1`, select `V45-C` as the next default candidate for
    that bounded corrective follow-up;
"""
    assert _extract_v45c_corrective_selected_path(text=text) == "V45-C"


def test_v102_corrective_planning_validation_rejects_table_drift() -> None:
    mutated_text = """
## Suggested `V45` Path Ladder

| Path | Theme | Primary output | Status |
|---|---|---|---|
| `V45-B` | symbol catalog + typed dependency graph | candidate outputs | planned |
| `V45-C` | open arc/slice dependency register | candidate output | closed_on_main |
| `V45-D` | test intent matrix | candidate output | selected_next_branch_local |

- Corrective follow-up note on this same planning surface:
  - if released `V45-C` hardening is selected before broader `V45-B` consumers rely on
    `repo_arc_dependency_register@1`, select `V45-C` as the next default candidate for
    that bounded corrective follow-up;
"""
    with pytest.raises(
        ValueError,
        match=(
            "v45c corrective extractor requires V45-B to remain the broader "
            "selected_next_branch_local path in planning"
        ),
    ):
        _validate_v45c_corrective_planning_markers(text=mutated_text)


def test_v102_rejects_cycles_when_cycle_posture_forbids_all_declared_edges() -> None:
    payload = deepcopy(_load_v102("repo_arc_dependency_register_v102_reference.json"))
    payload["dependency_edges"].append(
        {
            "edge_id": "edge:v45-f-to-v45-b",
            "from_arc_id": "V45-F",
            "to_arc_id": "V45-B",
            "dependency_kind": "family_progression",
            "dependency_strength": "soft",
            "dependency_status": "informational",
            "derivation_posture": "derived_deterministically",
            "derivation_method": "deterministic_projection",
            "source_artifact_refs": ["docs/DRAFT_NEXT_ARC_OPTIONS_v28.md"],
            "supporting_evidence_refs": [
                "evidence:planning:v28:row:V45-B",
                "evidence:planning:v28:row:V45-F",
                "evidence:policy:v45c",
            ],
        }
    )

    with pytest.raises(
        ValidationError,
        match="dependency cycles are forbidden under the declared cycle posture",
    ):
        RepoArcDependencyRegister.model_validate(payload)
