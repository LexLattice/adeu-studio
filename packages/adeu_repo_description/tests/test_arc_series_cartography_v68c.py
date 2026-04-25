from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_ARC_CARTOGRAPHY_TOOL_RUN_EVIDENCE_SCHEMA,
    RepoArcCartographyToolRunEvidence,
    derive_v68c_repo_arc_cartography_tool_run_evidence,
)
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v190_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / "vnext_plus190"


def _load_v190(name: str) -> dict[str, Any]:
    return json.loads((_v190_root() / name).read_text(encoding="utf-8"))


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_repo_description" / "schema" / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v190_reference_tool_run_evidence_validates() -> None:
    payload = _load_v190("repo_arc_cartography_tool_run_evidence_v190_reference.json")
    validated = RepoArcCartographyToolRunEvidence.model_validate(payload)

    assert validated.schema == REPO_ARC_CARTOGRAPHY_TOOL_RUN_EVIDENCE_SCHEMA
    assert validated.coordinate_posture == "coordinate_absent_deliberate"
    assert {
        row.applicability_posture for row in validated.tool_run_rows
    } == {
        "applicable_and_supporting",
        "failed_or_inconclusive",
        "namespace_limited",
        "not_run",
    }
    assert {
        row.gap_id for row in validated.gap_resolution_rows
    } == set(validated.v68b_gap_refs)


def test_v190_exported_schema_accepts_reference_fixture() -> None:
    _schema_validator("repo_arc_cartography_tool_run_evidence.v1.json").validate(
        _load_v190("repo_arc_cartography_tool_run_evidence_v190_reference.json")
    )


def test_v190_derivation_helper_matches_reference_fixture() -> None:
    evidence = derive_v68c_repo_arc_cartography_tool_run_evidence(repo_root=_repo_root())

    assert evidence.model_dump(mode="json") == _load_v190(
        "repo_arc_cartography_tool_run_evidence_v190_reference.json"
    )


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_arc_cartography_tool_run_evidence_v190_reject_arc67_as_family_v67_proof.json",
            "ARC=67",
        ),
        (
            "repo_arc_cartography_tool_run_evidence_v190_reject_coordinate_absence_silent_success.json",
            "coordinate absence",
        ),
        (
            "repo_arc_cartography_tool_run_evidence_v190_reject_coordinate_admits_conceptual_diff.json",
            "odeu_conceptual_diff_report",
        ),
        (
            "repo_arc_cartography_tool_run_evidence_v190_reject_coordinate_authorizes_v69.json",
            "future V-family targets beyond V68",
        ),
        (
            "repo_arc_cartography_tool_run_evidence_v190_reject_failed_tool_omitted.json",
            "expected tool invocations",
        ),
        (
            "repo_arc_cartography_tool_run_evidence_v190_reject_passing_tool_global_proof.json",
            "global proof",
        ),
        (
            "repo_arc_cartography_tool_run_evidence_v190_reject_support_doc_as_closeout_evidence.json",
            "support docs",
        ),
        (
            "repo_arc_cartography_tool_run_evidence_v190_reject_unresolved_gap_dropped.json",
            "V68-B gap refs",
        ),
    ],
)
def test_v190_rejects_invalid_tool_run_evidence_fixtures(
    fixture_name: str, match: str
) -> None:
    with pytest.raises(ValidationError, match=match):
        RepoArcCartographyToolRunEvidence.model_validate(_load_v190(fixture_name))


def test_v190_rejects_future_family_target_beyond_original_v69_to_v75_range() -> None:
    payload = deepcopy(_load_v190("repo_arc_cartography_tool_run_evidence_v190_reference.json"))
    payload["coordinate_plan_rows"][0]["target_refs"] = ["family:V76"]

    with pytest.raises(ValidationError, match="future V-family targets beyond V68"):
        RepoArcCartographyToolRunEvidence.model_validate(payload)


def test_v190_rejects_emitted_coordinate_row_under_absent_top_level_posture() -> None:
    payload = deepcopy(_load_v190("repo_arc_cartography_tool_run_evidence_v190_reference.json"))
    payload["coordinate_plan_rows"][0]["coordinate_posture"] = "coordinate_emitted"
    payload["coordinate_plan_rows"][0]["target_refs"] = ["family:V68"]

    with pytest.raises(ValidationError, match="cannot include coordinate emitted rows"):
        RepoArcCartographyToolRunEvidence.model_validate(payload)


def test_v190_arc67_family_guard_does_not_match_v670_substring() -> None:
    payload = deepcopy(_load_v190("repo_arc_cartography_tool_run_evidence_v190_reference.json"))
    payload["tool_run_rows"][0]["target_claim_id"] = "family:V670"
    payload["tool_run_rows"][0]["target_namespace_kind"] = "family_id"

    validated = RepoArcCartographyToolRunEvidence.model_validate(payload)

    assert validated.tool_run_rows[0].target_claim_id == "family:V670"
