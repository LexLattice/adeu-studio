from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_core_ir import (
    SYNTHETIC_PRESSURE_MISMATCH_FIX_PLAN_SCHEMA,
    SyntheticPressureMismatchFixPlan,
    canonicalize_synthetic_pressure_mismatch_fix_plan_payload,
    derive_v39d_fix_plan,
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
        / "vnext_plus75"
    )


def _load_json(name: str) -> dict[str, object]:
    return json.loads((_fixtures_root() / name).read_text(encoding="utf-8"))


def _load_exported_schema() -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / "synthetic_pressure_mismatch_fix_plan.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v39d_reference_fix_plan_fixture_validates_and_replays() -> None:
    fixture = _load_json("synthetic_pressure_mismatch_fix_plan_v75_reference.json")
    plan = SyntheticPressureMismatchFixPlan.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert plan.schema == SYNTHETIC_PRESSURE_MISMATCH_FIX_PLAN_SCHEMA
    assert len(plan.forward_agent_projections) == 1
    assert len(plan.post_optimizer_projections) == 1
    assert plan.post_optimizer_projections[0].plan_posture == "safe_autofix_candidate"

    derived = derive_v39d_fix_plan(
        "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/"
        "synthetic_pressure_mismatch_conformance_report_v74_reference.json",
        repository_root=_repo_root(),
    )
    assert (
        canonicalize_synthetic_pressure_mismatch_fix_plan_payload(
            derived.model_dump(mode="json", exclude_none=True),
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v39d_no_op_fix_plan_fixture_validates_and_replays() -> None:
    fixture = _load_json("synthetic_pressure_mismatch_fix_plan_v75_no_op.json")
    plan = SyntheticPressureMismatchFixPlan.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert plan.forward_agent_projections == []
    assert plan.post_optimizer_projections == []
    assert plan.derivation_metadata.source_finding_ids == []

    derived = derive_v39d_fix_plan(
        "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/"
        "synthetic_pressure_mismatch_conformance_report_v74_no_findings.json",
        repository_root=_repo_root(),
    )
    assert (
        canonicalize_synthetic_pressure_mismatch_fix_plan_payload(
            derived.model_dump(mode="json", exclude_none=True),
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v39d_invalid_unauthorized_route_fixture_fails_closed() -> None:
    payload = _load_json("synthetic_pressure_mismatch_fix_plan_v75_invalid_unauthorized_route.json")

    with pytest.raises(
        ValidationError,
        match=(
            "post_optimizer_projections\\[\\]\\.plan_posture must match the released "
            "conformance route for safe_autofix_candidates"
        ),
    ):
        SyntheticPressureMismatchFixPlan.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v39d_fix_plan_rejects_duplicate_projected_item_id() -> None:
    payload = _load_json("synthetic_pressure_mismatch_fix_plan_v75_reference.json")
    payload["post_optimizer_projections"][0]["projected_item_id"] = payload[  # type: ignore[index]
        "forward_agent_projections"
    ][0]["projected_item_id"]

    with pytest.raises(ValidationError, match="projected_item_id must not contain duplicates"):
        SyntheticPressureMismatchFixPlan.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v39d_fix_plan_rejects_authorship_signal_kind() -> None:
    payload = _load_json("synthetic_pressure_mismatch_fix_plan_v75_reference.json")
    payload["forward_agent_projections"][0]["signal_kind"] = "authorship_drift"  # type: ignore[index]

    with pytest.raises(ValidationError):
        SyntheticPressureMismatchFixPlan.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v39d_fix_plan_rejects_hidden_score_field() -> None:
    payload = _load_json("synthetic_pressure_mismatch_fix_plan_v75_reference.json")
    payload["priority_score"] = 1

    with pytest.raises(ValidationError):
        SyntheticPressureMismatchFixPlan.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v39d_fix_plan_rejects_text_that_deviates_from_released_role_policy() -> None:
    payload = _load_json("synthetic_pressure_mismatch_fix_plan_v75_reference.json")
    payload["post_optimizer_projections"][0]["projected_next_step_text"] = "Apply this edit now."

    with pytest.raises(
        ValidationError,
        match=(
            "post_optimizer_projections\\[\\]\\.projected_next_step_text must equal the "
            "released role policy projection for this route"
        ),
    ):
        SyntheticPressureMismatchFixPlan.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v39d_derived_projection_text_tracks_released_role_policy() -> None:
    plan = derive_v39d_fix_plan(
        "apps/api/fixtures/synthetic_pressure_mismatch/vnext_plus74/"
        "synthetic_pressure_mismatch_conformance_report_v74_reference.json",
        repository_root=_repo_root(),
    )

    assert plan.forward_agent_projections[0].projected_next_step_text == (
        "Avoid adding defensive null checks unless a reachable boundary can supply null."
    )
    assert plan.post_optimizer_projections[0].projected_next_step_text.startswith(
        "Candidate only: "
    )


def test_v39d_exported_schema_accepts_valid_fixtures_and_rejects_bad_projection_kind() -> None:
    validator = _load_exported_schema()

    reference = _load_json("synthetic_pressure_mismatch_fix_plan_v75_reference.json")
    no_op = _load_json("synthetic_pressure_mismatch_fix_plan_v75_no_op.json")
    assert validator.is_valid(reference)
    assert validator.is_valid(no_op)

    bad_kind = _load_json("synthetic_pressure_mismatch_fix_plan_v75_reference.json")
    bad_kind["post_optimizer_projections"][0]["projection_kind"] = "guidance"  # type: ignore[index]
    assert not validator.is_valid(bad_kind)
