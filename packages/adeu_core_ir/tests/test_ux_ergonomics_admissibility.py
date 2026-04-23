from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest
from adeu_core_ir import (
    UXErgonomicAdjudicationResult,
    UXErgonomicCaseEnvelope,
    canonicalize_ux_ergonomic_adjudication_result_payload,
    canonicalize_ux_ergonomic_case_envelope_payload,
)
from adeu_ir.repo import repo_root
from pydantic import ValidationError


def _fixtures_root() -> Path:
    root = repo_root(anchor=Path(__file__))
    return root / "apps" / "api" / "fixtures" / "ux_ergonomics" / "vnext_plus185"


def _load_json(name: str) -> dict[str, object]:
    return json.loads((_fixtures_root() / name).read_text(encoding="utf-8"))


def test_v67a_case_envelope_reference_fixture_round_trips() -> None:
    payload = _load_json(
        "ux_ergonomic_case_envelope_artifact_inspector_desktop_maximized_reference.json"
    )

    assert canonicalize_ux_ergonomic_case_envelope_payload(payload) == payload


def test_v67a_reject_case_envelope_visual_angle_requires_admissible_chain() -> None:
    payload = _load_json("reject_ux_ergonomic_case_envelope_dpr_only_visual_angle_required.json")

    with pytest.raises(
        ValidationError,
        match=(
            "visual_angle_reasoning_required must not be true when visual-angle "
            "chain is inadmissible"
        ),
    ):
        UXErgonomicCaseEnvelope.model_validate(payload)


def test_v67a_reject_case_envelope_physical_size_requires_admissible_dpr() -> None:
    payload = copy.deepcopy(
        _load_json("ux_ergonomic_case_envelope_artifact_inspector_desktop_maximized_reference.json")
    )
    payload["device_pixel_ratio_or_none"] = {
        "admissibility": "none",
        "numeric_value": 2.0,
        "provenance_state": "verified_device_inventory",
        "source_kind": "device_inventory",
        "unit": "ratio",
    }
    payload["physical_screen_ppi_or_none"] = {
        "admissibility": "physical_size_admissible",
        "numeric_value": 110.0,
        "provenance_state": "verified_device_inventory",
        "source_kind": "device_inventory",
        "unit": "ppi",
    }
    payload["physical_size_reasoning_required"] = True

    with pytest.raises(
        ValidationError,
        match=(
            "physical_size_reasoning_required must not be true when "
            "physical-size chain is inadmissible"
        ),
    ):
        UXErgonomicCaseEnvelope.model_validate(payload)


def test_v67a_result_validity_is_separate_from_ergonomic_judgment() -> None:
    result = UXErgonomicAdjudicationResult.model_validate(
        _load_json(
            "ux_ergonomic_adjudication_result_artifact_inspector_desktop_maximized_reference.json"
        )
    )

    assert result.report_status == "valid"
    assert result.overall_judgment == "needs_review"


def test_v67a_reject_scalar_preference_scores() -> None:
    payload = _load_json("reject_ux_ergonomic_adjudication_result_scalar_preference_score.json")

    with pytest.raises(ValidationError, match="results cannot export scalar preference scores"):
        canonicalize_ux_ergonomic_adjudication_result_payload(payload)


def test_v67a_result_model_rejects_unknown_candidate_ref() -> None:
    result_path = (
        "ux_ergonomic_adjudication_result_"
        "artifact_inspector_desktop_maximized_reference.json"
    )
    result_payload = copy.deepcopy(
        _load_json(result_path)
    )
    result_payload["blocked_candidate_rows"][0]["candidate_profile_id"] = (
        "artifact_inspector_unknown"
    )

    with pytest.raises(ValidationError, match="candidate_profile_id"):
        UXErgonomicAdjudicationResult.model_validate(result_payload)
