from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_core_ir import SyntheticPressureMismatchRuleRegistry
from pydantic import ValidationError


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def _fixture_payload() -> dict[str, object]:
    fixture_path = (
        _repo_root()
        / "apps"
        / "api"
        / "fixtures"
        / "synthetic_pressure_mismatch"
        / "vnext_plus73"
        / "synthetic_pressure_mismatch_rule_registry_v73_reference.json"
    )
    return json.loads(fixture_path.read_text(encoding="utf-8"))


def test_safe_autofix_requires_deterministic_only_route() -> None:
    payload = _fixture_payload()
    payload["rules"][0]["resolution_route"] = "oracle_assisted"  # type: ignore[index]

    with pytest.raises(
        ValidationError,
        match=(
            "rules\\[\\]\\.allowed_action safe_autofix requires "
            "resolution_route deterministic_only"
        ),
    ):
        SyntheticPressureMismatchRuleRegistry.model_validate(payload)


def test_shape_regularity_rule_cannot_claim_safe_autofix() -> None:
    payload = _fixture_payload()
    payload["rules"][3]["allowed_action"] = "safe_autofix"  # type: ignore[index]
    payload["rules"][3]["evidence_regime"] = "deterministic_local"  # type: ignore[index]
    payload["rules"][3]["resolution_route"] = "deterministic_only"  # type: ignore[index]

    with pytest.raises(
        ValidationError,
        match=(
            "rules\\[\\]\\.allowed_action safe_autofix is forbidden for "
            "shape_regularity_drift"
        ),
    ):
        SyntheticPressureMismatchRuleRegistry.model_validate(payload)


def test_meta_intent_rule_rejects_non_meta_subject_kinds() -> None:
    payload = _fixture_payload()
    payload["rules"][4]["applicable_subject_kinds"] = [  # type: ignore[index]
        "code_span",
        "review_note",
    ]

    with pytest.raises(
        ValidationError,
        match="meta_intent_failure rules must use only meta-artifact subject kinds",
    ):
        SyntheticPressureMismatchRuleRegistry.model_validate(payload)


def test_counterexample_policy_requires_structured_non_empty_text() -> None:
    payload = _fixture_payload()
    payload["rules"][2]["counterexample_policy"]["defeating_evidence"] = "   "  # type: ignore[index]

    with pytest.raises(
        ValidationError,
        match="counterexample_policy\\.defeating_evidence must not be empty",
    ):
        SyntheticPressureMismatchRuleRegistry.model_validate(payload)
