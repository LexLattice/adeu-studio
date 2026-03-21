from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_core_ir import (
    SYNTHETIC_PRESSURE_MISMATCH_RULE_REGISTRY_SCHEMA,
    SyntheticPressureMismatchRuleRegistry,
    canonicalize_synthetic_pressure_mismatch_rule_registry_payload,
)
from adeu_ir.repo import repo_root
from pydantic import ValidationError


def _fixtures_root() -> Path:
    root = repo_root(anchor=Path(__file__))
    return root / "apps" / "api" / "fixtures" / "synthetic_pressure_mismatch" / "vnext_plus73"


def _load_json(name: str) -> dict[str, object]:
    return json.loads((_fixtures_root() / name).read_text(encoding="utf-8"))


def test_v39b_reference_registry_fixture_validates() -> None:
    payload = _load_json("synthetic_pressure_mismatch_rule_registry_v73_reference.json")
    registry = SyntheticPressureMismatchRuleRegistry.model_validate(payload)

    assert registry.schema == SYNTHETIC_PRESSURE_MISMATCH_RULE_REGISTRY_SCHEMA
    assert registry.target_arc == "vNext+73"
    assert registry.target_path == "V39-B"
    assert len(registry.rules) >= 5
    assert registry.rules[0].allowed_action == "safe_autofix"
    assert registry.rules[0].evidence_regime == "deterministic_local"
    assert registry.rules[0].resolution_route == "deterministic_only"


def test_v39b_reference_registry_fixture_round_trips_without_drift() -> None:
    payload = _load_json("synthetic_pressure_mismatch_rule_registry_v73_reference.json")

    assert canonicalize_synthetic_pressure_mismatch_rule_registry_payload(payload) == payload


def test_v39b_registry_rejects_duplicate_rule_id() -> None:
    payload = _load_json("synthetic_pressure_mismatch_rule_registry_v73_reference.json")
    payload["rules"][1]["rule_id"] = payload["rules"][0]["rule_id"]  # type: ignore[index]

    with pytest.raises(ValidationError):
        SyntheticPressureMismatchRuleRegistry.model_validate(payload)


def test_v39b_registry_rejects_empty_rules() -> None:
    payload = _load_json("synthetic_pressure_mismatch_rule_registry_v73_reference.json")
    payload["rules"] = []  # type: ignore[index]

    with pytest.raises(ValidationError):
        SyntheticPressureMismatchRuleRegistry.model_validate(payload)


def test_v39b_registry_rejects_rule_without_applicable_subject_surface() -> None:
    payload = _load_json("synthetic_pressure_mismatch_rule_registry_v73_reference.json")
    payload["rules"][0]["applicable_subject_kinds"] = []  # type: ignore[index]

    with pytest.raises(ValidationError):
        SyntheticPressureMismatchRuleRegistry.model_validate(payload)


def test_v39b_registry_rejects_authorship_signal_kind() -> None:
    payload = _load_json("synthetic_pressure_mismatch_rule_registry_v73_reference.json")
    payload["rules"][0]["signal_kind"] = "authorship_drift"  # type: ignore[index]

    with pytest.raises(ValidationError):
        SyntheticPressureMismatchRuleRegistry.model_validate(payload)
