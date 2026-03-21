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
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _fixtures_root() -> Path:
    root = repo_root(anchor=Path(__file__))
    return root / "apps" / "api" / "fixtures" / "synthetic_pressure_mismatch" / "vnext_plus73"


def _load_json(name: str) -> dict[str, object]:
    return json.loads((_fixtures_root() / name).read_text(encoding="utf-8"))


def _load_exported_schema() -> Draft202012Validator:
    root = repo_root(anchor=Path(__file__))
    schema = json.loads(
        (
            root
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / "synthetic_pressure_mismatch_rule_registry.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


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


def test_v39b_exported_schema_rejects_empty_registry_and_empty_rule_arrays() -> None:
    validator = _load_exported_schema()

    empty_registry = _load_json("synthetic_pressure_mismatch_rule_registry_v73_reference.json")
    empty_registry["rules"] = []  # type: ignore[index]
    assert not validator.is_valid(empty_registry)

    empty_subjects = _load_json("synthetic_pressure_mismatch_rule_registry_v73_reference.json")
    empty_subjects["rules"][0]["applicable_subject_kinds"] = []  # type: ignore[index]
    assert not validator.is_valid(empty_subjects)

    empty_utilities = _load_json("synthetic_pressure_mismatch_rule_registry_v73_reference.json")
    empty_utilities["rules"][0]["expected_utility_gains"] = []  # type: ignore[index]
    assert not validator.is_valid(empty_utilities)


def test_v39b_exported_schema_rejects_safe_autofix_contract_violations() -> None:
    validator = _load_exported_schema()

    wrong_route = _load_json("synthetic_pressure_mismatch_rule_registry_v73_reference.json")
    wrong_route["rules"][0]["resolution_route"] = "oracle_assisted"  # type: ignore[index]
    assert not validator.is_valid(wrong_route)

    shape_regular_autofix = _load_json(
        "synthetic_pressure_mismatch_rule_registry_v73_reference.json"
    )
    shape_regular_autofix["rules"][3]["allowed_action"] = "safe_autofix"  # type: ignore[index]
    shape_regular_autofix["rules"][3]["evidence_regime"] = "deterministic_local"  # type: ignore[index]
    shape_regular_autofix["rules"][3]["resolution_route"] = "deterministic_only"  # type: ignore[index]
    assert not validator.is_valid(shape_regular_autofix)


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
