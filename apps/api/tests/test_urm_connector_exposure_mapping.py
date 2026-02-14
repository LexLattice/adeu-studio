from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator
from urm_runtime.connector_exposure_mapping import (
    CONNECTOR_EXPOSURE_CAPABILITY_DENY_CODE,
    derive_connector_exposure,
    load_connector_exposure_mapping,
)
from urm_runtime.errors import URMError


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("repository root not found")


def test_connector_exposure_mapping_file_matches_spec_schema() -> None:
    root = _repo_root()
    mapping_payload = json.loads(
        (root / "policy" / "connector_exposure_mapping.v1.json").read_text(encoding="utf-8")
    )
    schema_payload = json.loads(
        (
            root / "spec" / "policy_connector_exposure_mapping.v1.schema.json"
        ).read_text(encoding="utf-8")
    )
    validator = Draft202012Validator(schema_payload)
    errors = sorted(validator.iter_errors(mapping_payload), key=lambda err: str(err.path))
    assert errors == []


def test_connector_exposure_mapping_packaged_copy_matches_repo_source() -> None:
    root = _repo_root()
    source_payload = json.loads(
        (root / "policy" / "connector_exposure_mapping.v1.json").read_text(encoding="utf-8")
    )
    packaged_payload = json.loads(
        (
            root
            / "packages"
            / "urm_runtime"
            / "src"
            / "urm_runtime"
            / "policy"
            / "connector_exposure_mapping.v1.json"
        ).read_text(encoding="utf-8")
    )
    assert packaged_payload == source_payload


def test_derive_connector_exposure_is_deterministic_and_sorted() -> None:
    mapping = load_connector_exposure_mapping()
    connectors = [
        {"id": "zeta", "name": "Zeta"},
        {"id": "omega", "name": "Omega"},
        {"id": "alpha", "name": "Alpha"},
    ]
    exposed, detail = derive_connector_exposure(
        connectors=connectors,
        role_capabilities={"read_state"},
        mapping=mapping,
    )
    assert [item.get("id") for item in exposed] == ["alpha", "zeta"]
    assert [item.get("connector_id") for item in detail] == ["alpha", "omega", "zeta"]
    omega = next(item for item in detail if item.get("connector_id") == "omega")
    assert omega["exposed"] is False
    assert omega["deny_reason_code"] == "URM_CONNECTOR_EXPOSURE_UNMAPPED"
    assert omega["matched_rule_id"] is None


def test_derive_connector_exposure_requires_capability() -> None:
    mapping = load_connector_exposure_mapping()
    exposed, detail = derive_connector_exposure(
        connectors=[{"id": "alpha", "name": "Alpha"}],
        role_capabilities=set(),
        mapping=mapping,
    )
    assert exposed == []
    assert detail == [
        {
            "connector_id": "alpha",
            "exposed": False,
            "deny_reason_code": CONNECTOR_EXPOSURE_CAPABILITY_DENY_CODE,
            "matched_rule_id": "allow_alpha_read_state",
            "missing_capabilities": ["read_state"],
        }
    ]


def test_connector_exposure_mapping_invalid_raises_deterministic_error(tmp_path: Path) -> None:
    invalid_mapping = tmp_path / "connector_exposure_mapping.v1.json"
    invalid_mapping.write_text(
        json.dumps(
            {
                "schema": "policy.connector_exposure_mapping.v1",
                "default_deny_reason_code": "URM_CONNECTOR_EXPOSURE_UNMAPPED",
                "rules": [
                    {
                        "rule_id": "dup",
                        "priority": 1,
                        "match": {"connector_id": "alpha"},
                        "expose": True,
                        "required_capabilities": [],
                        "deny_reason_code": "URM_CONNECTOR_EXPOSURE_DENIED",
                    },
                    {
                        "rule_id": "dup",
                        "priority": 2,
                        "match": {"connector_id": "zeta"},
                        "expose": True,
                        "required_capabilities": [],
                        "deny_reason_code": "URM_CONNECTOR_EXPOSURE_DENIED",
                    },
                ],
            }
        ),
        encoding="utf-8",
    )
    with pytest.raises(URMError) as exc_info:
        load_connector_exposure_mapping(mapping_path=invalid_mapping)
    assert exc_info.value.detail.code == "URM_CONNECTOR_EXPOSURE_MAPPING_INVALID"
