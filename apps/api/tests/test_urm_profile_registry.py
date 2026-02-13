from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator
from urm_runtime.errors import URMError
from urm_runtime.profile_registry import (
    list_policy_profiles,
    load_policy_profile_registry,
)


def _write_json(path: Path, payload: dict[str, object]) -> None:
    path.write_text(json.dumps(payload), encoding="utf-8")


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("repository root not found")


def test_policy_profile_registry_loads_and_lists_deterministically() -> None:
    registry = load_policy_profile_registry()
    profiles = list_policy_profiles(registry=registry)
    profile_ids = [profile.profile_id for profile in profiles]
    assert profile_ids == sorted(profile_ids)
    assert profile_ids == ["default", "experimental", "safe_mode"]
    for profile in profiles:
        assert profile.default_policy_hash in profile.allowed_policy_hashes
        assert profile.policy_ref == "policy/odeu.instructions.v1.json"


def test_policy_profile_registry_file_matches_spec_schema() -> None:
    repo_root = _repo_root()
    profile_payload = json.loads(
        (repo_root / "policy" / "profiles.v1.json").read_text(encoding="utf-8")
    )
    schema_payload = json.loads(
        (repo_root / "spec" / "policy_profiles.v1.schema.json").read_text(encoding="utf-8")
    )
    validator = Draft202012Validator(schema_payload)
    errors = sorted(validator.iter_errors(profile_payload), key=lambda err: str(err.path))
    assert errors == []


def test_policy_profile_registry_invalid_duplicate_profile_ids(tmp_path: Path) -> None:
    profile_path = tmp_path / "profiles.v1.json"
    _write_json(
        profile_path,
        {
            "schema": "policy.profiles.v1",
            "profiles": [
                {
                    "profile_id": "default",
                    "profile_version": "profile.v1",
                    "default_policy_hash": "a" * 64,
                    "allowed_policy_hashes": ["a" * 64],
                    "policy_ref": "policy/one.json",
                },
                {
                    "profile_id": "default",
                    "profile_version": "profile.v1",
                    "default_policy_hash": "a" * 64,
                    "allowed_policy_hashes": ["a" * 64],
                    "policy_ref": "policy/two.json",
                },
            ],
        },
    )
    with pytest.raises(URMError) as exc_info:
        load_policy_profile_registry(profile_registry_path=profile_path)
    assert exc_info.value.detail.code == "URM_POLICY_PROFILE_MAPPING_INVALID"


def test_policy_profile_registry_lookup_unknown_profile_raises_not_found() -> None:
    registry = load_policy_profile_registry()
    with pytest.raises(URMError) as exc_info:
        registry.get_profile("unknown_profile")
    assert exc_info.value.detail.code == "URM_POLICY_PROFILE_NOT_FOUND"
    supported = exc_info.value.detail.context.get("supported_profile_ids", [])
    assert supported == ["default", "experimental", "safe_mode"]
