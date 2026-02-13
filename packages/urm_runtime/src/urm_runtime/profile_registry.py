from __future__ import annotations

import importlib.resources as resources
import json
import os
from pathlib import Path
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, ValidationError, field_validator, model_validator

from .errors import URMError

PROFILE_REGISTRY_SCHEMA = "policy.profiles.v1"
PROFILE_REGISTRY_FILE = "profiles.v1.json"


class PolicyProfileEntry(BaseModel):
    model_config = ConfigDict(extra="forbid")

    profile_id: str = Field(min_length=1)
    profile_version: str = Field(min_length=1)
    default_policy_hash: str = Field(pattern=r"^[a-f0-9]{64}$")
    allowed_policy_hashes: list[str] = Field(default_factory=list)
    policy_ref: str = Field(min_length=1)

    @field_validator("profile_id", "profile_version", "policy_ref")
    @classmethod
    def _normalize_strings(cls, value: str) -> str:
        return value.strip()

    @field_validator("allowed_policy_hashes")
    @classmethod
    def _normalize_allowed_hashes(cls, value: list[str]) -> list[str]:
        normalized = sorted({item.strip() for item in value if item and item.strip()})
        if not normalized:
            raise ValueError("allowed_policy_hashes must not be empty")
        for item in normalized:
            if len(item) != 64 or any(ch not in "0123456789abcdef" for ch in item):
                raise ValueError("allowed_policy_hashes must contain lowercase sha256 hex values")
        return normalized

    @model_validator(mode="after")
    def _validate_default_hash_allowed(self) -> "PolicyProfileEntry":
        if self.default_policy_hash not in self.allowed_policy_hashes:
            raise ValueError("default_policy_hash must be included in allowed_policy_hashes")
        return self


class PolicyProfileRegistry(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: Literal[PROFILE_REGISTRY_SCHEMA] = Field(
        alias="schema",
        serialization_alias="schema",
    )
    profiles: list[PolicyProfileEntry] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_unique_profile_ids(self) -> "PolicyProfileRegistry":
        seen: set[str] = set()
        duplicates: list[str] = []
        for profile in self.profiles:
            if profile.profile_id in seen:
                duplicates.append(profile.profile_id)
            seen.add(profile.profile_id)
        if duplicates:
            raise ValueError(f"duplicate profile_id values: {sorted(set(duplicates))}")
        return self

    def sorted_profiles(self) -> list[PolicyProfileEntry]:
        return sorted(self.profiles, key=lambda profile: profile.profile_id)

    def profile_ids(self) -> list[str]:
        return [profile.profile_id for profile in self.sorted_profiles()]

    def get_profile(self, profile_id: str) -> PolicyProfileEntry:
        normalized = profile_id.strip()
        for profile in self.profiles:
            if profile.profile_id == normalized:
                return profile
        raise URMError(
            code="URM_POLICY_PROFILE_NOT_FOUND",
            message="profile is not defined in registry",
            context={
                "profile_id": profile_id,
                "supported_profile_ids": self.profile_ids(),
            },
        )


def _discover_repo_root(anchor: Path) -> Path | None:
    for parent in anchor.parents:
        if (parent / ".git").exists():
            return parent
    return None


def _repo_relative_path(*parts: str) -> Path | None:
    repo_root = _discover_repo_root(Path(__file__).resolve())
    if repo_root is None:
        return None
    return (repo_root.joinpath(*parts)).resolve()


def _load_json_from_path(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise URMError(
            code="URM_POLICY_PROFILE_MAPPING_INVALID",
            message="policy profile registry file not found",
            context={"path": str(path)},
        ) from exc
    except json.JSONDecodeError as exc:
        raise URMError(
            code="URM_POLICY_PROFILE_MAPPING_INVALID",
            message="policy profile registry file is invalid JSON",
            context={"path": str(path), "error": str(exc)},
        ) from exc
    except OSError as exc:
        raise URMError(
            code="URM_POLICY_PROFILE_MAPPING_INVALID",
            message="failed reading policy profile registry file",
            context={"path": str(path), "error": str(exc)},
        ) from exc
    if not isinstance(payload, dict):
        raise URMError(
            code="URM_POLICY_PROFILE_MAPPING_INVALID",
            message="policy profile registry must be a JSON object",
            context={"path": str(path)},
        )
    return payload


def _load_packaged_registry() -> dict[str, Any]:
    resource = resources.files("urm_runtime.policy").joinpath(PROFILE_REGISTRY_FILE)
    try:
        payload = json.loads(resource.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise URMError(
            code="URM_POLICY_PROFILE_MAPPING_INVALID",
            message="packaged policy profile registry is missing",
            context={"resource": PROFILE_REGISTRY_FILE},
        ) from exc
    except json.JSONDecodeError as exc:
        raise URMError(
            code="URM_POLICY_PROFILE_MAPPING_INVALID",
            message="packaged policy profile registry is invalid JSON",
            context={"resource": PROFILE_REGISTRY_FILE, "error": str(exc)},
        ) from exc
    if not isinstance(payload, dict):
        raise URMError(
            code="URM_POLICY_PROFILE_MAPPING_INVALID",
            message="packaged policy profile registry must be a JSON object",
            context={"resource": PROFILE_REGISTRY_FILE},
        )
    return payload


def load_policy_profile_registry(
    *,
    profile_registry_path: Path | None = None,
) -> PolicyProfileRegistry:
    if profile_registry_path is not None:
        payload = _load_json_from_path(profile_registry_path)
    else:
        env_path = os.environ.get("URM_POLICY_PROFILES_PATH", "").strip()
        if env_path:
            payload = _load_json_from_path(Path(env_path).expanduser().resolve())
        else:
            repo_path = _repo_relative_path("policy", PROFILE_REGISTRY_FILE)
            if repo_path is not None and repo_path.exists():
                payload = _load_json_from_path(repo_path)
            else:
                payload = _load_packaged_registry()
    try:
        return PolicyProfileRegistry.model_validate(payload)
    except ValidationError as exc:
        raise URMError(
            code="URM_POLICY_PROFILE_MAPPING_INVALID",
            message="policy profile registry validation failed",
            context={"error": str(exc)},
        ) from exc


def list_policy_profiles(
    *,
    registry: PolicyProfileRegistry | None = None,
) -> list[PolicyProfileEntry]:
    resolved = registry or load_policy_profile_registry()
    return resolved.sorted_profiles()
