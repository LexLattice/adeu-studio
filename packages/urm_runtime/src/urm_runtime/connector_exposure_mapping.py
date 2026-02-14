from __future__ import annotations

import importlib.resources as resources
import json
import os
from pathlib import Path
from typing import Annotated, Any, Literal

from pydantic import (
    BaseModel,
    ConfigDict,
    Field,
    StringConstraints,
    ValidationError,
    field_validator,
    model_validator,
)

from .errors import URMError
from .hashing import canonical_json, sha256_canonical_json

CONNECTOR_EXPOSURE_MAPPING_SCHEMA = "policy.connector_exposure_mapping.v1"
CONNECTOR_EXPOSURE_MAPPING_FILE = "connector_exposure_mapping.v1.json"
CONNECTOR_EXPOSURE_CAPABILITY_DENY_CODE = "URM_CONNECTOR_EXPOSURE_CAPABILITY_MISSING"

NonEmptyTrimmedStr = Annotated[
    str,
    StringConstraints(strip_whitespace=True, min_length=1),
]


class ConnectorExposureMatch(BaseModel):
    model_config = ConfigDict(extra="forbid")

    connector_id: NonEmptyTrimmedStr | None = None
    connector_name: NonEmptyTrimmedStr | None = None

    @model_validator(mode="after")
    def _validate_non_empty_match(self) -> "ConnectorExposureMatch":
        if self.connector_id is None and self.connector_name is None:
            raise ValueError("at least one connector match field must be provided")
        return self

    def matches(self, *, connector: dict[str, Any]) -> bool:
        candidate_id = str(connector.get("id", "")).strip()
        candidate_name = str(connector.get("name", "")).strip()
        if self.connector_id is not None and candidate_id != self.connector_id:
            return False
        if self.connector_name is not None and candidate_name != self.connector_name:
            return False
        return True


class ConnectorExposureRule(BaseModel):
    model_config = ConfigDict(extra="forbid")

    rule_id: NonEmptyTrimmedStr
    priority: int = Field(default=100, ge=0)
    match: ConnectorExposureMatch
    expose: bool = False
    required_capabilities: list[NonEmptyTrimmedStr] = Field(default_factory=list)
    deny_reason_code: NonEmptyTrimmedStr = "URM_CONNECTOR_EXPOSURE_DENIED"

    @field_validator("required_capabilities", mode="before")
    @classmethod
    def _normalize_required_capabilities(cls, value: Any) -> list[str]:
        if value is None:
            return []
        if not isinstance(value, list):
            raise ValueError("required_capabilities must be a list")
        normalized: set[str] = set()
        for item in value:
            if not isinstance(item, str):
                raise ValueError("required_capabilities must contain strings")
            stripped = item.strip()
            if stripped:
                normalized.add(stripped)
        return sorted(normalized)


class ConnectorExposureMapping(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: Literal[CONNECTOR_EXPOSURE_MAPPING_SCHEMA] = Field(
        alias="schema",
        serialization_alias="schema",
    )
    default_deny_reason_code: NonEmptyTrimmedStr = "URM_CONNECTOR_EXPOSURE_UNMAPPED"
    rules: list[ConnectorExposureRule] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_unique_rule_ids(self) -> "ConnectorExposureMapping":
        seen: set[str] = set()
        duplicates: set[str] = set()
        for rule in self.rules:
            if rule.rule_id in seen:
                duplicates.add(rule.rule_id)
            seen.add(rule.rule_id)
        if duplicates:
            raise ValueError(f"duplicate connector exposure rule ids: {sorted(duplicates)}")
        return self

    def sorted_rules(self) -> list[ConnectorExposureRule]:
        return sorted(self.rules, key=lambda rule: (rule.priority, rule.rule_id))


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


def _load_json_from_path(path: Path, *, description: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise URMError(
            code="URM_CONNECTOR_EXPOSURE_MAPPING_INVALID",
            message=f"{description} file not found",
            context={"path": str(path)},
        ) from exc
    except json.JSONDecodeError as exc:
        raise URMError(
            code="URM_CONNECTOR_EXPOSURE_MAPPING_INVALID",
            message=f"{description} file is invalid JSON",
            context={"path": str(path), "error": str(exc)},
        ) from exc
    except OSError as exc:
        raise URMError(
            code="URM_CONNECTOR_EXPOSURE_MAPPING_INVALID",
            message=f"failed reading {description} file",
            context={"path": str(path), "error": str(exc)},
        ) from exc
    if not isinstance(payload, dict):
        raise URMError(
            code="URM_CONNECTOR_EXPOSURE_MAPPING_INVALID",
            message=f"{description} must be a JSON object",
            context={"path": str(path)},
        )
    return payload


def _load_packaged_mapping() -> dict[str, Any]:
    resource = resources.files("urm_runtime.policy").joinpath(CONNECTOR_EXPOSURE_MAPPING_FILE)
    try:
        payload = json.loads(resource.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise URMError(
            code="URM_CONNECTOR_EXPOSURE_MAPPING_INVALID",
            message="packaged connector exposure mapping is missing",
            context={"resource": CONNECTOR_EXPOSURE_MAPPING_FILE},
        ) from exc
    except json.JSONDecodeError as exc:
        raise URMError(
            code="URM_CONNECTOR_EXPOSURE_MAPPING_INVALID",
            message="packaged connector exposure mapping is invalid JSON",
            context={"resource": CONNECTOR_EXPOSURE_MAPPING_FILE, "error": str(exc)},
        ) from exc
    if not isinstance(payload, dict):
        raise URMError(
            code="URM_CONNECTOR_EXPOSURE_MAPPING_INVALID",
            message="packaged connector exposure mapping must be a JSON object",
            context={"resource": CONNECTOR_EXPOSURE_MAPPING_FILE},
        )
    return payload


def load_connector_exposure_mapping(
    *,
    mapping_path: Path | None = None,
) -> ConnectorExposureMapping:
    if mapping_path is not None:
        payload = _load_json_from_path(mapping_path, description="connector exposure mapping")
    else:
        env_path = os.environ.get("URM_CONNECTOR_EXPOSURE_MAPPING_PATH", "").strip()
        if env_path:
            payload = _load_json_from_path(
                Path(env_path).expanduser().resolve(),
                description="connector exposure mapping",
            )
        else:
            repo_path = _repo_relative_path("policy", CONNECTOR_EXPOSURE_MAPPING_FILE)
            if repo_path is not None and repo_path.exists():
                payload = _load_json_from_path(
                    repo_path,
                    description="connector exposure mapping",
                )
            else:
                payload = _load_packaged_mapping()
    try:
        return ConnectorExposureMapping.model_validate(payload)
    except ValidationError as exc:
        raise URMError(
            code="URM_CONNECTOR_EXPOSURE_MAPPING_INVALID",
            message="connector exposure mapping validation failed",
            context={"error": str(exc)},
        ) from exc


def _normalized_connector(raw: dict[str, Any]) -> tuple[str, str, dict[str, Any]]:
    normalized = json.loads(canonical_json(raw))
    connector_hash = sha256_canonical_json(normalized)
    connector_id_raw = normalized.get("id")
    connector_id = str(connector_id_raw).strip() if connector_id_raw is not None else ""
    if not connector_id:
        connector_id = f"_anon_{connector_hash[:12]}"
    return connector_id, connector_hash, normalized


def derive_connector_exposure(
    *,
    connectors: list[dict[str, Any]],
    role_capabilities: set[str] | frozenset[str],
    mapping: ConnectorExposureMapping | None = None,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    resolved_mapping = mapping or load_connector_exposure_mapping()
    rules = resolved_mapping.sorted_rules()
    normalized_connectors = [
        _normalized_connector(connector)
        for connector in connectors
        if isinstance(connector, dict)
    ]
    normalized_connectors.sort(key=lambda item: (item[0], item[1]))
    role_cap_set = set(role_capabilities)
    exposed_connectors: list[tuple[str, str, dict[str, Any]]] = []
    exposure_detail: list[dict[str, Any]] = []

    for connector_id, connector_hash, normalized in normalized_connectors:
        matched_rule: ConnectorExposureRule | None = None
        for rule in rules:
            if rule.match.matches(connector=normalized):
                matched_rule = rule
                break
        deny_reason_code: str | None = None
        missing_capabilities: list[str] = []
        exposed = False
        if matched_rule is None:
            deny_reason_code = resolved_mapping.default_deny_reason_code
        else:
            missing_capabilities = sorted(
                capability
                for capability in matched_rule.required_capabilities
                if capability not in role_cap_set
            )
            if missing_capabilities:
                deny_reason_code = CONNECTOR_EXPOSURE_CAPABILITY_DENY_CODE
            elif matched_rule.expose:
                exposed = True
            else:
                deny_reason_code = matched_rule.deny_reason_code
        if exposed:
            exposed_connectors.append((connector_id, connector_hash, normalized))
        detail: dict[str, Any] = {
            "connector_id": connector_id,
            "exposed": exposed,
            "deny_reason_code": deny_reason_code,
            "matched_rule_id": matched_rule.rule_id if matched_rule is not None else None,
        }
        if missing_capabilities:
            detail["missing_capabilities"] = missing_capabilities
        exposure_detail.append(detail)

    exposed_connectors.sort(key=lambda item: (item[0], item[1]))
    exposure_detail.sort(
        key=lambda item: (
            str(item.get("connector_id", "")),
            str(item.get("matched_rule_id", "")),
        )
    )
    return [connector for _, _, connector in exposed_connectors], exposure_detail
