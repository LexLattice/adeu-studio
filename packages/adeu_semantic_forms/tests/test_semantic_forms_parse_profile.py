from __future__ import annotations

import json
from pathlib import Path

from adeu_semantic_forms import (
    ADEU_SEMANTIC_PARSE_PROFILE_SCHEMA,
    ADEU_SEMANTIC_TRANSFORM_CONTRACT_SCHEMA,
    SemanticParseProfile,
    SemanticTransformContract,
    build_reference_repo_policy_work_profile,
    build_reference_transform_contract,
)


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v49a" / name


def _read_json(name: str) -> dict[str, object]:
    return json.loads(_fixture_path(name).read_text(encoding="utf-8"))


def test_reference_parse_profile_builder_replays_committed_fixture() -> None:
    fixture = _read_json("reference_semantic_parse_profile.json")

    profile = build_reference_repo_policy_work_profile()

    assert profile.schema == ADEU_SEMANTIC_PARSE_PROFILE_SCHEMA
    assert profile.model_dump(mode="json", by_alias=True, exclude_none=True) == fixture


def test_reference_parse_profile_fixture_validates() -> None:
    fixture = _read_json("reference_semantic_parse_profile.json")

    profile = SemanticParseProfile.model_validate(fixture)

    assert profile.semantic_hash == fixture["semantic_hash"]


def test_reference_transform_contract_builder_replays_committed_fixture() -> None:
    profile = build_reference_repo_policy_work_profile()
    fixture = _read_json("reference_semantic_transform_contract.json")

    contract = build_reference_transform_contract(profile.profile_id)

    assert contract.schema == ADEU_SEMANTIC_TRANSFORM_CONTRACT_SCHEMA
    assert contract.model_dump(mode="json", by_alias=True, exclude_none=True) == fixture


def test_reference_transform_contract_fixture_validates() -> None:
    fixture = _read_json("reference_semantic_transform_contract.json")

    contract = SemanticTransformContract.model_validate(fixture)

    assert contract.semantic_hash == fixture["semantic_hash"]
