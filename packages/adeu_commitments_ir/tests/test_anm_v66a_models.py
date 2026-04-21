from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_commitments_ir import (
    ANM_DOC_AUTHORITY_PROFILE_SCHEMA,
    ANM_DOC_CLASS_POLICY_SCHEMA,
    ANM_SOURCE_SET_MANIFEST_SCHEMA,
    AnmDocAuthorityProfile,
    AnmDocClassPolicy,
    AnmSourceSetManifest,
)
from pydantic import ValidationError


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v66a" / name


def _read_json(name: str) -> dict[str, object]:
    return json.loads(_fixture_path(name).read_text(encoding="utf-8"))


def test_v66a_models_accept_committed_reference_payloads() -> None:
    manifest = AnmSourceSetManifest.model_validate(
        _read_json("reference_anm_source_set_manifest.json")
    )
    profile = AnmDocAuthorityProfile.model_validate(
        _read_json("reference_anm_doc_authority_profile.json")
    )
    class_policy = AnmDocClassPolicy.model_validate(
        _read_json("reference_anm_doc_class_policy.json")
    )

    assert manifest.schema_id == ANM_SOURCE_SET_MANIFEST_SCHEMA
    assert profile.schema_id == ANM_DOC_AUTHORITY_PROFILE_SCHEMA
    assert class_policy.schema_id == ANM_DOC_CLASS_POLICY_SCHEMA


def test_v66a_rejects_companion_entry_without_host_registration() -> None:
    payload = _read_json("reference_anm_source_set_manifest.json")
    payload["source_entries"][1]["host_doc_ref_or_none"] = None

    with pytest.raises(ValidationError):
        AnmSourceSetManifest.model_validate(payload)


def test_v66a_rejects_overlapping_allowed_and_forbidden_outputs() -> None:
    payload = _read_json("reference_anm_doc_authority_profile.json")
    payload["forbidden_outputs"] = ["d1_normalized_ir@1"]

    with pytest.raises(ValidationError):
        AnmDocAuthorityProfile.model_validate(payload)
