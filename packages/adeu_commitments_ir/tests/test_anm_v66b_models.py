from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_commitments_ir import (
    ANM_MIGRATION_BINDING_PROFILE_SCHEMA,
    ANM_READER_PROJECTION_MANIFEST_SCHEMA,
    ANM_SEMANTIC_DIFF_REPORT_SCHEMA,
    AnmMigrationBindingProfile,
    AnmReaderProjectionManifest,
    AnmSemanticDiffReport,
)
from pydantic import ValidationError


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v66b" / name


def _read_json(name: str) -> dict[str, object]:
    return json.loads(_fixture_path(name).read_text(encoding="utf-8"))


def test_v66b_models_accept_committed_reference_payloads() -> None:
    migration = AnmMigrationBindingProfile.model_validate(
        _read_json("reference_anm_migration_binding_profile.json")
    )
    projection = AnmReaderProjectionManifest.model_validate(
        _read_json("reference_anm_reader_projection_manifest.json")
    )
    diff_report = AnmSemanticDiffReport.model_validate(
        _read_json("reference_anm_semantic_diff_report.json")
    )

    assert migration.schema_id == ANM_MIGRATION_BINDING_PROFILE_SCHEMA
    assert projection.schema_id == ANM_READER_PROJECTION_MANIFEST_SCHEMA
    assert diff_report.schema_id == ANM_SEMANTIC_DIFF_REPORT_SCHEMA


def test_v66b_rejects_standalone_binding_with_companion_refs() -> None:
    payload = _read_json("reference_anm_migration_binding_profile.json")
    payload["binding_rows"][0]["binding_posture"] = "standalone_no_companion"

    with pytest.raises(ValidationError):
        AnmMigrationBindingProfile.model_validate(payload)


def test_v66b_rejects_current_projection_without_hash() -> None:
    payload = _read_json("reference_anm_reader_projection_manifest.json")
    payload["projection_rows"][0]["projection_content_hash_or_none"] = None

    with pytest.raises(ValidationError):
        AnmReaderProjectionManifest.model_validate(payload)


def test_v66b_rejects_initial_diff_with_baseline_ref() -> None:
    payload = _read_json("reference_anm_semantic_diff_report.json")
    payload["baseline_artifact_ref_or_none"] = "artifact:baseline"

    with pytest.raises(ValidationError):
        AnmSemanticDiffReport.model_validate(payload)
