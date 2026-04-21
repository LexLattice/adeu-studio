from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_commitments_ir import (
    ANM_COMPILE_REPORT_SCHEMA,
    ANM_PROSE_BOUNDARY_NOTICE_SET_SCHEMA,
    AnmCompileReport,
    AnmProseBoundaryNoticeSet,
)
from pydantic import ValidationError


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v66c" / name


def _read_json(name: str) -> dict[str, object]:
    return json.loads(_fixture_path(name).read_text(encoding="utf-8"))


def test_v66c_models_accept_committed_reference_payloads() -> None:
    compile_report = AnmCompileReport.model_validate(
        _read_json("reference_anm_compile_report.json")
    )
    notice_set = AnmProseBoundaryNoticeSet.model_validate(
        _read_json("reference_anm_prose_boundary_notice_set.json")
    )

    assert compile_report.schema_id == ANM_COMPILE_REPORT_SCHEMA
    assert notice_set.schema_id == ANM_PROSE_BOUNDARY_NOTICE_SET_SCHEMA


def test_v66c_rejects_valid_report_without_recommendation() -> None:
    payload = _read_json("reference_anm_compile_report.json")
    payload["advisory_result"]["recommended_adoption_posture_or_none"] = None

    with pytest.raises(ValidationError):
        AnmCompileReport.model_validate(payload)


def test_v66c_rejects_normative_notice_with_compiled_authority_block_ref() -> None:
    payload = _read_json("reference_anm_prose_boundary_notice_set.json")
    payload["notice_rows"][0]["compiled_authority_block_ref_or_none"] = "d1:block"

    with pytest.raises(ValidationError):
        AnmProseBoundaryNoticeSet.model_validate(payload)
