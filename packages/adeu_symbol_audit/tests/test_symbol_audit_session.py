from __future__ import annotations

import json
from pathlib import Path

from adeu_symbol_audit import (
    SymbolAuditSession,
    SymbolAuditSessionConfig,
    SymbolSemanticAudit,
    build_manifest_to_census_coverage_report,
    build_reference_architecture_ir_scope_manifest,
    build_symbol_audit_session,
    build_symbol_audit_session_config,
    build_symbol_census,
    build_symbol_semantic_audit,
)


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def _fixture_path(version: str, name: str) -> Path:
    return Path(__file__).parent / "fixtures" / version / name


def _read_json(version: str, name: str) -> dict[str, object]:
    return json.loads(_fixture_path(version, name).read_text(encoding="utf-8"))


def _released_stack() -> tuple[object, object, object, object]:
    manifest = build_reference_architecture_ir_scope_manifest(repo_root=_repo_root())
    census = build_symbol_census(repo_root=_repo_root(), scope_manifest=manifest)
    coverage = build_manifest_to_census_coverage_report(scope_manifest=manifest, census=census)
    audit = build_symbol_semantic_audit(
        repo_root=_repo_root(),
        census=census,
        coverage_report=coverage,
    )
    return manifest, census, coverage, audit


def test_reference_symbol_audit_session_configs_replay_deterministically() -> None:
    for fixture_name in (
        "reference_symbol_audit_session_config_text.json",
        "reference_symbol_audit_session_config_json.json",
    ):
        payload = _read_json("v50c", fixture_name)
        model = SymbolAuditSessionConfig.model_validate(payload)

        assert model.model_dump(mode="json", by_alias=True, exclude_none=True) == payload


def test_reference_symbol_audit_sessions_replay_deterministically() -> None:
    for fixture_name in (
        "reference_symbol_audit_session_text.json",
        "reference_symbol_audit_session_json.json",
    ):
        payload = _read_json("v50c", fixture_name)
        model = SymbolAuditSession.model_validate(payload)

        assert model.model_dump(mode="json", by_alias=True, exclude_none=True) == payload


def test_reference_symbol_audit_session_text_matches_fixture() -> None:
    manifest, census, coverage, audit = _released_stack()
    session_config = build_symbol_audit_session_config(
        session_mode="read_only_helper_render",
        output_format="text",
        include_evidence_refs=False,
    )

    session = build_symbol_audit_session(
        scope_manifest=manifest,
        census=census,
        coverage_report=coverage,
        semantic_audit=audit,
        session_config=session_config,
    )

    assert session.model_dump(mode="json", by_alias=True, exclude_none=True) == _read_json(
        "v50c",
        "reference_symbol_audit_session_text.json",
    )


def test_reference_symbol_audit_session_json_matches_fixture() -> None:
    manifest, census, coverage, audit = _released_stack()
    session_config = build_symbol_audit_session_config(
        session_mode="read_only_helper_render",
        output_format="json",
        include_evidence_refs=True,
    )

    session = build_symbol_audit_session(
        scope_manifest=manifest,
        census=census,
        coverage_report=coverage,
        semantic_audit=audit,
        session_config=session_config,
    )

    assert session.model_dump(mode="json", by_alias=True, exclude_none=True) == _read_json(
        "v50c",
        "reference_symbol_audit_session_json.json",
    )


def test_symbol_audit_session_fail_closed_on_census_audit_mismatch() -> None:
    manifest, census, coverage, audit = _released_stack()
    session_config = build_symbol_audit_session_config(
        session_mode="read_only_helper_render",
        output_format="text",
        include_evidence_refs=False,
    )
    mismatched_audit = audit.model_copy(
        update={"scope_manifest_ref": "scope_manifest:0000000000000000"},
        deep=True,
    )

    session = build_symbol_audit_session(
        scope_manifest=manifest,
        census=census,
        coverage_report=coverage,
        semantic_audit=mismatched_audit,
        session_config=session_config,
    )

    assert session.session_status == "fail_closed_input_mismatch"
    assert session.exit_code == 1
    assert "semantic audit scope_manifest_ref" in session.rendered_output


def test_symbol_audit_session_fail_closed_on_invalid_output_format() -> None:
    manifest, census, coverage, audit = _released_stack()

    session = build_symbol_audit_session(
        scope_manifest=manifest,
        census=census,
        coverage_report=coverage,
        semantic_audit=audit,
        session_config={
            "session_mode": "read_only_helper_render",
            "output_format": "yaml",
            "include_evidence_refs": False,
        },
    )

    assert session.session_status == "fail_closed_invalid_config"
    assert session.exit_code == 2
    assert "output_format must equal one of: json, text" in session.rendered_output


def test_symbol_audit_session_hash_tracks_rendered_output_format() -> None:
    manifest, census, coverage, audit = _released_stack()
    text_session = build_symbol_audit_session(
        scope_manifest=manifest,
        census=census,
        coverage_report=coverage,
        semantic_audit=audit,
        session_config=build_symbol_audit_session_config(
            session_mode="read_only_helper_render",
            output_format="text",
            include_evidence_refs=False,
        ),
    )
    json_session = build_symbol_audit_session(
        scope_manifest=manifest,
        census=census,
        coverage_report=coverage,
        semantic_audit=audit,
        session_config=build_symbol_audit_session_config(
            session_mode="read_only_helper_render",
            output_format="json",
            include_evidence_refs=True,
        ),
    )

    assert text_session.session_status == "completed_clean"
    assert json_session.session_status == "completed_clean"
    assert text_session.rendered_output != json_session.rendered_output
    assert text_session.session_hash != json_session.session_hash


def test_symbol_audit_session_preserves_released_audit_independence_posture() -> None:
    payload = _read_json("v50b", "reference_symbol_semantic_audit.json")
    audit = SymbolSemanticAudit.model_validate(payload)

    assert audit.semantic_vocabulary_posture == "explicit_independence_from_v49"
