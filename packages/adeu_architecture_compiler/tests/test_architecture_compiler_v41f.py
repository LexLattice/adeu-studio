from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path

import pytest
from adeu_architecture_compiler import (
    ADEU_ARCHITECTURE_ANALYSIS_RUN_MANIFEST_SCHEMA,
    AdeuArchitectureAnalysisRunManifest,
    canonicalize_adeu_architecture_analysis_run_manifest_payload,
    derive_v41f_practical_analysis_run_bundle,
)
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v88_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "architecture" / "vnext_plus88"


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v88(name: str) -> dict[str, object]:
    return _load_json(_v88_root() / name)


def _schema_validator() -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_architecture_compiler"
            / "schema"
            / "adeu_architecture_analysis_run_manifest.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v41f_completed_fixture_replays_and_validates() -> None:
    request = _load_v88("completed_run_outputs/adeu_architecture_analysis_request.json")
    settlement = _load_v88("completed_run_outputs/adeu_architecture_analysis_settlement_frame.json")
    observation = _load_v88("completed_run_outputs/adeu_architecture_observation_frame.json")
    semantic_ir = _load_v88("completed_run_outputs/adeu_architecture_semantic_ir.json")
    alignment = _load_v88("completed_run_outputs/adeu_architecture_alignment_report.json")
    manifest = _load_v88("adeu_architecture_analysis_run_manifest_v88_completed_reference.json")

    validated = AdeuArchitectureAnalysisRunManifest.model_validate(manifest)

    assert validated.schema == ADEU_ARCHITECTURE_ANALYSIS_RUN_MANIFEST_SCHEMA
    assert validated.run_outcome == "completed"
    assert validated.stop_reason_kind == "none"
    assert validated.terminal_alignment_posture == "blocked"
    assert [entry.stage_state for entry in validated.stage_statuses] == [
        "completed",
        "completed",
        "completed",
        "completed",
        "completed",
        "completed",
    ]

    bundle = derive_v41f_practical_analysis_run_bundle(
        analysis_request_payload=request,
        analysis_request_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "completed_run_outputs/adeu_architecture_analysis_request.json"
        ),
        settlement_frame_payload=settlement,
        settlement_frame_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "completed_run_outputs/adeu_architecture_analysis_settlement_frame.json"
        ),
        observation_frame_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "completed_run_outputs/adeu_architecture_observation_frame.json"
        ),
        semantic_ir_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "completed_run_outputs/adeu_architecture_semantic_ir.json"
        ),
        alignment_report_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "completed_run_outputs/adeu_architecture_alignment_report.json"
        ),
        output_root_ref=manifest["output_root_ref"],  # type: ignore[index]
        runtime_evidence_root_ref=manifest["runtime_evidence_root_ref"],  # type: ignore[index]
        repository_root=_repo_root(),
    )

    assert bundle.observation_frame_payload == observation
    assert bundle.semantic_ir_payload == semantic_ir
    assert bundle.alignment_report_payload == alignment
    assert bundle.run_manifest_payload == manifest
    assert (
        canonicalize_adeu_architecture_analysis_run_manifest_payload(
            manifest,
            repository_root=_repo_root(),
            analysis_request_payload=request,
            analysis_settlement_payload=settlement,
            observation_frame_payload=observation,
            semantic_ir_payload=semantic_ir,
            alignment_report_payload=alignment,
        )
        == manifest
    )


def test_v41f_blocked_fixture_replays_and_validates() -> None:
    request = _load_v88("blocked_run_outputs/adeu_architecture_analysis_request.json")
    settlement = _load_v88("blocked_run_outputs/adeu_architecture_analysis_settlement_frame.json")
    observation = _load_v88("blocked_run_outputs/adeu_architecture_observation_frame.json")
    manifest = _load_v88("adeu_architecture_analysis_run_manifest_v88_blocked_reference.json")

    validated = AdeuArchitectureAnalysisRunManifest.model_validate(manifest)

    assert validated.run_outcome == "blocked"
    assert validated.stop_reason_kind == "settlement_blocked"
    assert validated.terminal_alignment_posture == "none"
    assert validated.semantic_ir_id is None
    assert validated.alignment_report_id is None
    assert [entry.stage_state for entry in validated.stage_statuses] == [
        "completed",
        "completed",
        "completed",
        "not_run",
        "not_run",
        "completed",
    ]

    bundle = derive_v41f_practical_analysis_run_bundle(
        analysis_request_payload=request,
        analysis_request_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "blocked_run_outputs/adeu_architecture_analysis_request.json"
        ),
        settlement_frame_payload=settlement,
        settlement_frame_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "blocked_run_outputs/adeu_architecture_analysis_settlement_frame.json"
        ),
        observation_frame_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "blocked_run_outputs/adeu_architecture_observation_frame.json"
        ),
        output_root_ref=manifest["output_root_ref"],  # type: ignore[index]
        runtime_evidence_root_ref=manifest["runtime_evidence_root_ref"],  # type: ignore[index]
        repository_root=_repo_root(),
    )

    assert bundle.observation_frame_payload == observation
    assert bundle.semantic_ir_payload is None
    assert bundle.alignment_report_payload is None
    assert bundle.run_manifest_payload == manifest
    assert (
        canonicalize_adeu_architecture_analysis_run_manifest_payload(
            manifest,
            repository_root=_repo_root(),
            analysis_request_payload=request,
            analysis_settlement_payload=settlement,
            observation_frame_payload=observation,
        )
        == manifest
    )


def test_v41f_exported_schema_accepts_reference_fixtures() -> None:
    validator = _schema_validator()
    validator.validate(_load_v88("adeu_architecture_analysis_run_manifest_v88_completed_reference.json"))
    validator.validate(_load_v88("adeu_architecture_analysis_run_manifest_v88_blocked_reference.json"))


def test_v41f_rejects_stage_ledger_drift() -> None:
    payload = deepcopy(
        _load_v88("adeu_architecture_analysis_run_manifest_v88_completed_reference.json")
    )
    payload["stage_statuses"][3], payload["stage_statuses"][4] = (  # type: ignore[index]
        payload["stage_statuses"][4],
        payload["stage_statuses"][3],
    )

    with pytest.raises(ValidationError, match="canonical stage order"):
        AdeuArchitectureAnalysisRunManifest.model_validate(payload)


def test_v41f_rejects_blocked_terminal_alignment_leak() -> None:
    payload = deepcopy(
        _load_v88("adeu_architecture_analysis_run_manifest_v88_blocked_reference.json")
    )
    payload["terminal_alignment_posture"] = "blocked"

    with pytest.raises(ValidationError, match="terminal_alignment_posture=none"):
        AdeuArchitectureAnalysisRunManifest.model_validate(payload)


def test_v41f_rejects_blocked_shadow_semantic_ref() -> None:
    request = _load_v88("blocked_run_outputs/adeu_architecture_analysis_request.json")
    settlement = _load_v88("blocked_run_outputs/adeu_architecture_analysis_settlement_frame.json")

    with pytest.raises(
        ValueError,
        match="settlement-blocked runs may not supply semantic_ir_ref",
    ):
        derive_v41f_practical_analysis_run_bundle(
            analysis_request_payload=request,
            analysis_request_ref=(
                "apps/api/fixtures/architecture/vnext_plus88/"
                "blocked_run_outputs/adeu_architecture_analysis_request.json"
            ),
            settlement_frame_payload=settlement,
            settlement_frame_ref=(
                "apps/api/fixtures/architecture/vnext_plus88/"
                "blocked_run_outputs/adeu_architecture_analysis_settlement_frame.json"
            ),
            observation_frame_ref=(
                "apps/api/fixtures/architecture/vnext_plus88/"
                "blocked_run_outputs/adeu_architecture_observation_frame.json"
            ),
            semantic_ir_ref=(
                "apps/api/fixtures/architecture/vnext_plus88/"
                "blocked_run_outputs/adeu_architecture_semantic_ir.json"
            ),
            output_root_ref="apps/api/fixtures/architecture/vnext_plus88/blocked_run_outputs",
            runtime_evidence_root_ref="apps/api/fixtures/architecture/vnext_plus88/blocked_run_runtime",
            repository_root=_repo_root(),
        )


def test_v41f_run_id_is_deterministic_and_runner_sensitive() -> None:
    request = _load_v88("completed_run_outputs/adeu_architecture_analysis_request.json")
    settlement = _load_v88("completed_run_outputs/adeu_architecture_analysis_settlement_frame.json")

    first = derive_v41f_practical_analysis_run_bundle(
        analysis_request_payload=request,
        analysis_request_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "completed_run_outputs/adeu_architecture_analysis_request.json"
        ),
        settlement_frame_payload=settlement,
        settlement_frame_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "completed_run_outputs/adeu_architecture_analysis_settlement_frame.json"
        ),
        observation_frame_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "completed_run_outputs/adeu_architecture_observation_frame.json"
        ),
        semantic_ir_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "completed_run_outputs/adeu_architecture_semantic_ir.json"
        ),
        alignment_report_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "completed_run_outputs/adeu_architecture_alignment_report.json"
        ),
        output_root_ref="apps/api/fixtures/architecture/vnext_plus88/completed_run_outputs",
        runtime_evidence_root_ref="apps/api/fixtures/architecture/vnext_plus88/completed_run_runtime",
        repository_root=_repo_root(),
    )
    second = derive_v41f_practical_analysis_run_bundle(
        analysis_request_payload=request,
        analysis_request_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "completed_run_outputs/adeu_architecture_analysis_request.json"
        ),
        settlement_frame_payload=settlement,
        settlement_frame_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "completed_run_outputs/adeu_architecture_analysis_settlement_frame.json"
        ),
        observation_frame_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "completed_run_outputs/adeu_architecture_observation_frame.json"
        ),
        semantic_ir_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "completed_run_outputs/adeu_architecture_semantic_ir.json"
        ),
        alignment_report_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "completed_run_outputs/adeu_architecture_alignment_report.json"
        ),
        output_root_ref="apps/api/fixtures/architecture/vnext_plus88/completed_run_outputs",
        runtime_evidence_root_ref="apps/api/fixtures/architecture/vnext_plus88/completed_run_runtime",
        repository_root=_repo_root(),
    )
    changed = derive_v41f_practical_analysis_run_bundle(
        analysis_request_payload=request,
        analysis_request_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "completed_run_outputs/adeu_architecture_analysis_request.json"
        ),
        settlement_frame_payload=settlement,
        settlement_frame_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "completed_run_outputs/adeu_architecture_analysis_settlement_frame.json"
        ),
        observation_frame_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "completed_run_outputs/adeu_architecture_observation_frame.json"
        ),
        semantic_ir_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "completed_run_outputs/adeu_architecture_semantic_ir.json"
        ),
        alignment_report_ref=(
            "apps/api/fixtures/architecture/vnext_plus88/"
            "completed_run_outputs/adeu_architecture_alignment_report.json"
        ),
        output_root_ref="apps/api/fixtures/architecture/vnext_plus88/completed_run_outputs",
        runtime_evidence_root_ref="apps/api/fixtures/architecture/vnext_plus88/completed_run_runtime",
        runner={"version": "2"},
        repository_root=_repo_root(),
    )

    assert first.run_manifest_payload["run_id"] == second.run_manifest_payload["run_id"]
    assert first.run_manifest_payload["run_id"] != changed.run_manifest_payload["run_id"]
    assert len(first.run_manifest_payload["run_id"]) == len("run_v88_") + 32
