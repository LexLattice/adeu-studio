from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path

import pytest
from adeu_architecture_compiler import (
    ADEU_ARCHITECTURE_ALIGNMENT_REPORT_SCHEMA,
    AdeuArchitectureAlignmentReport,
    canonicalize_adeu_architecture_alignment_report_payload,
    derive_v41e_alignment_report,
)
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v87_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "architecture" / "vnext_plus87"


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v87(name: str) -> dict[str, object]:
    return _load_json(_v87_root() / name)


def _schema_validator() -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_architecture_compiler"
            / "schema"
            / "adeu_architecture_alignment_report.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v41e_alignment_fixture_replays_and_validates() -> None:
    request = _load_v87("adeu_architecture_analysis_request_v87_alignment_derivative.json")
    settlement = _load_v87(
        "adeu_architecture_analysis_settlement_frame_v87_alignment_derivative.json"
    )
    observation = _load_v87(
        "adeu_architecture_observation_frame_v87_alignment_derivative.json"
    )
    semantic_ir = _load_v87("adeu_architecture_semantic_ir_v87_alignment_derivative.json")
    fixture = _load_v87("adeu_architecture_alignment_report_v87_reference.json")

    report = AdeuArchitectureAlignmentReport.model_validate(fixture)

    assert report.schema == ADEU_ARCHITECTURE_ALIGNMENT_REPORT_SCHEMA
    assert report.alignment_posture == "blocked"
    assert report.blocking_finding_ids
    assert report.findings[0].mismatch_class == "unresolved_unknown"

    derived = derive_v41e_alignment_report(
        analysis_request_payload=request,
        analysis_request_path=(
            "apps/api/fixtures/architecture/vnext_plus87/"
            "adeu_architecture_analysis_request_v87_alignment_derivative.json"
        ),
        settlement_frame_payload=settlement,
        settlement_frame_path=(
            "apps/api/fixtures/architecture/vnext_plus87/"
            "adeu_architecture_analysis_settlement_frame_v87_alignment_derivative.json"
        ),
        observation_frame_payload=observation,
        observation_frame_path=(
            "apps/api/fixtures/architecture/vnext_plus87/"
            "adeu_architecture_observation_frame_v87_alignment_derivative.json"
        ),
        semantic_ir_payload=semantic_ir,
        repository_root=_repo_root(),
    )

    assert derived == fixture
    assert (
        canonicalize_adeu_architecture_alignment_report_payload(
            fixture,
            repository_root=_repo_root(),
            analysis_request_payload=request,
            analysis_settlement_payload=settlement,
            observation_frame_payload=observation,
            semantic_ir_payload=semantic_ir,
        )
        == fixture
    )


def test_v41e_exported_schema_accepts_reference_fixture() -> None:
    _schema_validator().validate(_load_v87("adeu_architecture_alignment_report_v87_reference.json"))


def test_v41e_can_emit_aligned_report_when_no_findings_remain() -> None:
    request = _load_v87("adeu_architecture_analysis_request_v87_alignment_derivative.json")
    settlement = _load_v87(
        "adeu_architecture_analysis_settlement_frame_v87_alignment_derivative.json"
    )
    observation = deepcopy(
        _load_v87("adeu_architecture_observation_frame_v87_alignment_derivative.json")
    )
    semantic_ir = _load_v87("adeu_architecture_semantic_ir_v87_alignment_derivative.json")
    observation["unresolved_observations"] = []

    derived = derive_v41e_alignment_report(
        analysis_request_payload=request,
        analysis_request_path=(
            "apps/api/fixtures/architecture/vnext_plus87/"
            "adeu_architecture_analysis_request_v87_alignment_derivative.json"
        ),
        settlement_frame_payload=settlement,
        settlement_frame_path=(
            "apps/api/fixtures/architecture/vnext_plus87/"
            "adeu_architecture_analysis_settlement_frame_v87_alignment_derivative.json"
        ),
        observation_frame_payload=observation,
        observation_frame_path=(
            "apps/api/fixtures/architecture/vnext_plus87/"
            "adeu_architecture_observation_frame_v87_alignment_derivative.json"
        ),
        semantic_ir_payload=semantic_ir,
        repository_root=_repo_root(),
    )

    assert derived["alignment_posture"] == "aligned"
    assert derived["findings"] == []
    assert derived["blocking_finding_ids"] == []
    assert derived["severity_counts"] == {"advisory": 0, "warning": 0, "blocking": 0}


def test_v41e_missing_observability_hook_yields_warning_drift() -> None:
    request = _load_v87("adeu_architecture_analysis_request_v87_alignment_derivative.json")
    settlement = _load_v87(
        "adeu_architecture_analysis_settlement_frame_v87_alignment_derivative.json"
    )
    observation = deepcopy(
        _load_v87("adeu_architecture_observation_frame_v87_alignment_derivative.json")
    )
    semantic_ir = _load_v87("adeu_architecture_semantic_ir_v87_alignment_derivative.json")
    observation["unresolved_observations"] = []
    observation["observed_observability_hooks"] = observation["observed_observability_hooks"][:1]

    derived = derive_v41e_alignment_report(
        analysis_request_payload=request,
        analysis_request_path=(
            "apps/api/fixtures/architecture/vnext_plus87/"
            "adeu_architecture_analysis_request_v87_alignment_derivative.json"
        ),
        settlement_frame_payload=settlement,
        settlement_frame_path=(
            "apps/api/fixtures/architecture/vnext_plus87/"
            "adeu_architecture_analysis_settlement_frame_v87_alignment_derivative.json"
        ),
        observation_frame_payload=observation,
        observation_frame_path=(
            "apps/api/fixtures/architecture/vnext_plus87/"
            "adeu_architecture_observation_frame_v87_alignment_derivative.json"
        ),
        semantic_ir_payload=semantic_ir,
        repository_root=_repo_root(),
    )

    assert derived["alignment_posture"] == "drifted"
    assert derived["blocking_finding_ids"] == []
    assert derived["severity_counts"] == {"advisory": 0, "warning": 1, "blocking": 0}
    assert derived["findings"][0]["mismatch_class"] == "evidence_or_observability_gap"
    assert derived["findings"][0]["basis_kind"] == "missing_observation"
    assert derived["findings"][0]["request_support_refs"] == sorted(
        {
            *request["accepted_doc_refs"],  # type: ignore[index]
            *request["maintainer_brief_refs"],  # type: ignore[index]
        }
    )


def test_v41e_rejects_blocked_settlement_world() -> None:
    request = _load_v87("adeu_architecture_analysis_request_v87_alignment_derivative.json")
    settlement = deepcopy(
        _load_v87("adeu_architecture_analysis_settlement_frame_v87_alignment_derivative.json")
    )
    observation = _load_v87("adeu_architecture_observation_frame_v87_alignment_derivative.json")
    semantic_ir = _load_v87("adeu_architecture_semantic_ir_v87_alignment_derivative.json")
    settlement["compile_entitlement"] = "blocked"
    settlement["blocking_lineage"] = [
        {
            "blocking_ref_id": "blocking_alignment_prereq",
            "blocking_kind": "active_escalation",
            "supporting_refs": ["docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md"],
        }
    ]

    with pytest.raises(ValueError, match="compile_entitlement=entitled"):
        derive_v41e_alignment_report(
            analysis_request_payload=request,
            analysis_request_path=(
                "apps/api/fixtures/architecture/vnext_plus87/"
                "adeu_architecture_analysis_request_v87_alignment_derivative.json"
            ),
            settlement_frame_payload=settlement,
            settlement_frame_path=(
                "apps/api/fixtures/architecture/vnext_plus87/"
                "adeu_architecture_analysis_settlement_frame_v87_alignment_derivative.json"
            ),
            observation_frame_payload=observation,
            observation_frame_path=(
                "apps/api/fixtures/architecture/vnext_plus87/"
                "adeu_architecture_observation_frame_v87_alignment_derivative.json"
            ),
            semantic_ir_payload=semantic_ir,
            repository_root=_repo_root(),
        )


def test_v41e_rejects_finding_id_drift() -> None:
    request = _load_v87("adeu_architecture_analysis_request_v87_alignment_derivative.json")
    settlement = _load_v87(
        "adeu_architecture_analysis_settlement_frame_v87_alignment_derivative.json"
    )
    observation = _load_v87(
        "adeu_architecture_observation_frame_v87_alignment_derivative.json"
    )
    semantic_ir = _load_v87("adeu_architecture_semantic_ir_v87_alignment_derivative.json")
    payload = deepcopy(_load_v87("adeu_architecture_alignment_report_v87_reference.json"))
    payload["findings"][0]["finding_id"] = "ALIGN-UNK-deadbeef"

    with pytest.raises(ValidationError, match="canonical support-tuple hash"):
        canonicalize_adeu_architecture_alignment_report_payload(
            payload,
            repository_root=_repo_root(),
            analysis_request_payload=request,
            analysis_settlement_payload=settlement,
            observation_frame_payload=observation,
            semantic_ir_payload=semantic_ir,
        )


def test_v41e_rejects_prose_only_finding_support() -> None:
    request = _load_v87("adeu_architecture_analysis_request_v87_alignment_derivative.json")
    settlement = _load_v87(
        "adeu_architecture_analysis_settlement_frame_v87_alignment_derivative.json"
    )
    observation = _load_v87(
        "adeu_architecture_observation_frame_v87_alignment_derivative.json"
    )
    semantic_ir = _load_v87("adeu_architecture_semantic_ir_v87_alignment_derivative.json")
    payload = deepcopy(_load_v87("adeu_architecture_alignment_report_v87_reference.json"))
    payload["findings"][0]["intended_refs"] = []
    payload["findings"][0]["observed_refs"] = []
    payload["findings"][0]["request_support_refs"] = []
    payload["findings"][0]["settlement_support_refs"] = []
    payload["findings"][0]["finding_id"] = "ALIGN-UNK-00000000"

    with pytest.raises(ValidationError, match="must resolve to at least one typed"):
        canonicalize_adeu_architecture_alignment_report_payload(
            payload,
            repository_root=_repo_root(),
            analysis_request_payload=request,
            analysis_settlement_payload=settlement,
            observation_frame_payload=observation,
            semantic_ir_payload=semantic_ir,
        )


def test_v41e_rejects_blocking_finding_omitted_from_lineage() -> None:
    request = _load_v87("adeu_architecture_analysis_request_v87_alignment_derivative.json")
    settlement = _load_v87(
        "adeu_architecture_analysis_settlement_frame_v87_alignment_derivative.json"
    )
    observation = _load_v87(
        "adeu_architecture_observation_frame_v87_alignment_derivative.json"
    )
    semantic_ir = _load_v87("adeu_architecture_semantic_ir_v87_alignment_derivative.json")
    payload = deepcopy(_load_v87("adeu_architecture_alignment_report_v87_reference.json"))
    payload["blocking_finding_ids"] = []

    with pytest.raises(ValidationError, match="blocking_finding_ids must match"):
        canonicalize_adeu_architecture_alignment_report_payload(
            payload,
            repository_root=_repo_root(),
            analysis_request_payload=request,
            analysis_settlement_payload=settlement,
            observation_frame_payload=observation,
            semantic_ir_payload=semantic_ir,
        )
