from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path

import pytest
from adeu_architecture_compiler import (
    ADEU_ARCHITECTURE_OBSERVATION_FRAME_SCHEMA,
    AdeuArchitectureObservationFrame,
    canonicalize_adeu_architecture_observation_frame_payload,
    derive_v41c_observation_frame,
)
from adeu_architecture_compiler.observation import (
    ObservedObservabilityHook,
    _derive_unresolved_observations,
)
from adeu_architecture_ir import AdeuArchitectureAnalysisRequest
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v85_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "architecture" / "vnext_plus85"


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v85(name: str) -> dict[str, object]:
    return _load_json(_v85_root() / name)


def _schema_validator() -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_architecture_compiler"
            / "schema"
            / "adeu_architecture_observation_frame.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v41c_observation_fixture_validates_and_replays() -> None:
    request = _load_v85("adeu_architecture_analysis_request_v85_observation_derivative.json")
    settlement = _load_v85(
        "adeu_architecture_analysis_settlement_frame_v85_observation_derivative.json"
    )
    fixture = _load_v85("adeu_architecture_observation_frame_v85_reference.json")

    observation = AdeuArchitectureObservationFrame.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )
    assert observation.schema == ADEU_ARCHITECTURE_OBSERVATION_FRAME_SCHEMA
    assert observation.upstream_compile_entitlement == "blocked"
    assert observation.upstream_blocking_refs == [
        "blocking_runtime_signal_unproved",
        "blocking_v41c_governance_gap",
    ]
    assert observation.observed_boundaries[0].crossing_refs == []

    derived = derive_v41c_observation_frame(
        analysis_request_payload=request,
        analysis_request_path=(
            "apps/api/fixtures/architecture/vnext_plus85/"
            "adeu_architecture_analysis_request_v85_observation_derivative.json"
        ),
        settlement_frame_payload=settlement,
        settlement_frame_path=(
            "apps/api/fixtures/architecture/vnext_plus85/"
            "adeu_architecture_analysis_settlement_frame_v85_observation_derivative.json"
        ),
        observation_frame_id="v41c_v85_architecture_ir_observation_reference",
        repository_root=_repo_root(),
    )
    assert derived == fixture
    assert (
        canonicalize_adeu_architecture_observation_frame_payload(
            fixture,
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v41c_exported_schema_accepts_reference_fixture() -> None:
    _schema_validator().validate(_load_v85("adeu_architecture_observation_frame_v85_reference.json"))


def test_v41c_rejects_source_ref_outside_request_boundary() -> None:
    payload = deepcopy(_load_v85("adeu_architecture_observation_frame_v85_reference.json"))
    payload["observed_units"][0]["source_refs"] = ["README.md"]
    payload["observed_units"][0]["source_hashes"] = {"README.md": "0" * 64}

    with pytest.raises(ValidationError, match="must resolve inside the released V41-A"):
        AdeuArchitectureObservationFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41c_rejects_documentation_as_observed_source_ref() -> None:
    payload = deepcopy(_load_v85("adeu_architecture_observation_frame_v85_reference.json"))
    doc_ref = "docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md"
    request = _load_v85("adeu_architecture_analysis_request_v85_observation_derivative.json")
    doc_hash = next(
        item["sha256"] for item in request["source_set"]["items"] if item["path"] == doc_ref
    )
    payload["observed_units"][0]["source_refs"] = [doc_ref]
    payload["observed_units"][0]["source_hashes"] = {doc_ref: doc_hash}

    with pytest.raises(ValidationError, match="may not rely on documentation items"):
        AdeuArchitectureObservationFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41c_rejects_upstream_compile_entitlement_drift() -> None:
    payload = deepcopy(_load_v85("adeu_architecture_observation_frame_v85_reference.json"))
    payload["upstream_compile_entitlement"] = "entitled"

    with pytest.raises(ValidationError, match="upstream_compile_entitlement must match"):
        AdeuArchitectureObservationFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41c_rejects_upstream_blocking_ref_drift() -> None:
    payload = deepcopy(_load_v85("adeu_architecture_observation_frame_v85_reference.json"))
    payload["upstream_blocking_refs"] = payload["upstream_blocking_refs"][:-1]

    with pytest.raises(ValidationError, match="upstream_blocking_refs must match"):
        AdeuArchitectureObservationFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41c_rejects_missing_observation_mode() -> None:
    payload = deepcopy(_load_v85("adeu_architecture_observation_frame_v85_reference.json"))
    del payload["observed_units"][0]["observation_mode"]

    with pytest.raises(ValidationError):
        AdeuArchitectureObservationFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41c_rejects_workflow_ref_outside_typed_entries() -> None:
    payload = deepcopy(_load_v85("adeu_architecture_observation_frame_v85_reference.json"))
    payload["observed_workflows"][0]["step_refs"] = ["missing_unit"]

    with pytest.raises(ValidationError, match="step_ref 'missing_unit' must resolve"):
        AdeuArchitectureObservationFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41c_rejects_unresolved_observation_without_reason_kind() -> None:
    payload = deepcopy(_load_v85("adeu_architecture_observation_frame_v85_reference.json"))
    del payload["unresolved_observations"][0]["unresolved_reason_kind"]

    with pytest.raises(ValidationError):
        AdeuArchitectureObservationFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41c_uses_observable_kind_not_filename_substrings_for_resolution() -> None:
    request_payload = _load_v85(
        "adeu_architecture_analysis_request_v85_observation_derivative.json"
    )
    request = AdeuArchitectureAnalysisRequest.model_validate(
        request_payload,
        context={"repository_root": _repo_root()},
    )
    event_like_hook = ObservedObservabilityHook.model_validate(
        {
            "observability_hook_id": "observability_runtime_signal_join",
            "hook_kind": "events_artifact",
            "observable_kind": "events",
            "observation_mode": "direct",
            "source_refs": ["artifacts/quality_dashboard_v83_closeout.json"],
            "source_hashes": {
                "artifacts/quality_dashboard_v83_closeout.json": next(
                    item["sha256"]
                    for item in request_payload["source_set"]["items"]
                    if item["path"] == "artifacts/quality_dashboard_v83_closeout.json"
                )
            },
        }
    )

    assert _derive_unresolved_observations(
        request=request,
        observability_hooks=[event_like_hook],
    ) == []


def test_v41c_rejects_alignment_creep() -> None:
    payload = deepcopy(_load_v85("adeu_architecture_observation_frame_v85_reference.json"))
    payload["alignment_diagnostics"] = []

    with pytest.raises(ValidationError):
        AdeuArchitectureObservationFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )
