from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path

import pytest
from adeu_architecture_compiler import (
    V41DIntendedCompileBundle,
    derive_v41d_boundary_graph,
    derive_v41d_intended_root_bundle,
    derive_v41d_intent_packet,
    derive_v41d_ontology_frame,
    derive_v41d_semantic_ir,
    derive_v41d_world_hypothesis,
)
from adeu_architecture_ir import (
    ArchitectureBoundaryGraph,
    ArchitectureIntentPacket,
    ArchitectureOntologyFrame,
    ArchitectureWorldHypothesis,
)
from adeu_architecture_ir.root_family import AdeuArchitectureSemanticIR
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v85_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "architecture" / "vnext_plus85"


def _v86_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "architecture" / "vnext_plus86"


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v85(name: str) -> dict[str, object]:
    return _load_json(_v85_root() / name)


def _load_v86(name: str) -> dict[str, object]:
    return _load_json(_v86_root() / name)


def _schema_validator(name: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_architecture_ir"
            / "schema"
            / name
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v41d_fixture_replays_and_emitted_roots_validate() -> None:
    request = _load_v86("adeu_architecture_analysis_request_v86_intended_derivative.json")
    settlement = _load_v86(
        "adeu_architecture_analysis_settlement_frame_v86_intended_derivative.json"
    )
    observation = _load_v86("adeu_architecture_observation_frame_v86_intended_derivative.json")

    expected_intent = _load_v86("adeu_architecture_intent_packet_v86_reference.json")
    expected_ontology = _load_v86("adeu_architecture_ontology_frame_v86_reference.json")
    expected_boundary = _load_v86("adeu_architecture_boundary_graph_v86_reference.json")
    expected_world = _load_v86("adeu_architecture_world_hypothesis_v86_reference.json")
    expected_semantic = _load_v86("adeu_architecture_semantic_ir_v86_reference.json")

    bundle = derive_v41d_intended_root_bundle(
        analysis_request_payload=request,
        analysis_request_path=(
            "apps/api/fixtures/architecture/vnext_plus86/"
            "adeu_architecture_analysis_request_v86_intended_derivative.json"
        ),
        settlement_frame_payload=settlement,
        settlement_frame_path=(
            "apps/api/fixtures/architecture/vnext_plus86/"
            "adeu_architecture_analysis_settlement_frame_v86_intended_derivative.json"
        ),
        observation_frame_payload=observation,
        observation_frame_path=(
            "apps/api/fixtures/architecture/vnext_plus86/"
            "adeu_architecture_observation_frame_v86_intended_derivative.json"
        ),
        repository_root=_repo_root(),
    )

    assert isinstance(bundle, V41DIntendedCompileBundle)
    assert bundle.analysis_request_id == request["analysis_request_id"]
    assert bundle.settlement_frame_id == settlement["settlement_frame_id"]
    assert bundle.observation_frame_id == observation["observation_frame_id"]
    assert bundle.source_set_hash == request["source_set_hash"]

    assert bundle.intent_packet_payload == expected_intent
    assert bundle.ontology_frame_payload == expected_ontology
    assert bundle.boundary_graph_payload == expected_boundary
    assert bundle.world_hypothesis_payload == expected_world
    assert bundle.semantic_ir_payload == expected_semantic

    ArchitectureIntentPacket.model_validate(
        expected_intent,
        context={"repository_root": _repo_root()},
    )
    ArchitectureOntologyFrame.model_validate(
        expected_ontology,
        context={"repository_root": _repo_root()},
    )
    ArchitectureBoundaryGraph.model_validate(
        expected_boundary,
        context={"repository_root": _repo_root(), "ontology_frame": expected_ontology},
    )
    ArchitectureWorldHypothesis.model_validate(
        expected_world,
        context={"repository_root": _repo_root()},
    )
    AdeuArchitectureSemanticIR.model_validate(
        expected_semantic,
        context={"repository_root": _repo_root()},
    )

    _schema_validator("adeu_architecture_intent_packet.v1.json").validate(expected_intent)
    _schema_validator("adeu_architecture_ontology_frame.v1.json").validate(expected_ontology)
    _schema_validator("adeu_architecture_boundary_graph.v1.json").validate(expected_boundary)
    _schema_validator("adeu_architecture_world_hypothesis.v1.json").validate(expected_world)
    _schema_validator("adeu_architecture_semantic_ir.v1.json").validate(expected_semantic)


def test_v41d_individual_helpers_match_bundle() -> None:
    request = _load_v86("adeu_architecture_analysis_request_v86_intended_derivative.json")
    settlement = _load_v86(
        "adeu_architecture_analysis_settlement_frame_v86_intended_derivative.json"
    )
    observation = _load_v86("adeu_architecture_observation_frame_v86_intended_derivative.json")
    kwargs = {
        "analysis_request_payload": request,
        "analysis_request_path": (
            "apps/api/fixtures/architecture/vnext_plus86/"
            "adeu_architecture_analysis_request_v86_intended_derivative.json"
        ),
        "settlement_frame_payload": settlement,
        "settlement_frame_path": (
            "apps/api/fixtures/architecture/vnext_plus86/"
            "adeu_architecture_analysis_settlement_frame_v86_intended_derivative.json"
        ),
        "observation_frame_payload": observation,
        "observation_frame_path": (
            "apps/api/fixtures/architecture/vnext_plus86/"
            "adeu_architecture_observation_frame_v86_intended_derivative.json"
        ),
        "repository_root": _repo_root(),
    }
    bundle = derive_v41d_intended_root_bundle(**kwargs)

    assert derive_v41d_intent_packet(**kwargs) == bundle.intent_packet_payload
    assert derive_v41d_ontology_frame(**kwargs) == bundle.ontology_frame_payload
    assert derive_v41d_boundary_graph(**kwargs) == bundle.boundary_graph_payload
    assert derive_v41d_world_hypothesis(**kwargs) == bundle.world_hypothesis_payload
    assert derive_v41d_semantic_ir(**kwargs) == bundle.semantic_ir_payload


def test_v41d_carries_unresolved_observation_into_emitted_posture() -> None:
    request = _load_v86("adeu_architecture_analysis_request_v86_intended_derivative.json")
    settlement = _load_v86(
        "adeu_architecture_analysis_settlement_frame_v86_intended_derivative.json"
    )
    observation = _load_v86("adeu_architecture_observation_frame_v86_intended_derivative.json")

    semantic_ir = derive_v41d_semantic_ir(
        analysis_request_payload=request,
        analysis_request_path=(
            "apps/api/fixtures/architecture/vnext_plus86/"
            "adeu_architecture_analysis_request_v86_intended_derivative.json"
        ),
        settlement_frame_payload=settlement,
        settlement_frame_path=(
            "apps/api/fixtures/architecture/vnext_plus86/"
            "adeu_architecture_analysis_settlement_frame_v86_intended_derivative.json"
        ),
        observation_frame_payload=observation,
        observation_frame_path=(
            "apps/api/fixtures/architecture/vnext_plus86/"
            "adeu_architecture_observation_frame_v86_intended_derivative.json"
        ),
        repository_root=_repo_root(),
    )

    ambiguity_ids = {item["ambiguity_id"] for item in semantic_ir["epistemics"]["ambiguities"]}
    assert "amb_unresolved_runtime_signal_join" in ambiguity_ids
    assert any(
        "unresolved_runtime_signal_join" in item["question"]
        for item in semantic_ir["epistemics"]["ambiguities"]
    )
    first_fact_sources = semantic_ir["epistemics"]["facts"][0]["source_refs"]
    assert all(not source.startswith("src_artifacts_") for source in first_fact_sources)


def test_v41d_rejects_blocked_settlement_emission() -> None:
    request = _load_v85("adeu_architecture_analysis_request_v85_observation_derivative.json")
    settlement = _load_v85(
        "adeu_architecture_analysis_settlement_frame_v85_observation_derivative.json"
    )
    observation = _load_v85("adeu_architecture_observation_frame_v85_reference.json")

    with pytest.raises(ValueError, match="compile_entitlement=entitled"):
        derive_v41d_intended_root_bundle(
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
            observation_frame_payload=observation,
            observation_frame_path=(
                "apps/api/fixtures/architecture/vnext_plus85/"
                "adeu_architecture_observation_frame_v85_reference.json"
            ),
            repository_root=_repo_root(),
        )


def test_v41d_rejects_locally_recomputed_entitlement_drift() -> None:
    request = _load_v86("adeu_architecture_analysis_request_v86_intended_derivative.json")
    settlement = _load_v86(
        "adeu_architecture_analysis_settlement_frame_v86_intended_derivative.json"
    )
    observation = deepcopy(
        _load_v86("adeu_architecture_observation_frame_v86_intended_derivative.json")
    )
    observation["upstream_compile_entitlement"] = "blocked"
    observation["upstream_blocking_refs"] = ["blocking_shadow_recompute"]

    with pytest.raises(ValidationError, match="upstream_compile_entitlement must match"):
        derive_v41d_intended_root_bundle(
            analysis_request_payload=request,
            analysis_request_path=(
                "apps/api/fixtures/architecture/vnext_plus86/"
                "adeu_architecture_analysis_request_v86_intended_derivative.json"
            ),
            settlement_frame_payload=settlement,
            settlement_frame_path=(
                "apps/api/fixtures/architecture/vnext_plus86/"
                "adeu_architecture_analysis_settlement_frame_v86_intended_derivative.json"
            ),
            observation_frame_payload=observation,
            observation_frame_path=(
                "apps/api/fixtures/architecture/vnext_plus86/"
                "adeu_architecture_observation_frame_v86_intended_derivative.json"
            ),
            repository_root=_repo_root(),
        )


def test_v41d_rejects_missing_request_bound_accepted_doc() -> None:
    request = deepcopy(_load_v86("adeu_architecture_analysis_request_v86_intended_derivative.json"))
    settlement = _load_v86(
        "adeu_architecture_analysis_settlement_frame_v86_intended_derivative.json"
    )
    observation = _load_v86("adeu_architecture_observation_frame_v86_intended_derivative.json")
    request["accepted_doc_refs"] = []

    with pytest.raises(ValueError, match="accepted_doc_ref"):
        derive_v41d_intended_root_bundle(
            analysis_request_payload=request,
            analysis_request_path=(
                "apps/api/fixtures/architecture/vnext_plus86/"
                "adeu_architecture_analysis_request_v86_intended_derivative.json"
            ),
            settlement_frame_payload=settlement,
            settlement_frame_path=(
                "apps/api/fixtures/architecture/vnext_plus86/"
                "adeu_architecture_analysis_settlement_frame_v86_intended_derivative.json"
            ),
            observation_frame_payload=observation,
            observation_frame_path=(
                "apps/api/fixtures/architecture/vnext_plus86/"
                "adeu_architecture_observation_frame_v86_intended_derivative.json"
            ),
            repository_root=_repo_root(),
        )
