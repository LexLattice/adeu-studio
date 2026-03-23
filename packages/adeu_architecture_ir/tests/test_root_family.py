from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path

import pytest
from adeu_architecture_ir import (
    ADEU_ARCHITECTURE_BOUNDARY_GRAPH_SCHEMA,
    ADEU_ARCHITECTURE_INTENT_PACKET_SCHEMA,
    ADEU_ARCHITECTURE_ONTOLOGY_FRAME_SCHEMA,
    ADEU_ARCHITECTURE_SEMANTIC_IR_SCHEMA,
    ADEU_ARCHITECTURE_WORLD_HYPOTHESIS_SCHEMA,
    AdeuArchitectureSemanticIR,
    ArchitectureBoundaryGraph,
    ArchitectureIntentPacket,
    ArchitectureOntologyFrame,
    ArchitectureWorldHypothesis,
    canonicalize_adeu_architecture_boundary_graph_payload,
    canonicalize_adeu_architecture_intent_packet_payload,
    canonicalize_adeu_architecture_ontology_frame_payload,
    canonicalize_adeu_architecture_semantic_ir_payload,
    canonicalize_adeu_architecture_world_hypothesis_payload,
    compute_adeu_architecture_semantic_ir_hash,
)
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixtures_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "architecture" / "vnext_plus77"


def _load_json(name: str) -> dict[str, object]:
    return json.loads((_fixtures_root() / name).read_text(encoding="utf-8"))


def _load_exported_schema(name: str) -> Draft202012Validator:
    schema = json.loads(
        (_repo_root() / "packages" / "adeu_architecture_ir" / "schema" / name).read_text(
            encoding="utf-8"
        )
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v40a_intent_packet_fixture_validates_and_replays() -> None:
    fixture = _load_json("adeu_architecture_intent_packet_v77_reference.json")
    packet = ArchitectureIntentPacket.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert packet.schema == ADEU_ARCHITECTURE_INTENT_PACKET_SCHEMA
    assert all(
        source.path.startswith("apps/api/fixtures/architecture/vnext_plus77/")
        for source in packet.source_set.sources
    )
    assert (
        canonicalize_adeu_architecture_intent_packet_payload(
            fixture,
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v40a_ontology_frame_fixture_validates_and_replays() -> None:
    fixture = _load_json("adeu_architecture_ontology_frame_v77_reference.json")
    frame = ArchitectureOntologyFrame.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert frame.schema == ADEU_ARCHITECTURE_ONTOLOGY_FRAME_SCHEMA
    assert frame.authority_boundary_policy.no_direct_brief_to_codegen is True
    assert (
        canonicalize_adeu_architecture_ontology_frame_payload(
            fixture,
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v40a_boundary_graph_fixture_validates_and_replays() -> None:
    frame_fixture = _load_json("adeu_architecture_ontology_frame_v77_reference.json")
    fixture = _load_json("adeu_architecture_boundary_graph_v77_reference.json")
    graph = ArchitectureBoundaryGraph.model_validate(
        fixture,
        context={
            "repository_root": _repo_root(),
            "ontology_frame": frame_fixture,
        },
    )

    assert graph.schema == ADEU_ARCHITECTURE_BOUNDARY_GRAPH_SCHEMA
    assert set(graph.authority_crossings) <= {edge.edge_id for edge in graph.edge_set}
    assert (
        canonicalize_adeu_architecture_boundary_graph_payload(
            fixture,
            repository_root=_repo_root(),
            ontology_frame=frame_fixture,
        )
        == fixture
    )


def test_v40a_world_hypothesis_fixture_validates_and_replays() -> None:
    fixture = _load_json("adeu_architecture_world_hypothesis_v77_reference.json")
    hypothesis = ArchitectureWorldHypothesis.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert hypothesis.schema == ADEU_ARCHITECTURE_WORLD_HYPOTHESIS_SCHEMA
    assert hypothesis.authoritative is False
    assert (
        canonicalize_adeu_architecture_world_hypothesis_payload(
            fixture,
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v40a_semantic_ir_fixture_validates_and_replays() -> None:
    fixture = _load_json("adeu_architecture_semantic_ir_v77_reference.json")
    semantic_ir = AdeuArchitectureSemanticIR.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert semantic_ir.schema == ADEU_ARCHITECTURE_SEMANTIC_IR_SCHEMA
    assert semantic_ir.compiler.scope == "root_family_only"
    assert semantic_ir.semantic_hash == compute_adeu_architecture_semantic_ir_hash(fixture)
    assert (
        canonicalize_adeu_architecture_semantic_ir_payload(
            fixture,
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v40a_exported_schemas_accept_reference_fixtures() -> None:
    validators = {
        "adeu_architecture_intent_packet_v77_reference.json": _load_exported_schema(
            "adeu_architecture_intent_packet.v1.json"
        ),
        "adeu_architecture_ontology_frame_v77_reference.json": _load_exported_schema(
            "adeu_architecture_ontology_frame.v1.json"
        ),
        "adeu_architecture_boundary_graph_v77_reference.json": _load_exported_schema(
            "adeu_architecture_boundary_graph.v1.json"
        ),
        "adeu_architecture_world_hypothesis_v77_reference.json": _load_exported_schema(
            "adeu_architecture_world_hypothesis.v1.json"
        ),
        "adeu_architecture_semantic_ir_v77_reference.json": _load_exported_schema(
            "adeu_architecture_semantic_ir.v1.json"
        ),
    }
    for fixture_name, validator in validators.items():
        validator.validate(_load_json(fixture_name))


def test_v40a_world_hypothesis_rejects_authoritative_claim() -> None:
    payload = deepcopy(_load_json("adeu_architecture_world_hypothesis_v77_reference.json"))
    payload["authoritative"] = True

    with pytest.raises(ValidationError):
        ArchitectureWorldHypothesis.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v40a_boundary_graph_rejects_unknown_node_ref() -> None:
    frame_fixture = _load_json("adeu_architecture_ontology_frame_v77_reference.json")
    payload = deepcopy(_load_json("adeu_architecture_boundary_graph_v77_reference.json"))
    payload["node_refs"].append("nonexistent_ref")

    with pytest.raises(ValidationError, match="node_refs must resolve"):
        ArchitectureBoundaryGraph.model_validate(
            payload,
            context={
                "repository_root": _repo_root(),
                "ontology_frame": frame_fixture,
            },
        )


def test_v40a_semantic_ir_rejects_deferred_state_fields() -> None:
    payload = deepcopy(_load_json("adeu_architecture_semantic_ir_v77_reference.json"))
    payload["projection_readiness"] = "blocked"

    with pytest.raises(ValidationError):
        AdeuArchitectureSemanticIR.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v40a_semantic_ir_rejects_non_root_compiler_scope() -> None:
    payload = deepcopy(_load_json("adeu_architecture_semantic_ir_v77_reference.json"))
    payload["compiler"]["scope"] = "whole_asir_compile"

    with pytest.raises(ValidationError):
        AdeuArchitectureSemanticIR.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v40a_semantic_ir_rejects_missing_ambiguity_fields() -> None:
    payload = deepcopy(_load_json("adeu_architecture_semantic_ir_v77_reference.json"))
    del payload["epistemics"]["ambiguities"][0]["resolution_route"]

    with pytest.raises(ValidationError):
        AdeuArchitectureSemanticIR.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v40a_semantic_ir_rejects_unknown_touch_ref() -> None:
    payload = deepcopy(_load_json("adeu_architecture_semantic_ir_v77_reference.json"))
    payload["epistemics"]["ambiguities"][0]["touches_refs"].append("unknown_ref")

    with pytest.raises(ValidationError, match="touches_refs must resolve"):
        AdeuArchitectureSemanticIR.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v40a_semantic_ir_rejects_duplicate_actor_ids() -> None:
    payload = deepcopy(_load_json("adeu_architecture_semantic_ir_v77_reference.json"))
    duplicate = deepcopy(payload["ontology"]["actors"][0])
    payload["ontology"]["actors"].append(duplicate)

    with pytest.raises(ValidationError, match="duplicate id"):
        AdeuArchitectureSemanticIR.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )
