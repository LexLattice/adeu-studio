from __future__ import annotations

import json
import shutil
from copy import deepcopy
from pathlib import Path

import pytest
from adeu_architecture_compiler import (
    ADEU_ARCHITECTURE_CONFORMANCE_REPORT_SCHEMA,
    AdeuArchitectureConformanceReport,
    canonicalize_adeu_architecture_conformance_report_payload,
    derive_v40b_conformance_report,
)
from adeu_architecture_ir import materialize_adeu_architecture_semantic_ir_payload
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v77_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "architecture" / "vnext_plus77"


def _v78_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "architecture" / "vnext_plus78"


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v77(name: str) -> dict[str, object]:
    return _load_json(_v77_root() / name)


def _load_v78(name: str) -> dict[str, object]:
    return _load_json(_v78_root() / name)


def _report_schema() -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_architecture_compiler"
            / "schema"
            / "adeu_architecture_conformance_report.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _derive_blocked_report(*, repository_root: Path | None = None) -> dict[str, object]:
    root = repository_root or _repo_root()
    return derive_v40b_conformance_report(
        intent_packet_payload=_load_json(
            root
            / "apps"
            / "api"
            / "fixtures"
            / "architecture"
            / "vnext_plus77"
            / "adeu_architecture_intent_packet_v77_reference.json"
        ),
        intent_packet_path="apps/api/fixtures/architecture/vnext_plus77/adeu_architecture_intent_packet_v77_reference.json",
        ontology_frame_payload=_load_json(
            root
            / "apps"
            / "api"
            / "fixtures"
            / "architecture"
            / "vnext_plus77"
            / "adeu_architecture_ontology_frame_v77_reference.json"
        ),
        ontology_frame_path="apps/api/fixtures/architecture/vnext_plus77/adeu_architecture_ontology_frame_v77_reference.json",
        boundary_graph_payload=_load_json(
            root
            / "apps"
            / "api"
            / "fixtures"
            / "architecture"
            / "vnext_plus77"
            / "adeu_architecture_boundary_graph_v77_reference.json"
        ),
        boundary_graph_path="apps/api/fixtures/architecture/vnext_plus77/adeu_architecture_boundary_graph_v77_reference.json",
        world_hypothesis_payload=_load_json(
            root
            / "apps"
            / "api"
            / "fixtures"
            / "architecture"
            / "vnext_plus77"
            / "adeu_architecture_world_hypothesis_v77_reference.json"
        ),
        world_hypothesis_path="apps/api/fixtures/architecture/vnext_plus77/adeu_architecture_world_hypothesis_v77_reference.json",
        semantic_ir_payload=_load_json(
            root
            / "apps"
            / "api"
            / "fixtures"
            / "architecture"
            / "vnext_plus77"
            / "adeu_architecture_semantic_ir_v77_reference.json"
        ),
        semantic_ir_path="apps/api/fixtures/architecture/vnext_plus77/adeu_architecture_semantic_ir_v77_reference.json",
        repository_root=root,
    )


def _derive_ready_report(*, repository_root: Path | None = None) -> dict[str, object]:
    root = repository_root or _repo_root()
    return derive_v40b_conformance_report(
        intent_packet_payload=_load_json(
            root
            / "apps"
            / "api"
            / "fixtures"
            / "architecture"
            / "vnext_plus77"
            / "adeu_architecture_intent_packet_v77_reference.json"
        ),
        intent_packet_path="apps/api/fixtures/architecture/vnext_plus77/adeu_architecture_intent_packet_v77_reference.json",
        ontology_frame_payload=_load_json(
            root
            / "apps"
            / "api"
            / "fixtures"
            / "architecture"
            / "vnext_plus77"
            / "adeu_architecture_ontology_frame_v77_reference.json"
        ),
        ontology_frame_path="apps/api/fixtures/architecture/vnext_plus77/adeu_architecture_ontology_frame_v77_reference.json",
        boundary_graph_payload=_load_json(
            root
            / "apps"
            / "api"
            / "fixtures"
            / "architecture"
            / "vnext_plus77"
            / "adeu_architecture_boundary_graph_v77_reference.json"
        ),
        boundary_graph_path="apps/api/fixtures/architecture/vnext_plus77/adeu_architecture_boundary_graph_v77_reference.json",
        world_hypothesis_payload=_load_json(
            root
            / "apps"
            / "api"
            / "fixtures"
            / "architecture"
            / "vnext_plus77"
            / "adeu_architecture_world_hypothesis_v77_reference.json"
        ),
        world_hypothesis_path="apps/api/fixtures/architecture/vnext_plus77/adeu_architecture_world_hypothesis_v77_reference.json",
        semantic_ir_payload=_load_json(
            root
            / "apps"
            / "api"
            / "fixtures"
            / "architecture"
            / "vnext_plus78"
            / "adeu_architecture_semantic_ir_v78_ready_derivative.json"
        ),
        semantic_ir_path="apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_semantic_ir_v78_ready_derivative.json",
        repository_root=root,
    )


def _copy_fixture_tree(tmp_path: Path) -> Path:
    repo_root = _repo_root()
    shutil.copytree(repo_root / "apps", tmp_path / "apps")
    return tmp_path


def test_v40b_blocked_reference_fixture_validates_and_replays() -> None:
    fixture = _load_v78("adeu_architecture_conformance_report_v78_blocked_reference.json")
    report = AdeuArchitectureConformanceReport.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )
    assert report.schema == ADEU_ARCHITECTURE_CONFORMANCE_REPORT_SCHEMA
    assert report.projection_readiness == "blocked"
    assert report.failed_check_ids == ["ASIR-P-001", "ASIR-P-002"]
    assert _derive_blocked_report() == fixture
    assert (
        canonicalize_adeu_architecture_conformance_report_payload(
            fixture,
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v40b_ready_reference_fixture_validates_and_replays() -> None:
    fixture = _load_v78("adeu_architecture_conformance_report_v78_ready_reference.json")
    report = AdeuArchitectureConformanceReport.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )
    assert report.projection_readiness == "ready"
    assert report.failed_check_ids == []
    assert _derive_ready_report() == fixture


def test_v40b_exported_schema_accepts_reference_fixtures() -> None:
    validator = _report_schema()
    validator.validate(_load_v78("adeu_architecture_conformance_report_v78_blocked_reference.json"))
    validator.validate(_load_v78("adeu_architecture_conformance_report_v78_ready_reference.json"))


def test_v40b_compiler_blocks_when_gate_coverage_is_missing(tmp_path: Path) -> None:
    temp_root = _copy_fixture_tree(tmp_path)
    semantic_path = (
        temp_root
        / "apps"
        / "api"
        / "fixtures"
        / "architecture"
        / "vnext_plus77"
        / "adeu_architecture_semantic_ir_v77_reference.json"
    )
    payload = _load_json(semantic_path)
    payload["deontics"]["gates"][0]["required_refs"] = ["fact_policy_required"]
    semantic_path.write_text(
        json.dumps(
            materialize_adeu_architecture_semantic_ir_payload(payload, repository_root=temp_root),
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )

    report = _derive_blocked_report(repository_root=temp_root)
    assert report["projection_readiness"] == "blocked"
    assert "ASIR-D-002" in report["failed_check_ids"]


def test_v40b_compiler_rejects_nonempty_emitted_artifact_refs() -> None:
    payload = deepcopy(_load_v78("adeu_architecture_conformance_report_v78_ready_reference.json"))
    payload["emitted_artifact_refs"] = ["spec/adeu_core_ir.schema.json"]

    with pytest.raises(ValidationError, match="emitted_artifact_refs must remain empty"):
        AdeuArchitectureConformanceReport.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v40b_advisory_check_failure_does_not_block_ready_state(tmp_path: Path) -> None:
    temp_root = _copy_fixture_tree(tmp_path)
    ready_semantic_path = (
        temp_root
        / "apps"
        / "api"
        / "fixtures"
        / "architecture"
        / "vnext_plus78"
        / "adeu_architecture_semantic_ir_v78_ready_derivative.json"
    )
    payload = _load_json(ready_semantic_path)
    payload["utility"]["priority_rules"] = []
    payload["utility"]["tradeoffs"] = []
    ready_semantic_path.write_text(
        json.dumps(
            materialize_adeu_architecture_semantic_ir_payload(payload, repository_root=temp_root),
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )

    report = _derive_ready_report(repository_root=temp_root)
    check_results = {entry["check_id"]: entry for entry in report["check_results"]}
    assert report["projection_readiness"] == "ready"
    assert report["failed_check_ids"] == []
    assert check_results["ASIR-U-002"]["passed"] is False
    assert check_results["ASIR-U-002"]["required"] is False
