from __future__ import annotations

import json
import shutil
from copy import deepcopy
from pathlib import Path

import pytest
from adeu_architecture_compiler import (
    ADEU_ARCHITECTURE_CHECKPOINT_TRACE_SCHEMA,
    ADEU_ARCHITECTURE_IR_DELTA_SCHEMA,
    ADEU_ARCHITECTURE_ORACLE_REQUEST_SCHEMA,
    ADEU_ARCHITECTURE_ORACLE_RESOLUTION_SCHEMA,
    AdeuArchitectureCheckpointTrace,
    AdeuArchitectureIRDelta,
    AdeuArchitectureOracleRequest,
    AdeuArchitectureOracleResolution,
    canonicalize_adeu_architecture_ir_delta_payload,
    derive_v40c_checkpoint_trace,
    derive_v40c_ir_delta,
    derive_v40c_oracle_request,
    derive_v40c_oracle_resolution,
)
from adeu_architecture_compiler.conformance import derive_v40b_conformance_report
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


def _v79_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "architecture" / "vnext_plus79"


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v77(name: str) -> dict[str, object]:
    return _load_json(_v77_root() / name)


def _load_v78(name: str) -> dict[str, object]:
    return _load_json(_v78_root() / name)


def _load_v79(name: str) -> dict[str, object]:
    return _load_json(_v79_root() / name)


def _copy_fixture_tree(tmp_path: Path) -> Path:
    shutil.copytree(_repo_root() / "apps", tmp_path / "apps")
    return tmp_path


def _schema_validator(stem: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_architecture_compiler" / "schema" / f"{stem}.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _oracle_derivative_semantic() -> dict[str, object]:
    payload = deepcopy(_load_v77("adeu_architecture_semantic_ir_v77_reference.json"))
    payload["epistemics"]["ambiguities"][0]["resolution_route"] = "oracle_assisted"
    payload["deontics"]["escalation_rules"] = []
    return materialize_adeu_architecture_semantic_ir_payload(
        payload,
        repository_root=_repo_root(),
    )


def _oracle_derivative_conformance(*, repository_root: Path | None = None) -> dict[str, object]:
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
            / "vnext_plus79"
            / "adeu_architecture_semantic_ir_v79_oracle_derivative.json"
        ),
        semantic_ir_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_semantic_ir_v79_oracle_derivative.json",
        repository_root=root,
    )


def test_v40c_deterministic_pass_trace_fixture_validates_and_replays() -> None:
    fixture = _load_v79("adeu_architecture_checkpoint_trace_v79_deterministic_pass_reference.json")
    trace = AdeuArchitectureCheckpointTrace.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )
    assert trace.schema == ADEU_ARCHITECTURE_CHECKPOINT_TRACE_SCHEMA
    assert trace.checkpoint_entries[0].checkpoint_class == "deterministic_pass"
    assert (
        derive_v40c_checkpoint_trace(
            semantic_ir_payload=_load_v78(
                "adeu_architecture_semantic_ir_v78_ready_derivative.json"
            ),
            conformance_report_payload=_load_v78(
                "adeu_architecture_conformance_report_v78_ready_reference.json"
            ),
            conformance_report_path="apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_ready_reference.json",
            checkpoint_source_kind="ambiguity",
            checkpoint_subject_ref="amb_auto_approve_threshold",
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v40c_human_needed_trace_fixture_validates_and_replays() -> None:
    fixture = _load_v79("adeu_architecture_checkpoint_trace_v79_human_needed_reference.json")
    trace = AdeuArchitectureCheckpointTrace.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )
    assert trace.checkpoint_entries[0].checkpoint_class == "human_needed"
    assert trace.checkpoint_entries[0].final_adjudication == "escalated_human"
    assert (
        derive_v40c_checkpoint_trace(
            semantic_ir_payload=_load_v77("adeu_architecture_semantic_ir_v77_reference.json"),
            conformance_report_payload=_load_v78(
                "adeu_architecture_conformance_report_v78_blocked_reference.json"
            ),
            conformance_report_path="apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_blocked_reference.json",
            checkpoint_source_kind="human_escalation",
            checkpoint_subject_ref="rule_policy_gap",
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v40c_oracle_reference_fixture_set_validates_and_replays() -> None:
    request_fixture = _load_v79("adeu_architecture_oracle_request_v79_reference.json")
    resolution_fixture = _load_v79("adeu_architecture_oracle_resolution_v79_reference.json")
    delta_fixture = _load_v79("adeu_architecture_ir_delta_v79_reference.json")
    trace_fixture = _load_v79("adeu_architecture_checkpoint_trace_v79_oracle_reference.json")

    request = AdeuArchitectureOracleRequest.model_validate(
        request_fixture,
        context={"repository_root": _repo_root()},
    )
    resolution = AdeuArchitectureOracleResolution.model_validate(
        resolution_fixture,
        context={"repository_root": _repo_root()},
    )
    delta = AdeuArchitectureIRDelta.model_validate(
        delta_fixture,
        context={"repository_root": _repo_root()},
    )
    trace = AdeuArchitectureCheckpointTrace.model_validate(
        trace_fixture,
        context={"repository_root": _repo_root()},
    )

    assert request.schema == ADEU_ARCHITECTURE_ORACLE_REQUEST_SCHEMA
    assert resolution.schema == ADEU_ARCHITECTURE_ORACLE_RESOLUTION_SCHEMA
    assert delta.schema == ADEU_ARCHITECTURE_IR_DELTA_SCHEMA
    assert trace.checkpoint_entries[0].final_adjudication == "resolved_pass"

    derived_request = derive_v40c_oracle_request(
        semantic_ir_payload=_load_v79("adeu_architecture_semantic_ir_v79_oracle_derivative.json"),
        conformance_report_payload=_load_v79(
            "adeu_architecture_conformance_report_v79_oracle_blocked_derivative.json"
        ),
        conformance_report_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_conformance_report_v79_oracle_blocked_derivative.json",
        ambiguity_ref="amb_auto_approve_threshold",
        model_id="gpt-5.4",
        model_version="2026-03-24",
        reasoning_effort="high",
        prompt_template_version="v40c_oracle_request.v1",
        repository_root=_repo_root(),
    )
    provisional_resolution = derive_v40c_oracle_resolution(
        oracle_request_payload=derived_request,
        oracle_request_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_oracle_request_v79_reference.json",
        resolution_state="advisory_support",
        raw_output_text=(
            "The policy threshold can remain operator-defined so long as the approval "
            "workbench preserves explicit human authority over final commit."
        ),
        repository_root=_repo_root(),
    )
    derived_delta = derive_v40c_ir_delta(
        semantic_ir_payload=_load_v79("adeu_architecture_semantic_ir_v79_oracle_derivative.json"),
        oracle_resolution_payload=provisional_resolution,
        checkpoint_id=derived_request["checkpoint_id"],
        scope_ref="epistemics.ambiguities.amb_auto_approve_threshold",
        target_refs=["amb_auto_approve_threshold"],
        authorized_placeholder_refs=["ph_auto_approve_threshold_policy"],
        operation_set=[
            {
                "operation_id": "op_replace_question",
                "operation_kind": "replace_text",
                "target_ref": "amb_auto_approve_threshold",
                "field_path": "epistemics.ambiguities.amb_auto_approve_threshold.question",
                "value": (
                    "What policy-owned threshold definition governs advisory auto-approval "
                    "without minting new authority?"
                ),
            }
        ],
        repository_root=_repo_root(),
    )
    derived_resolution = derive_v40c_oracle_resolution(
        oracle_request_payload=derived_request,
        oracle_request_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_oracle_request_v79_reference.json",
        resolution_state="advisory_support",
        raw_output_text=(
            "The policy threshold can remain operator-defined so long as the approval "
            "workbench preserves explicit human authority over final commit."
        ),
        proposed_delta_ref=derived_delta["delta_id"],
        repository_root=_repo_root(),
    )
    derived_trace = derive_v40c_checkpoint_trace(
        semantic_ir_payload=_load_v79("adeu_architecture_semantic_ir_v79_oracle_derivative.json"),
        conformance_report_payload=_load_v79(
            "adeu_architecture_conformance_report_v79_oracle_blocked_derivative.json"
        ),
        conformance_report_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_conformance_report_v79_oracle_blocked_derivative.json",
        checkpoint_source_kind="ambiguity",
        checkpoint_subject_ref="amb_auto_approve_threshold",
        oracle_request_payload=derived_request,
        oracle_request_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_oracle_request_v79_reference.json",
        oracle_resolution_payload=derived_resolution,
        oracle_resolution_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_oracle_resolution_v79_reference.json",
        repository_root=_repo_root(),
    )

    assert derived_request == request_fixture
    assert derived_delta == delta_fixture
    assert derived_resolution == resolution_fixture
    assert derived_trace == trace_fixture


def test_v40c_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("adeu_architecture_oracle_request").validate(
        _load_v79("adeu_architecture_oracle_request_v79_reference.json")
    )
    _schema_validator("adeu_architecture_oracle_resolution").validate(
        _load_v79("adeu_architecture_oracle_resolution_v79_reference.json")
    )
    _schema_validator("adeu_architecture_ir_delta").validate(
        _load_v79("adeu_architecture_ir_delta_v79_reference.json")
    )
    _schema_validator("adeu_architecture_checkpoint_trace").validate(
        _load_v79("adeu_architecture_checkpoint_trace_v79_deterministic_pass_reference.json")
    )
    _schema_validator("adeu_architecture_checkpoint_trace").validate(
        _load_v79("adeu_architecture_checkpoint_trace_v79_human_needed_reference.json")
    )
    _schema_validator("adeu_architecture_checkpoint_trace").validate(
        _load_v79("adeu_architecture_checkpoint_trace_v79_oracle_reference.json")
    )


def test_v40c_oracle_request_rejects_non_oracle_ambiguity() -> None:
    with pytest.raises(ValueError, match="oracle-assisted ambiguity"):
        derive_v40c_oracle_request(
            semantic_ir_payload=_load_v78(
                "adeu_architecture_semantic_ir_v78_ready_derivative.json"
            ),
            conformance_report_payload=_load_v78(
                "adeu_architecture_conformance_report_v78_ready_reference.json"
            ),
            conformance_report_path="apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_ready_reference.json",
            ambiguity_ref="amb_auto_approve_threshold",
            model_id="gpt-5.4",
            model_version="2026-03-24",
            reasoning_effort="high",
            prompt_template_version="v40c_oracle_request.v1",
            repository_root=_repo_root(),
        )


def test_v40c_oracle_request_rejects_structural_deterministic_failures() -> None:
    report = deepcopy(
        _load_v79("adeu_architecture_conformance_report_v79_oracle_blocked_derivative.json")
    )
    for result in report["check_results"]:
        if result["check_id"] == "ASIR-D-001":
            result["passed"] = False
            break
    report["failed_check_ids"] = ["ASIR-D-001", "ASIR-P-001"]
    report["projection_readiness"] = "blocked"
    with pytest.raises(ValueError, match="structural deterministic failures"):
        derive_v40c_oracle_request(
            semantic_ir_payload=_load_v79(
                "adeu_architecture_semantic_ir_v79_oracle_derivative.json"
            ),
            conformance_report_payload=report,
            conformance_report_path="apps/api/fixtures/architecture/vnext_plus79/adeu_architecture_conformance_report_v79_oracle_blocked_derivative.json",
            ambiguity_ref="amb_auto_approve_threshold",
            model_id="gpt-5.4",
            model_version="2026-03-24",
            reasoning_effort="high",
            prompt_template_version="v40c_oracle_request.v1",
            repository_root=_repo_root(),
        )


def test_v40c_delta_rejects_authority_rewrite() -> None:
    payload = deepcopy(_load_v79("adeu_architecture_ir_delta_v79_reference.json"))
    payload["operation_set"][0]["field_path"] = "deontics.gates.gate_decide.authority_source_ref"
    with pytest.raises(ValidationError, match="authority or boundary provenance"):
        canonicalize_adeu_architecture_ir_delta_payload(
            payload,
            repository_root=_repo_root(),
        )


def test_v40c_invalid_replay_resolution_fixture_is_rejected() -> None:
    fixture = _load_v79("adeu_architecture_oracle_resolution_v79_invalid_replay.json")
    with pytest.raises(ValidationError, match="referenced oracle request"):
        AdeuArchitectureOracleResolution.model_validate(
            fixture,
            context={"repository_root": _repo_root()},
        )


def test_v40c_oracle_derivative_conformance_replays_in_temp_root(tmp_path: Path) -> None:
    temp_root = _copy_fixture_tree(tmp_path)
    semantic_path = (
        temp_root
        / "apps"
        / "api"
        / "fixtures"
        / "architecture"
        / "vnext_plus79"
        / "adeu_architecture_semantic_ir_v79_oracle_derivative.json"
    )
    semantic_path.parent.mkdir(parents=True, exist_ok=True)
    semantic_path.write_text(
        json.dumps(_oracle_derivative_semantic(), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    assert _oracle_derivative_conformance(repository_root=temp_root) == _load_v79(
        "adeu_architecture_conformance_report_v79_oracle_blocked_derivative.json"
    )
