from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path

import pytest
from adeu_architecture_ir import (
    ADEU_ARCHITECTURE_ANALYSIS_SETTLEMENT_FRAME_SCHEMA,
    AdeuArchitectureAnalysisRequest,
    AdeuArchitectureAnalysisSettlementFrame,
    canonicalize_adeu_architecture_analysis_settlement_frame_payload,
    materialize_adeu_architecture_analysis_settlement_frame_payload,
)
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import ValidationError

_FIXTURE_NAME = "adeu_architecture_analysis_settlement_frame_v84_reference.json"


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "architecture" / "vnext_plus84"


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_fixture(name: str) -> dict[str, object]:
    return _load_json(_fixture_root() / name)


def _load_request_fixture() -> dict[str, object]:
    return _load_json(
        _repo_root()
        / "apps"
        / "api"
        / "fixtures"
        / "architecture"
        / "vnext_plus83"
        / "adeu_architecture_analysis_request_v83_reference.json"
    )


def _load_exported_schema(name: str) -> Draft202012Validator:
    schema = json.loads(
        (_repo_root() / "packages" / "adeu_architecture_ir" / "schema" / name).read_text(
            encoding="utf-8"
        )
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v41b_settlement_fixture_validates_and_replays() -> None:
    fixture = _load_fixture(_FIXTURE_NAME)
    settlement = AdeuArchitectureAnalysisSettlementFrame.model_validate(
        fixture,
        context={"repository_root": _repo_root()},
    )

    assert settlement.schema == ADEU_ARCHITECTURE_ANALYSIS_SETTLEMENT_FRAME_SCHEMA
    assert settlement.compile_entitlement == "blocked"
    assert (
        canonicalize_adeu_architecture_analysis_settlement_frame_payload(
            fixture,
            repository_root=_repo_root(),
        )
        == fixture
    )


def test_v41b_materialize_reference_fixture_replays() -> None:
    request = AdeuArchitectureAnalysisRequest.model_validate(
        _load_request_fixture(),
        context={"repository_root": _repo_root()},
    )
    fixture = _load_fixture("adeu_architecture_analysis_settlement_frame_v84_reference.json")
    payload = deepcopy(fixture)
    for field in (
        "analysis_request_id",
        "analysis_request_ref",
        "source_set_hash",
        "authority_boundary_policy",
    ):
        payload.pop(field)

    materialized = materialize_adeu_architecture_analysis_settlement_frame_payload(
        payload,
        analysis_request_payload=request,
        analysis_request_ref=(
            "apps/api/fixtures/architecture/vnext_plus83/"
            "adeu_architecture_analysis_request_v83_reference.json"
        ),
        repository_root=_repo_root(),
    )

    assert materialized == fixture


def test_v41b_exported_schema_accepts_reference_fixture() -> None:
    validator = _load_exported_schema("adeu_architecture_analysis_settlement_frame.v1.json")
    validator.validate(_load_fixture(_FIXTURE_NAME))


def test_v41b_rejects_request_lineage_drift() -> None:
    payload = deepcopy(_load_fixture(_FIXTURE_NAME))
    payload["source_set_hash"] = "0" * 64

    with pytest.raises(
        ValidationError,
        match="source_set_hash must match released V41-A request boundary",
    ):
        AdeuArchitectureAnalysisSettlementFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41b_rejects_missing_chosen_interpretation() -> None:
    payload = deepcopy(_load_fixture(_FIXTURE_NAME))
    payload["chosen_interpretation_id"] = "missing_interpretation"

    with pytest.raises(
        ValidationError,
        match="chosen_interpretation_id must resolve inside interpretation_register",
    ):
        AdeuArchitectureAnalysisSettlementFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41b_rejects_unsupported_deontic_class() -> None:
    payload = deepcopy(_load_fixture(_FIXTURE_NAME))
    payload["deontic_typing_register"][0]["deontic_class"] = "mandatory"

    with pytest.raises(ValidationError):
        AdeuArchitectureAnalysisSettlementFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41b_rejects_unsupported_affordance_decision_class() -> None:
    payload = deepcopy(_load_fixture(_FIXTURE_NAME))
    payload["affordance_decisions"][0]["decision_class"] = "ignored"

    with pytest.raises(ValidationError):
        AdeuArchitectureAnalysisSettlementFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41b_rejects_unsupported_claim_posture_class() -> None:
    payload = deepcopy(_load_fixture(_FIXTURE_NAME))
    payload["claim_posture_register"][0]["posture_class"] = "proved_unsat"

    with pytest.raises(ValidationError):
        AdeuArchitectureAnalysisSettlementFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41b_rejects_missing_rationale_for_declined_affordance() -> None:
    payload = deepcopy(_load_fixture(_FIXTURE_NAME))
    payload["affordance_decisions"][0]["rationale"] = " "

    with pytest.raises(ValidationError, match="rationale must not be empty"):
        AdeuArchitectureAnalysisSettlementFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41b_rejects_missing_affordance_coverage() -> None:
    payload = deepcopy(_load_fixture(_FIXTURE_NAME))
    payload["affordance_decisions"] = payload["affordance_decisions"][:1]

    with pytest.raises(ValidationError, match="affordance_decisions"):
        AdeuArchitectureAnalysisSettlementFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41b_rejects_ref_outside_request_boundary() -> None:
    payload = deepcopy(_load_fixture(_FIXTURE_NAME))
    payload["claim_posture_register"][0]["claim_ref"] = "README.md"

    with pytest.raises(ValidationError, match="must resolve to the released V41-A request"):
        AdeuArchitectureAnalysisSettlementFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41b_rejects_entitled_frame_with_blockers() -> None:
    payload = deepcopy(_load_fixture(_FIXTURE_NAME))
    payload["compile_entitlement"] = "entitled"

    with pytest.raises(ValidationError, match="compile_entitlement=entitled"):
        AdeuArchitectureAnalysisSettlementFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41b_rejects_blocked_frame_without_blocking_lineage() -> None:
    payload = deepcopy(_load_fixture(_FIXTURE_NAME))
    payload["blocking_lineage"] = []

    with pytest.raises(
        ValidationError,
        match="compile_entitlement=blocked requires blocking_lineage",
    ):
        AdeuArchitectureAnalysisSettlementFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41b_rejects_unentitled_negative_claim_without_support_limit_class() -> None:
    payload = deepcopy(_load_fixture(_FIXTURE_NAME))
    payload["claim_posture_register"][1]["support_limit_class"] = None

    with pytest.raises(ValidationError, match="require support_limit_class"):
        AdeuArchitectureAnalysisSettlementFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41b_rejects_prose_only_semantic_additions() -> None:
    payload = deepcopy(_load_fixture(_FIXTURE_NAME))
    payload["advisory_notes"] = ["deontic_class: required for missing surface"]

    with pytest.raises(ValidationError, match="advisory_notes may not introduce"):
        AdeuArchitectureAnalysisSettlementFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )


def test_v41b_rejects_alignment_payload_creep() -> None:
    payload = deepcopy(_load_fixture(_FIXTURE_NAME))
    payload["alignment_diagnostics"] = []

    with pytest.raises(ValidationError):
        AdeuArchitectureAnalysisSettlementFrame.model_validate(
            payload,
            context={"repository_root": _repo_root()},
        )
