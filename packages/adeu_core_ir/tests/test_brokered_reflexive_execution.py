from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest
from adeu_core_ir.brokered_reflexive_execution import (
    ADEU_BROKERED_REFLEXIVE_EXECUTION_PLAN_SCHEMA,
    ADEU_BROKERED_REFLEXIVE_PAYLOAD_SCHEMA,
    AdeuBrokeredReflexivePayload,
    canonicalize_brokered_reflexive_execution_plan_payload,
    canonicalize_brokered_reflexive_payload_payload,
    compile_brokered_reflexive_execution_plan,
)


def _fixtures_root() -> Path:
    root = Path(__file__).resolve().parents[3]
    return (
        root / "apps" / "api" / "fixtures" / "brokered_reflexive_execution" / "vnext_plus71"
    )


def _source_doc_path() -> Path:
    return Path(__file__).resolve().parents[3] / "docs" / "DRAFT_MASTER_EXECUTABLE_PAYLOAD_v0.md"


def _source_doc_sha256() -> str:
    return hashlib.sha256(_source_doc_path().read_bytes()).hexdigest()


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _payload() -> dict[str, object]:
    return _load_json(_fixtures_root() / "adeu_brokered_reflexive_payload.json")


def test_brokered_reflexive_payload_model_validates_reference_payload() -> None:
    normalized = AdeuBrokeredReflexivePayload.model_validate(_payload())

    assert normalized.schema == ADEU_BROKERED_REFLEXIVE_PAYLOAD_SCHEMA
    assert normalized.domain_class == "soft_reflexive"
    assert normalized.source_doc_ref == "docs/DRAFT_MASTER_EXECUTABLE_PAYLOAD_v0.md"
    assert normalized.source_doc_sha256 == _source_doc_sha256()
    assert normalized.requested_roles[0] == "orchestrator"


def test_compile_brokered_reflexive_execution_plan_is_deterministic() -> None:
    first = compile_brokered_reflexive_execution_plan(_payload())
    second = compile_brokered_reflexive_execution_plan(_payload())

    first_payload = first.model_dump(mode="json", by_alias=True)
    second_payload = second.model_dump(mode="json", by_alias=True)

    assert first_payload == second_payload
    assert first.schema == ADEU_BROKERED_REFLEXIVE_EXECUTION_PLAN_SCHEMA
    assert first.inspection_order == ["utility", "deontics", "ontology", "epistemics"]
    assert first.source_doc_ref == "docs/DRAFT_MASTER_EXECUTABLE_PAYLOAD_v0.md"
    assert first.source_doc_sha256 == _source_doc_sha256()
    assert first.max_delegation_depth == 3
    assert first.primary_execution_surface == "adeu.compile_brokered_reflexive_execution"
    assert first.supporting_api_route == "/urm/reflex/compile"
    assert first.summary.total_sessions == 6
    assert first.summary.total_layers == 8
    assert first.summary.counts_by_role["gatekeeper"] == 1
    assert first.summary.counts_by_stage["recursive_honesty_audit"] == 1
    assert first.sessions[0].delegation_depth_limit == 3
    assert first.sessions[1].role == "explorer"
    assert first.sessions[1].delegation_depth_limit == 2
    assert first.sessions[1].prompt_packet.recommended_agent_model == "gpt-5.4-mini"
    assert first.sessions[2].role == "adversarial_reviewer"
    assert first.sessions[2].prompt_packet.recommended_agent_model == "gpt-5.4"
    assert first.sessions[3].role == "implementer"
    assert first.sessions[3].prompt_packet.recommended_agent_model == "gpt-5.3-codex"
    assert first.sentinel_profile.permitted_intervention_depth == "constraint_suggestion"
    assert len(first.sentinel_profile.utility_capture_risk_rules) == 4


def test_canonicalize_payload_and_plan_normalize_valid_payloads() -> None:
    canonical_payload = canonicalize_brokered_reflexive_payload_payload(_payload())
    plan = compile_brokered_reflexive_execution_plan(canonical_payload)
    canonical_plan = canonicalize_brokered_reflexive_execution_plan_payload(
        plan.model_dump(mode="json", by_alias=True)
    )

    assert canonical_payload["schema"] == ADEU_BROKERED_REFLEXIVE_PAYLOAD_SCHEMA
    assert canonical_plan["schema"] == ADEU_BROKERED_REFLEXIVE_EXECUTION_PLAN_SCHEMA
    assert canonical_plan["summary"]["counts_by_stage"]["implementation"] == 1


def test_reference_fixtures_validate_and_bind_to_compiled_plan() -> None:
    fixture_root = _fixtures_root()
    canonical_payload = canonicalize_brokered_reflexive_payload_payload(
        _load_json(fixture_root / "adeu_brokered_reflexive_payload.json")
    )
    expected_plan = canonicalize_brokered_reflexive_execution_plan_payload(
        _load_json(fixture_root / "adeu_brokered_reflexive_execution_plan.json")
    )
    compiled_plan = canonicalize_brokered_reflexive_execution_plan_payload(
        compile_brokered_reflexive_execution_plan(canonical_payload).model_dump(
            mode="json",
            by_alias=True,
        )
    )

    assert canonical_payload["schema"] == ADEU_BROKERED_REFLEXIVE_PAYLOAD_SCHEMA
    assert expected_plan["schema"] == ADEU_BROKERED_REFLEXIVE_EXECUTION_PLAN_SCHEMA
    assert compiled_plan == expected_plan


def test_payload_rejects_non_advisory_posture() -> None:
    payload = _payload()
    payload["advisory_only"] = False

    with pytest.raises(ValueError, match="advisory_only must remain true"):
        AdeuBrokeredReflexivePayload.model_validate(payload)


def test_payload_rejects_routing_order_drift() -> None:
    payload = _payload()
    payload["adaptive_domain_routing"]["soft_reflexive_order"] = [  # type: ignore[index]
        "ontology",
        "epistemics",
        "deontics",
        "utility",
    ]

    with pytest.raises(
        ValueError,
        match="soft_reflexive_order must match the frozen routing order",
    ):
        AdeuBrokeredReflexivePayload.model_validate(payload)


def test_payload_rejects_requested_roles_without_orchestrator_head() -> None:
    payload = _payload()
    payload["requested_roles"] = [
        "explorer",
        "orchestrator",
        "adversarial_reviewer",
    ]

    with pytest.raises(
        ValueError,
        match="requested_roles must start with orchestrator",
    ):
        AdeuBrokeredReflexivePayload.model_validate(payload)
