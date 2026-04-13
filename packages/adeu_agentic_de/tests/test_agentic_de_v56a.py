from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_agentic_de import (
    DEFAULT_ACTION_PROPOSAL_PATH,
    DEFAULT_DOMAIN_PACKET_PATH,
    DEFAULT_INTERACTION_CONTRACT_PATH,
    DEFAULT_MORPH_IR_PATH,
    AgenticDeActionProposal,
    AgenticDeConformanceReport,
    AgenticDeDomainPacket,
    AgenticDeInteractionContract,
    AgenticDeMembraneCheckpoint,
    AgenticDeMorphDiagnosticFinding,
    AgenticDeMorphDiagnostics,
    AgenticDeMorphIr,
    load_domain_packet,
    load_interaction_contract,
    load_morph_ir,
    run_agentic_de_interaction_v56a,
)

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v56a"


def _fixture_payload(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_fixture(name: str) -> dict[str, object]:
    return _fixture_payload(FIXTURE_ROOT / name)


def test_reference_v56a_run_is_accepted_dry_run_only() -> None:
    checkpoint, diagnostics, conformance = run_agentic_de_interaction_v56a()

    assert checkpoint.model_dump(mode="json") == _load_fixture(
        "reference_agentic_de_membrane_checkpoint.json"
    )
    assert diagnostics.model_dump(mode="json") == _load_fixture(
        "reference_agentic_de_morph_diagnostics.json"
    )
    assert conformance.model_dump(mode="json") == _load_fixture(
        "reference_agentic_de_conformance_report.json"
    )

    assert checkpoint.schema == "agentic_de_membrane_checkpoint@1"
    assert checkpoint.status == "accepted"
    assert checkpoint.reason_code is None
    assert checkpoint.dry_run_only is True
    assert checkpoint.action_ticket_issuable is False
    assert checkpoint.live_effect_authorized is False

    assert diagnostics.schema == "agentic_de_morph_diagnostics@1"
    assert diagnostics.finding_count == 2
    assert diagnostics.findings[0].code == "ACTION_PROPOSAL_NON_ENTITLING"

    assert conformance.schema == "agentic_de_conformance_report@1"
    assert conformance.executed_or_observed_effect == "no_live_effect"
    assert conformance.live_effect_present is False
    assert conformance.conformance_status == "dry_run_aligned"


def test_missing_evidence_residualizes_with_reason_code() -> None:
    proposal_payload = _fixture_payload(DEFAULT_ACTION_PROPOSAL_PATH)
    proposal_payload["evidence_refs"] = []
    proposal_payload["proposal_id"] = None
    proposal = AgenticDeActionProposal.model_validate(proposal_payload)

    checkpoint, diagnostics, _conformance = run_agentic_de_interaction_v56a(
        domain_packet_path=DEFAULT_DOMAIN_PACKET_PATH,
        morph_ir_path=DEFAULT_MORPH_IR_PATH,
        interaction_contract_path=DEFAULT_INTERACTION_CONTRACT_PATH,
        action_proposal_path=DEFAULT_ACTION_PROPOSAL_PATH,
    )

    assert checkpoint.status == "accepted"
    assert diagnostics.findings[0].code == "ACTION_PROPOSAL_NON_ENTITLING"

    domain_packet = load_domain_packet(DEFAULT_DOMAIN_PACKET_PATH)
    morph_ir = load_morph_ir(DEFAULT_MORPH_IR_PATH)
    contract = load_interaction_contract(DEFAULT_INTERACTION_CONTRACT_PATH)
    from adeu_agentic_de.checker import _build_checkpoint

    residualized = _build_checkpoint(
        domain_packet=domain_packet,
        morph_ir=morph_ir,
        contract=contract,
        proposal=proposal,
    )
    assert residualized.status == "residualized"
    assert residualized.reason_code == "insufficient_evidence"


def test_not_evaluable_yet_is_reason_code_not_status() -> None:
    morph_payload = _fixture_payload(DEFAULT_MORPH_IR_PATH)
    morph_payload["evaluation_readiness"] = "not_evaluable_yet"
    morph_payload["morph_ir_id"] = None
    morph_ir = AgenticDeMorphIr.model_validate(morph_payload)
    contract_payload = _fixture_payload(DEFAULT_INTERACTION_CONTRACT_PATH)
    contract_payload["morph_ir_ref"] = morph_ir.morph_ir_id
    contract_payload["contract_id"] = None
    contract = AgenticDeInteractionContract.model_validate(contract_payload)
    proposal_payload = _fixture_payload(DEFAULT_ACTION_PROPOSAL_PATH)
    proposal_payload["contract_ref"] = contract.contract_id
    proposal_payload["proposal_id"] = None
    proposal = AgenticDeActionProposal.model_validate(proposal_payload)

    from adeu_agentic_de.checker import _build_checkpoint

    checkpoint = _build_checkpoint(
        domain_packet=load_domain_packet(DEFAULT_DOMAIN_PACKET_PATH),
        morph_ir=morph_ir,
        contract=contract,
        proposal=proposal,
    )

    assert checkpoint.status == "residualized"
    assert checkpoint.reason_code == "not_evaluable_yet"


def test_unknown_action_id_rejects_by_form() -> None:
    proposal_payload = _fixture_payload(DEFAULT_ACTION_PROPOSAL_PATH)
    proposal_payload["action_id"] = "unknown_action"
    proposal_payload["proposal_id"] = None
    proposal = AgenticDeActionProposal.model_validate(proposal_payload)

    from adeu_agentic_de.checker import _build_checkpoint

    checkpoint = _build_checkpoint(
        domain_packet=load_domain_packet(DEFAULT_DOMAIN_PACKET_PATH),
        morph_ir=load_morph_ir(DEFAULT_MORPH_IR_PATH),
        contract=load_interaction_contract(DEFAULT_INTERACTION_CONTRACT_PATH),
        proposal=proposal,
    )

    assert checkpoint.status == "rejected_by_form"
    assert checkpoint.reason_code == "proposal_malformed"


def test_missing_authority_blocks_with_reason_code() -> None:
    proposal_payload = _fixture_payload(DEFAULT_ACTION_PROPOSAL_PATH)
    proposal_payload["authority_basis_refs"] = []
    proposal_payload["proposal_id"] = None
    proposal = AgenticDeActionProposal.model_validate(proposal_payload)

    from adeu_agentic_de.checker import _build_checkpoint

    checkpoint = _build_checkpoint(
        domain_packet=load_domain_packet(DEFAULT_DOMAIN_PACKET_PATH),
        morph_ir=load_morph_ir(DEFAULT_MORPH_IR_PATH),
        contract=load_interaction_contract(DEFAULT_INTERACTION_CONTRACT_PATH),
        proposal=proposal,
    )

    assert checkpoint.status == "blocked"
    assert checkpoint.reason_code == "authority_missing"


def test_missing_schema_marker_fails_closed_on_loader(tmp_path: Path) -> None:
    payload = _fixture_payload(DEFAULT_DOMAIN_PACKET_PATH)
    payload.pop("schema")
    path = tmp_path / "domain_packet_missing_schema.json"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="missing required schema marker"):
        load_domain_packet(path)


@pytest.mark.parametrize(
    ("model_cls", "payload_builder", "id_field"),
    [
        (
            AgenticDeDomainPacket,
            lambda: _load_fixture("reference_agentic_de_domain_packet.json"),
            "packet_id",
        ),
        (
            AgenticDeMorphIr,
            lambda: _load_fixture("reference_agentic_de_morph_ir.json"),
            "morph_ir_id",
        ),
        (
            AgenticDeInteractionContract,
            lambda: _load_fixture("reference_agentic_de_interaction_contract.json"),
            "contract_id",
        ),
        (
            AgenticDeActionProposal,
            lambda: _load_fixture("reference_agentic_de_action_proposal.json"),
            "proposal_id",
        ),
        (
            AgenticDeMembraneCheckpoint,
            lambda: _load_fixture("reference_agentic_de_membrane_checkpoint.json"),
            "checkpoint_id",
        ),
        (
            AgenticDeMorphDiagnosticFinding,
            lambda: _load_fixture("reference_agentic_de_morph_diagnostics.json")["findings"][0],
            "finding_id",
        ),
        (
            AgenticDeMorphDiagnostics,
            lambda: _load_fixture("reference_agentic_de_morph_diagnostics.json"),
            "diagnostics_id",
        ),
        (
            AgenticDeConformanceReport,
            lambda: _load_fixture("reference_agentic_de_conformance_report.json"),
            "report_id",
        ),
    ],
)
def test_provided_content_addressed_ids_must_match_payload(
    model_cls: type[object],
    payload_builder: object,
    id_field: str,
) -> None:
    payload = dict(payload_builder())
    payload[id_field] = f"{payload[id_field]}_tampered"

    with pytest.raises(ValueError, match=f"{id_field} mismatch"):
        model_cls.model_validate(payload)
