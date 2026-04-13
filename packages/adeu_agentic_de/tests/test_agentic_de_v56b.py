from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_agentic_de import (
    DEFAULT_ACTION_PROPOSAL_PATH,
    DEFAULT_DOMAIN_PACKET_PATH,
    DEFAULT_INTERACTION_CONTRACT_PATH,
    DEFAULT_MORPH_IR_PATH,
    DEFAULT_V56B_ACTION_CLASS_TAXONOMY_PATH,
    DEFAULT_V56B_RUNTIME_STATE_PATH,
    AgenticDeActionClassTaxonomy,
    AgenticDeActionProposal,
    AgenticDeInteractionContract,
    AgenticDeMorphIr,
    AgenticDeRuntimeState,
    load_action_class_taxonomy,
    load_domain_packet,
    run_agentic_de_interaction_v56b,
)

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v56b"


def _fixture_payload(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_fixture(name: str) -> dict[str, object]:
    return _fixture_payload(FIXTURE_ROOT / name)


def test_reference_v56b_run_issues_local_ticket_and_matches_fixtures() -> None:
    checkpoint, runtime_state, ticket, diagnostics, conformance = run_agentic_de_interaction_v56b()

    assert checkpoint.status == "accepted"
    assert checkpoint.reason_code is None
    assert runtime_state.model_dump(mode="json") == _load_fixture(
        "reference_agentic_de_runtime_state.json"
    )
    assert ticket is not None
    assert ticket.model_dump(mode="json") == _load_fixture(
        "reference_agentic_de_action_ticket.json"
    )
    assert diagnostics.model_dump(mode="json") == _load_fixture(
        "reference_agentic_de_morph_diagnostics.json"
    )
    assert conformance.model_dump(mode="json") == _load_fixture(
        "reference_agentic_de_conformance_report.json"
    )
    assert ticket.exact_action_class == "local_write"


def test_checkpoint_acceptance_is_not_sufficient_without_selected_live_class(
    tmp_path: Path,
) -> None:
    runtime_payload = _fixture_payload(DEFAULT_V56B_RUNTIME_STATE_PATH)
    runtime_payload["selected_live_action_classes"] = ["local_reversible_execute"]
    runtime_payload["state_id"] = None
    runtime_path = tmp_path / "runtime_state.json"
    runtime_path.write_text(
        json.dumps(runtime_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    checkpoint, _runtime_state, ticket, diagnostics, conformance = run_agentic_de_interaction_v56b(
        runtime_state_path=runtime_path
    )

    assert checkpoint.status == "accepted"
    assert ticket is None
    assert diagnostics.findings[-1].code == "LIVE_ACTION_TICKET_WITHHELD"
    assert "ticket_issued=false" in conformance.delta_notes


def test_not_evaluable_yet_reason_code_blocks_ticket_issuance(tmp_path: Path) -> None:
    morph_payload = _fixture_payload(DEFAULT_MORPH_IR_PATH)
    morph_payload["evaluation_readiness"] = "not_evaluable_yet"
    morph_payload["morph_ir_id"] = None
    morph_ir = AgenticDeMorphIr.model_validate(morph_payload)
    morph_path = tmp_path / "morph_ir.json"
    morph_path.write_text(
        json.dumps(morph_ir.model_dump(mode="json"), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    contract_payload = _fixture_payload(DEFAULT_INTERACTION_CONTRACT_PATH)
    contract_payload["morph_ir_ref"] = morph_ir.morph_ir_id
    contract_payload["contract_id"] = None
    contract = AgenticDeInteractionContract.model_validate(contract_payload)
    contract_path = tmp_path / "interaction_contract.json"
    contract_path.write_text(
        json.dumps(contract.model_dump(mode="json"), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    proposal_payload = _fixture_payload(DEFAULT_ACTION_PROPOSAL_PATH)
    proposal_payload["contract_ref"] = contract.contract_id
    proposal_payload["proposal_id"] = None
    proposal = AgenticDeActionProposal.model_validate(proposal_payload)
    proposal_path = tmp_path / "action_proposal.json"
    proposal_path.write_text(
        json.dumps(proposal.model_dump(mode="json"), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    from adeu_agentic_de.checker import _build_checkpoint

    checkpoint = _build_checkpoint(
        domain_packet=load_domain_packet(DEFAULT_DOMAIN_PACKET_PATH),
        morph_ir=morph_ir,
        contract=contract,
        proposal=proposal,
    )
    runtime_payload = _fixture_payload(DEFAULT_V56B_RUNTIME_STATE_PATH)
    runtime_payload["contract_ref"] = contract.contract_id
    runtime_payload["checkpoint_ref"] = checkpoint.checkpoint_id
    runtime_payload["state_id"] = None
    runtime_state = AgenticDeRuntimeState.model_validate(runtime_payload)
    runtime_state_path = tmp_path / "runtime_state.json"
    runtime_state_path.write_text(
        json.dumps(runtime_state.model_dump(mode="json"), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    taxonomy_payload = _fixture_payload(DEFAULT_V56B_ACTION_CLASS_TAXONOMY_PATH)
    taxonomy_payload["contract_ref"] = contract.contract_id
    taxonomy_payload["taxonomy_id"] = None
    taxonomy_path = tmp_path / "taxonomy.json"
    taxonomy_path.write_text(
        json.dumps(taxonomy_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    checkpoint, _runtime_state, ticket, diagnostics, _conformance = run_agentic_de_interaction_v56b(
        morph_ir_path=morph_path,
        interaction_contract_path=contract_path,
        action_proposal_path=proposal_path,
        action_class_taxonomy_path=taxonomy_path,
        runtime_state_path=runtime_state_path,
    )

    assert checkpoint.status == "residualized"
    assert checkpoint.reason_code == "not_evaluable_yet"
    assert ticket is None
    assert diagnostics.findings[-1].code == "LIVE_ACTION_TICKET_WITHHELD"


def test_local_write_taxonomy_excludes_authority_bearing_surfaces() -> None:
    payload = _load_fixture("reference_agentic_de_action_class_taxonomy.json")
    payload["entries"][0]["write_surface_category"] = "lock_doc"
    payload["taxonomy_id"] = None

    with pytest.raises(ValueError, match="local_write must remain bounded_local_artifact"):
        AgenticDeActionClassTaxonomy.model_validate(payload)


def test_lane_drift_record_requires_expected_assumptions(tmp_path: Path) -> None:
    payload = _load_fixture("reference_agentic_de_lane_drift_record.json")
    payload["entries"] = payload["entries"][:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    path = tmp_path / "lane_drift.json"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="unexpected V56-B lane drift assumptions"):
        run_agentic_de_interaction_v56b(lane_drift_path=path)


def test_action_taxonomy_must_classify_the_proposed_action(tmp_path: Path) -> None:
    payload = _fixture_payload(DEFAULT_V56B_ACTION_CLASS_TAXONOMY_PATH)
    payload["entries"][0]["action_id"] = "different_action"
    payload["taxonomy_id"] = None
    path = tmp_path / "taxonomy.json"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="does not classify the proposed action"):
        run_agentic_de_interaction_v56b(action_class_taxonomy_path=path)


def test_invalid_taxonomy_contract_is_rejected_before_runtime_compatibility_return(
    tmp_path: Path,
) -> None:
    taxonomy_payload = _fixture_payload(DEFAULT_V56B_ACTION_CLASS_TAXONOMY_PATH)
    taxonomy_payload["contract_ref"] = "agentic_de_interaction_contract@1:wrong"
    taxonomy_payload["taxonomy_id"] = None
    taxonomy_path = tmp_path / "taxonomy.json"
    taxonomy_path.write_text(
        json.dumps(taxonomy_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    runtime_payload = _fixture_payload(DEFAULT_V56B_RUNTIME_STATE_PATH)
    runtime_payload["compatibility_status"] = "incompatible"
    runtime_payload["compatibility_note"] = "incompatible for fail-closed taxonomy validation"
    runtime_payload["state_id"] = None
    runtime_path = tmp_path / "runtime_state.json"
    runtime_path.write_text(
        json.dumps(runtime_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    with pytest.raises(ValueError, match="does not bind the provided interaction contract"):
        run_agentic_de_interaction_v56b(
            action_class_taxonomy_path=taxonomy_path,
            runtime_state_path=runtime_path,
        )


def test_dispatch_taxonomy_requires_not_applicable_reversibility_mode() -> None:
    payload = _load_fixture("reference_agentic_de_action_class_taxonomy.json")
    payload["entries"][0]["action_id"] = "dispatch_action"
    payload["entries"][0]["base_action_class"] = "dispatch"
    payload["entries"][0]["exact_action_class"] = "delegated_or_external_dispatch"
    payload["entries"][0]["reversibility_mode"] = "rollback_defined_and_testable"
    payload["entries"][0]["write_surface_category"] = "dispatch_surface"
    payload["entries"][0]["live_selected_in_v56b"] = False
    payload["taxonomy_id"] = None

    with pytest.raises(
        ValueError,
        match="delegated_or_external_dispatch may not declare a reversibility mode",
    ):
        AgenticDeActionClassTaxonomy.model_validate(payload)


def test_load_action_class_taxonomy_round_trips_reference_fixture() -> None:
    loaded = load_action_class_taxonomy(DEFAULT_V56B_ACTION_CLASS_TAXONOMY_PATH)

    assert loaded.model_dump(mode="json") == _load_fixture(
        "reference_agentic_de_action_class_taxonomy.json"
    )
