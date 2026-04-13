from __future__ import annotations

import json
from pathlib import Path

from adeu_ir.repo import repo_root

from .models import (
    AGENTIC_DE_ACTION_CLASS_TAXONOMY_SCHEMA,
    AGENTIC_DE_ACTION_PROPOSAL_SCHEMA,
    AGENTIC_DE_DOMAIN_PACKET_SCHEMA,
    AGENTIC_DE_INTERACTION_CONTRACT_SCHEMA,
    AGENTIC_DE_LANE_DRIFT_RECORD_SCHEMA,
    AGENTIC_DE_MORPH_IR_SCHEMA,
    AGENTIC_DE_RUNTIME_STATE_SCHEMA,
    AgenticDeActionClassTaxonomy,
    AgenticDeActionClassTaxonomyEntry,
    AgenticDeActionProposal,
    AgenticDeActionTicket,
    AgenticDeConformanceReport,
    AgenticDeDomainPacket,
    AgenticDeInteractionContract,
    AgenticDeInteractionContractEntry,
    AgenticDeLaneDriftRecord,
    AgenticDeMembraneCheckpoint,
    AgenticDeMorphDiagnosticFinding,
    AgenticDeMorphDiagnostics,
    AgenticDeMorphIr,
    AgenticDeRuntimeState,
)

CHECKER_VERSION = "agentic_de_interaction_v56a"
V56A_CHECKER_VERSION = CHECKER_VERSION
V56B_CHECKER_VERSION = "agentic_de_interaction_v56b"


def _default_fixture_path(variant: str, filename: str) -> Path:
    root = repo_root(anchor=Path(__file__))
    return root / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / variant / filename


DEFAULT_DOMAIN_PACKET_PATH = _default_fixture_path(
    "v56a", "reference_agentic_de_domain_packet.json"
)
DEFAULT_MORPH_IR_PATH = _default_fixture_path("v56a", "reference_agentic_de_morph_ir.json")
DEFAULT_INTERACTION_CONTRACT_PATH = _default_fixture_path(
    "v56a",
    "reference_agentic_de_interaction_contract.json",
)
DEFAULT_ACTION_PROPOSAL_PATH = _default_fixture_path(
    "v56a", "reference_agentic_de_action_proposal.json"
)
DEFAULT_V56B_LANE_DRIFT_PATH = _default_fixture_path(
    "v56b", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V56B_ACTION_CLASS_TAXONOMY_PATH = _default_fixture_path(
    "v56b", "reference_agentic_de_action_class_taxonomy.json"
)
DEFAULT_V56B_RUNTIME_STATE_PATH = _default_fixture_path(
    "v56b", "reference_agentic_de_runtime_state.json"
)


def _read_json_object(path: Path) -> dict[str, object]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path} must contain one JSON object")
    if "schema" not in payload:
        raise ValueError(f"{path} missing required schema marker")
    schema_value = payload["schema"]
    if not isinstance(schema_value, str) or not schema_value.strip():
        raise ValueError(f"{path} has invalid schema marker")
    return payload


def load_domain_packet(path: Path) -> AgenticDeDomainPacket:
    payload = AgenticDeDomainPacket.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_DOMAIN_PACKET_SCHEMA:
        raise ValueError(f"unexpected schema marker for domain packet: {payload.schema}")
    return payload


def load_morph_ir(path: Path) -> AgenticDeMorphIr:
    payload = AgenticDeMorphIr.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_MORPH_IR_SCHEMA:
        raise ValueError(f"unexpected schema marker for morph IR: {payload.schema}")
    return payload


def load_interaction_contract(path: Path) -> AgenticDeInteractionContract:
    payload = AgenticDeInteractionContract.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_INTERACTION_CONTRACT_SCHEMA:
        raise ValueError(f"unexpected schema marker for interaction contract: {payload.schema}")
    return payload


def load_action_proposal(path: Path) -> AgenticDeActionProposal:
    payload = AgenticDeActionProposal.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_ACTION_PROPOSAL_SCHEMA:
        raise ValueError(f"unexpected schema marker for action proposal: {payload.schema}")
    return payload


def load_action_class_taxonomy(path: Path) -> AgenticDeActionClassTaxonomy:
    payload = AgenticDeActionClassTaxonomy.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_ACTION_CLASS_TAXONOMY_SCHEMA:
        raise ValueError(f"unexpected schema marker for action class taxonomy: {payload.schema}")
    return payload


def load_runtime_state(path: Path) -> AgenticDeRuntimeState:
    payload = AgenticDeRuntimeState.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_RUNTIME_STATE_SCHEMA:
        raise ValueError(f"unexpected schema marker for runtime state: {payload.schema}")
    return payload


def load_lane_drift_record(path: Path) -> AgenticDeLaneDriftRecord:
    payload = AgenticDeLaneDriftRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_LANE_DRIFT_RECORD_SCHEMA:
        raise ValueError(f"unexpected schema marker for lane drift record: {payload.schema}")
    return payload


def _contract_entry_for_action(
    contract: AgenticDeInteractionContract,
    *,
    action_id: str,
) -> AgenticDeInteractionContractEntry | None:
    for entry in contract.interactions:
        if entry.action_id == action_id:
            return entry
    return None


def _taxonomy_entry_for_action(
    taxonomy: AgenticDeActionClassTaxonomy,
    *,
    action_id: str,
) -> AgenticDeActionClassTaxonomyEntry | None:
    for entry in taxonomy.entries:
        if entry.action_id == action_id:
            return entry
    return None


def _validate_taxonomy_for_proposal(
    *,
    contract: AgenticDeInteractionContract,
    proposal: AgenticDeActionProposal,
    taxonomy: AgenticDeActionClassTaxonomy,
) -> AgenticDeActionClassTaxonomyEntry:
    if taxonomy.contract_ref != contract.contract_id:
        raise ValueError("action taxonomy does not bind the provided interaction contract")
    taxonomy_entry = _taxonomy_entry_for_action(taxonomy, action_id=proposal.action_id)
    if taxonomy_entry is None:
        raise ValueError("action taxonomy does not classify the proposed action")
    if taxonomy_entry.base_action_class != proposal.action_class:
        raise ValueError("action taxonomy base class does not match the proposed action class")
    return taxonomy_entry


def _validate_v56b_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != "vNext+153":
        raise ValueError(
            f"V56-B lane drift record must target 'vNext+153', got {record.target_arc!r}"
        )
    if record.target_path != "V56-B":
        raise ValueError(f"V56-B lane drift record must target 'V56-B', got {record.target_path!r}")
    if record.prior_lane_ref != "docs/LOCKED_CONTINUATION_vNEXT_PLUS152.md":
        raise ValueError(
            "V56-B lane drift record must reference docs/LOCKED_CONTINUATION_vNEXT_PLUS152.md"
        )
    expected_assumptions = {
        "v56a_surface_reuse_default",
        "exact_action_class_taxonomy",
        "accepted_necessary_not_sufficient_for_ticket_issuance",
        "selected_live_subset_local_only",
    }
    actual_assumptions = {entry.assumption_ref for entry in record.entries}
    if actual_assumptions != expected_assumptions:
        missing = sorted(expected_assumptions - actual_assumptions)
        extra = sorted(actual_assumptions - expected_assumptions)
        parts: list[str] = []
        if missing:
            parts.append(f"missing={missing}")
        if extra:
            parts.append(f"extra={extra}")
        raise ValueError("unexpected V56-B lane drift assumptions: " + ", ".join(parts))
    return record


def _build_checkpoint(
    *,
    domain_packet: AgenticDeDomainPacket,
    morph_ir: AgenticDeMorphIr,
    contract: AgenticDeInteractionContract,
    proposal: AgenticDeActionProposal,
) -> AgenticDeMembraneCheckpoint:
    reason_code: str | None = None
    status: str
    explanation: str

    contract_entry = _contract_entry_for_action(contract, action_id=proposal.action_id)
    if contract.domain_packet_ref != domain_packet.packet_id:
        status = "rejected_by_form"
        reason_code = "proposal_malformed"
        explanation = "interaction contract does not bind the provided domain packet"
    elif morph_ir.domain_packet_ref != domain_packet.packet_id:
        status = "rejected_by_form"
        reason_code = "proposal_malformed"
        explanation = "morph IR does not bind the provided domain packet"
    elif contract.morph_ir_ref != morph_ir.morph_ir_id:
        status = "rejected_by_form"
        reason_code = "proposal_malformed"
        explanation = "interaction contract does not bind the provided morph IR"
    elif (
        proposal.domain_packet_ref != domain_packet.packet_id
        or proposal.contract_ref != contract.contract_id
    ):
        status = "rejected_by_form"
        reason_code = "proposal_malformed"
        explanation = "action proposal refs do not match the provided packet/contract"
    elif contract_entry is None:
        status = "rejected_by_form"
        reason_code = "proposal_malformed"
        explanation = "action proposal references an unknown contract action"
    elif contract_entry.action_class != proposal.action_class:
        status = "rejected_by_form"
        reason_code = "proposal_malformed"
        explanation = "action proposal class does not match the contract entry"
    elif domain_packet.capability_posture != "dry_run_only":
        status = "blocked"
        reason_code = "out_of_scope"
        explanation = "V56-A only admits dry-run-only capability posture"
    elif morph_ir.evaluation_readiness != "ready":
        status = "residualized"
        reason_code = "not_evaluable_yet"
        explanation = "morph IR marks the proposal as not yet evaluable under the current packet"
    elif contract_entry.evidence_required and not proposal.evidence_refs:
        status = "residualized"
        reason_code = "insufficient_evidence"
        explanation = "proposal requires evidence refs before checkpoint acceptance"
    elif contract_entry.authority_required and not proposal.authority_basis_refs:
        status = "blocked"
        reason_code = "authority_missing"
        explanation = "proposal requires authority basis refs before checkpoint acceptance"
    else:
        status = "accepted"
        reason_code = None
        explanation = (
            "proposal is checkpointable in dry-run mode only; no live write/execute/dispatch "
            "entitlement is carried in V56-A"
        )

    return AgenticDeMembraneCheckpoint(
        domain_packet_ref=domain_packet.packet_id,
        contract_ref=contract.contract_id,
        proposal_ref=proposal.proposal_id,
        status=status,
        reason_code=reason_code,
        status_explanation=explanation,
    )


def _build_diagnostics(
    *,
    domain_packet: AgenticDeDomainPacket,
    proposal: AgenticDeActionProposal,
    checkpoint: AgenticDeMembraneCheckpoint,
    extra_findings: list[AgenticDeMorphDiagnosticFinding] | None = None,
) -> AgenticDeMorphDiagnostics:
    findings: list[AgenticDeMorphDiagnosticFinding] = [
        AgenticDeMorphDiagnosticFinding(
            severity="info",
            code="ACTION_PROPOSAL_NON_ENTITLING",
            subject_ref=proposal.proposal_id,
            message=(
                "V56-A proposals remain non-entitling: candidate action, claimed basis, "
                "and dry-run checkpointability only"
            ),
        )
    ]
    if checkpoint.status == "accepted":
        findings.append(
            AgenticDeMorphDiagnosticFinding(
                severity="info",
                code="DRY_RUN_CHECKPOINT_ACCEPTED",
                subject_ref=checkpoint.checkpoint_id,
                message=checkpoint.status_explanation,
            )
        )
    else:
        findings.append(
            AgenticDeMorphDiagnosticFinding(
                severity="warn" if checkpoint.status in {"blocked", "residualized"} else "error",
                code=f"DRY_RUN_CHECKPOINT_{checkpoint.status.upper()}",
                subject_ref=checkpoint.checkpoint_id,
                message=checkpoint.status_explanation,
            )
        )
    if extra_findings:
        findings.extend(extra_findings)
    return AgenticDeMorphDiagnostics(
        packet_ref=domain_packet.packet_id,
        proposal_ref=proposal.proposal_id,
        checkpoint_ref=checkpoint.checkpoint_id,
        finding_count=len(findings),
        findings=findings,
    )


def _build_conformance_report(
    *,
    domain_packet: AgenticDeDomainPacket,
    proposal: AgenticDeActionProposal,
    checkpoint: AgenticDeMembraneCheckpoint,
    extra_delta_notes: list[str] | None = None,
) -> AgenticDeConformanceReport:
    conformance_status = (
        "dry_run_aligned" if checkpoint.live_effect_authorized is False else "dry_run_divergent"
    )
    entitlement_summary = (
        "dry_run_checkpoint_accepted_non_entitling"
        if checkpoint.status == "accepted"
        else f"dry_run_checkpoint_{checkpoint.status}"
    )
    return AgenticDeConformanceReport(
        packet_ref=domain_packet.packet_id,
        proposal_ref=proposal.proposal_id,
        checkpoint_ref=checkpoint.checkpoint_id,
        packed_state_summary=domain_packet.task_scope_summary,
        proposed_action_summary=proposal.requested_effect_summary,
        checkpoint_entitlement_summary=entitlement_summary,
        conformance_status=conformance_status,
        delta_notes=[
            "proposal remained non-entitling in V56-A",
            f"checkpoint status={checkpoint.status}",
            "executed_or_observed_effect=no_live_effect",
            *(extra_delta_notes or []),
        ],
    )


def run_agentic_de_interaction_v56a(
    *,
    domain_packet_path: Path = DEFAULT_DOMAIN_PACKET_PATH,
    morph_ir_path: Path = DEFAULT_MORPH_IR_PATH,
    interaction_contract_path: Path = DEFAULT_INTERACTION_CONTRACT_PATH,
    action_proposal_path: Path = DEFAULT_ACTION_PROPOSAL_PATH,
) -> tuple[AgenticDeMembraneCheckpoint, AgenticDeMorphDiagnostics, AgenticDeConformanceReport]:
    domain_packet = load_domain_packet(domain_packet_path)
    morph_ir = load_morph_ir(morph_ir_path)
    contract = load_interaction_contract(interaction_contract_path)
    proposal = load_action_proposal(action_proposal_path)
    checkpoint = _build_checkpoint(
        domain_packet=domain_packet,
        morph_ir=morph_ir,
        contract=contract,
        proposal=proposal,
    )
    diagnostics = _build_diagnostics(
        domain_packet=domain_packet,
        proposal=proposal,
        checkpoint=checkpoint,
    )
    conformance = _build_conformance_report(
        domain_packet=domain_packet,
        proposal=proposal,
        checkpoint=checkpoint,
    )
    return checkpoint, diagnostics, conformance


def _issue_action_ticket(
    *,
    domain_packet: AgenticDeDomainPacket,
    contract: AgenticDeInteractionContract,
    proposal: AgenticDeActionProposal,
    checkpoint: AgenticDeMembraneCheckpoint,
    taxonomy: AgenticDeActionClassTaxonomy,
    runtime_state: AgenticDeRuntimeState,
) -> tuple[AgenticDeActionTicket | None, str]:
    if runtime_state.domain_packet_ref != domain_packet.packet_id:
        raise ValueError("runtime state does not bind the provided domain packet")
    if runtime_state.contract_ref != contract.contract_id:
        raise ValueError("runtime state does not bind the provided interaction contract")
    if runtime_state.checkpoint_ref != checkpoint.checkpoint_id:
        raise ValueError("runtime state does not bind the provided checkpoint")
    if runtime_state.authority_frame_ref != domain_packet.authority_frame_ref:
        raise ValueError("runtime state authority frame does not match the domain packet")
    taxonomy_entry = _validate_taxonomy_for_proposal(
        contract=contract,
        proposal=proposal,
        taxonomy=taxonomy,
    )
    if checkpoint.status != "accepted":
        return None, f"checkpoint status {checkpoint.status} is non-entitling for ticket issuance"
    if runtime_state.compatibility_status != "compatible":
        return None, "runtime state is not compatible for live ticket issuance"
    if not taxonomy_entry.live_selected_in_v56b:
        return (
            None,
            "action taxonomy marks the proposed action as not selected for V56-B live gating",
        )
    if taxonomy_entry.exact_action_class not in runtime_state.selected_live_action_classes:
        return None, "runtime state does not admit the proposed exact action class"
    if runtime_state.issuance_capability_posture != "live_gate_required":
        return None, "runtime state capability posture is not live_gate_required"
    ticket = AgenticDeActionTicket(
        domain_packet_ref=domain_packet.packet_id,
        contract_ref=contract.contract_id,
        proposal_ref=proposal.proposal_id,
        checkpoint_ref=checkpoint.checkpoint_id,
        runtime_state_ref=runtime_state.state_id,
        taxonomy_ref=taxonomy.taxonomy_id,
        exact_action_class=taxonomy_entry.exact_action_class,
        authority_frame_ref=runtime_state.authority_frame_ref,
        ticket_scope_summary=runtime_state.ticket_scope_summary,
    )
    return ticket, "ticket issued for bounded local live action class"


def run_agentic_de_interaction_v56b(
    *,
    domain_packet_path: Path = DEFAULT_DOMAIN_PACKET_PATH,
    morph_ir_path: Path = DEFAULT_MORPH_IR_PATH,
    interaction_contract_path: Path = DEFAULT_INTERACTION_CONTRACT_PATH,
    action_proposal_path: Path = DEFAULT_ACTION_PROPOSAL_PATH,
    lane_drift_path: Path = DEFAULT_V56B_LANE_DRIFT_PATH,
    action_class_taxonomy_path: Path = DEFAULT_V56B_ACTION_CLASS_TAXONOMY_PATH,
    runtime_state_path: Path = DEFAULT_V56B_RUNTIME_STATE_PATH,
) -> tuple[
    AgenticDeMembraneCheckpoint,
    AgenticDeRuntimeState,
    AgenticDeActionTicket | None,
    AgenticDeMorphDiagnostics,
    AgenticDeConformanceReport,
]:
    _validate_v56b_lane_drift_record(load_lane_drift_record(lane_drift_path))
    domain_packet = load_domain_packet(domain_packet_path)
    morph_ir = load_morph_ir(morph_ir_path)
    contract = load_interaction_contract(interaction_contract_path)
    proposal = load_action_proposal(action_proposal_path)
    taxonomy = load_action_class_taxonomy(action_class_taxonomy_path)
    runtime_state = load_runtime_state(runtime_state_path)
    checkpoint = _build_checkpoint(
        domain_packet=domain_packet,
        morph_ir=morph_ir,
        contract=contract,
        proposal=proposal,
    )
    ticket, ticket_note = _issue_action_ticket(
        domain_packet=domain_packet,
        contract=contract,
        proposal=proposal,
        checkpoint=checkpoint,
        taxonomy=taxonomy,
        runtime_state=runtime_state,
    )
    extra_findings = [
        AgenticDeMorphDiagnosticFinding(
            severity="info" if ticket is not None else "warn",
            code="LIVE_ACTION_TICKET_ISSUED"
            if ticket is not None
            else "LIVE_ACTION_TICKET_WITHHELD",
            subject_ref=ticket.ticket_id if ticket is not None else checkpoint.checkpoint_id,
            message=ticket_note,
        )
    ]
    diagnostics = _build_diagnostics(
        domain_packet=domain_packet,
        proposal=proposal,
        checkpoint=checkpoint,
        extra_findings=extra_findings,
    )
    conformance = _build_conformance_report(
        domain_packet=domain_packet,
        proposal=proposal,
        checkpoint=checkpoint,
        extra_delta_notes=[
            f"ticket_issued={'true' if ticket is not None else 'false'}",
            f"ticket_ref={ticket.ticket_id if ticket is not None else 'none'}",
        ],
    )
    return checkpoint, runtime_state, ticket, diagnostics, conformance


def render_checkpoint_payload(checkpoint: AgenticDeMembraneCheckpoint) -> str:
    return json.dumps(checkpoint.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_diagnostics_payload(diagnostics: AgenticDeMorphDiagnostics) -> str:
    return json.dumps(diagnostics.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_conformance_payload(report: AgenticDeConformanceReport) -> str:
    return json.dumps(report.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_runtime_state_payload(runtime_state: AgenticDeRuntimeState) -> str:
    return json.dumps(runtime_state.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_action_ticket_payload(ticket: AgenticDeActionTicket) -> str:
    return json.dumps(ticket.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"
