from __future__ import annotations

from .models import (
    AgenticDeActionProposal,
    AgenticDeActionTicket,
    AgenticDeDomainPacket,
    AgenticDeLocalEffectConformanceReport,
    AgenticDeLocalEffectObservationRecord,
    AgenticDeMembraneCheckpoint,
    AgenticDeRuntimeHarvestRecord,
    AgenticDeRuntimeState,
)


def build_local_effect_conformance_report(
    *,
    target_arc: str,
    target_path: str,
    packet: AgenticDeDomainPacket,
    proposal: AgenticDeActionProposal,
    checkpoint: AgenticDeMembraneCheckpoint,
    runtime_state: AgenticDeRuntimeState,
    ticket: AgenticDeActionTicket,
    harvest: AgenticDeRuntimeHarvestRecord,
    observation: AgenticDeLocalEffectObservationRecord,
    evidence_refs: list[str],
) -> AgenticDeLocalEffectConformanceReport:
    conformance_status = (
        "effect_aligned"
        if observation.observation_outcome == "bounded_effect_observed"
        else "effect_divergent"
    )
    return AgenticDeLocalEffectConformanceReport(
        target_arc=target_arc,
        target_path=target_path,
        packet_ref=packet.packet_id,
        action_proposal_ref=proposal.proposal_id,
        checkpoint_ref=checkpoint.checkpoint_id,
        runtime_state_ref=runtime_state.state_id,
        ticket_ref=ticket.ticket_id,
        harvest_ref=harvest.harvest_id,
        observation_ref=observation.observation_id,
        packed_state_summary=packet.task_scope_summary,
        proposed_action_summary=proposal.requested_effect_summary,
        checkpoint_entitlement_summary=harvest.checkpoint_entitlement_summary,
        ticket_visibility_summary=f"ticket_ref={ticket.ticket_id}",
        observed_effect=observation.observed_effect,
        observation_outcome=observation.observation_outcome,
        live_effect_present=observation.observation_outcome != "no_effect_observed",
        boundedness_verdict=observation.boundedness_verdict,
        conformance_status=conformance_status,
        delta_notes=[
            f"packed_state={packet.task_scope_summary}",
            f"proposed_action={proposal.requested_effect_summary}",
            f"checkpoint_entitlement={harvest.checkpoint_entitlement_summary}",
            "ticket_issued=true",
            f"ticket_ref={ticket.ticket_id}",
            f"pre_state_ref={observation.pre_state_ref}",
            f"post_state_ref={observation.post_state_ref}",
            f"observed_effect={observation.observed_effect}",
            f"observation_outcome={observation.observation_outcome}",
            f"boundedness_verdict={observation.boundedness_verdict}",
        ],
        evidence_refs=evidence_refs,
    )
