from __future__ import annotations

import json
from pathlib import Path

from adeu_ir.repo import repo_root

from .models import (
    AGENTIC_DE_ACTION_CLASS_TAXONOMY_SCHEMA,
    AGENTIC_DE_ACTION_PROPOSAL_SCHEMA,
    AGENTIC_DE_ACTION_TICKET_SCHEMA,
    AGENTIC_DE_CONFORMANCE_REPORT_SCHEMA,
    AGENTIC_DE_DOMAIN_PACKET_SCHEMA,
    AGENTIC_DE_INTERACTION_CONTRACT_SCHEMA,
    AGENTIC_DE_LANE_DRIFT_RECORD_SCHEMA,
    AGENTIC_DE_MEMBRANE_CHECKPOINT_SCHEMA,
    AGENTIC_DE_MORPH_DIAGNOSTICS_SCHEMA,
    AGENTIC_DE_MORPH_IR_SCHEMA,
    AGENTIC_DE_RUNTIME_STATE_SCHEMA,
    AgenticDeActionClassTaxonomy,
    AgenticDeActionClassTaxonomyEntry,
    AgenticDeActionProposal,
    AgenticDeActionTicket,
    AgenticDeConformanceReport,
    AgenticDeDomainPacket,
    AgenticDeGovernanceCalibrationEntry,
    AgenticDeGovernanceCalibrationRegister,
    AgenticDeInteractionContract,
    AgenticDeInteractionContractEntry,
    AgenticDeLaneDriftRecord,
    AgenticDeMembraneCheckpoint,
    AgenticDeMigrationDecisionEntry,
    AgenticDeMigrationDecisionRegister,
    AgenticDeMorphDiagnosticFinding,
    AgenticDeMorphDiagnostics,
    AgenticDeMorphIr,
    AgenticDeRuntimeHarvestRecord,
    AgenticDeRuntimeState,
)

CHECKER_VERSION = "agentic_de_interaction_v56a"
V56A_CHECKER_VERSION = CHECKER_VERSION
V56B_CHECKER_VERSION = "agentic_de_interaction_v56b"
V56C_CHECKER_VERSION = "agentic_de_interaction_v56c"
V56C_TARGET_ARC = "vNext+154"
V56C_TARGET_PATH = "V56-C"


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
DEFAULT_V56A_CHECKPOINT_PATH = _default_fixture_path(
    "v56a", "reference_agentic_de_membrane_checkpoint.json"
)
DEFAULT_V56A_DIAGNOSTICS_PATH = _default_fixture_path(
    "v56a", "reference_agentic_de_morph_diagnostics.json"
)
DEFAULT_V56A_CONFORMANCE_PATH = _default_fixture_path(
    "v56a", "reference_agentic_de_conformance_report.json"
)
DEFAULT_V56B_TICKET_PATH = _default_fixture_path(
    "v56b", "reference_agentic_de_action_ticket.json"
)
DEFAULT_V56B_DIAGNOSTICS_PATH = _default_fixture_path(
    "v56b", "reference_agentic_de_morph_diagnostics.json"
)
DEFAULT_V56B_CONFORMANCE_PATH = _default_fixture_path(
    "v56b", "reference_agentic_de_conformance_report.json"
)
DEFAULT_V56C_LANE_DRIFT_PATH = _default_fixture_path(
    "v56c", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V56C_V56A_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v152"
    / "evidence_inputs"
    / "v56a_agentic_de_interaction_governance_starter_evidence_v152.json"
)
DEFAULT_V56C_V56B_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v153"
    / "evidence_inputs"
    / "v56b_bounded_live_gate_starter_evidence_v153.json"
)

EXPECTED_V56A_EVIDENCE_SCHEMA = "v56a_agentic_de_interaction_governance_starter_evidence@1"
EXPECTED_V56B_EVIDENCE_SCHEMA = "v56b_bounded_live_gate_starter_evidence@1"
EXPECTED_V56C_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS153.md"
REQUIRED_V56C_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v56b_surface_reuse_default": "holds",
    "selected_live_action_classes_closed_for_v56c": "holds",
    "selected_live_action_class_interpretation_closed_for_v56c": "holds",
    "runtime_harvest_observation_only": "amended",
    "advisory_governance_and_migration_only": "amended",
    "committed_lane_artifacts_outrank_narrative_docs": "amended",
}
EXPECTED_V56B_SELECTED_LIVE_CLASSES = (
    "local_reversible_execute",
    "local_write",
)
EXPECTED_V56B_LIVE_CLASS_DEFINITIONS = {
    "local_scope": (
        "current_bounded_workspace_process_and_sandbox_surface_only_excluding_"
        "delegated_remote_networked_or_broader_system_effects"
    ),
    "reversible_scope": (
        "rollback_or_compensating_restore_defined_and_testable_inside_the_same_"
        "local_authority_envelope"
    ),
    "local_write_exclusions": [
        "family_constitutions",
        "lock_docs",
        "ci_config",
        "secrets_or_credentials",
        "dispatch_surfaces",
    ],
}


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


def load_membrane_checkpoint(path: Path) -> AgenticDeMembraneCheckpoint:
    payload = AgenticDeMembraneCheckpoint.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_MEMBRANE_CHECKPOINT_SCHEMA:
        raise ValueError(f"unexpected schema marker for membrane checkpoint: {payload.schema}")
    return payload


def load_morph_diagnostics(path: Path) -> AgenticDeMorphDiagnostics:
    payload = AgenticDeMorphDiagnostics.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_MORPH_DIAGNOSTICS_SCHEMA:
        raise ValueError(f"unexpected schema marker for morph diagnostics: {payload.schema}")
    return payload


def load_conformance_report(path: Path) -> AgenticDeConformanceReport:
    payload = AgenticDeConformanceReport.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_CONFORMANCE_REPORT_SCHEMA:
        raise ValueError(f"unexpected schema marker for conformance report: {payload.schema}")
    return payload


def load_action_ticket(path: Path) -> AgenticDeActionTicket:
    payload = AgenticDeActionTicket.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_ACTION_TICKET_SCHEMA:
        raise ValueError(f"unexpected schema marker for action ticket: {payload.schema}")
    return payload


def _load_json_object(path: Path, *, error_label: str) -> dict[str, object]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{error_label} payload must be an object")
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


def _resolve_path(*, repo_root_path: Path, path: Path) -> Path:
    return path if path.is_absolute() else repo_root_path / path


def _render_input_ref(*, repo_root_path: Path, path: Path) -> str:
    try:
        return str(path.relative_to(repo_root_path))
    except ValueError:
        return str(path)


def _validate_v56c_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V56C_TARGET_ARC:
        raise ValueError(
            f"V56-C lane drift record must target {V56C_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V56C_TARGET_PATH:
        raise ValueError(
            f"V56-C lane drift record must target {V56C_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V56C_PRIOR_LANE_REF:
        raise ValueError(
            "V56-C lane drift record must point at "
            f"{EXPECTED_V56C_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V56C_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    unexpected_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V56C_DRIFT_ENTRY_STATUSES.items()
        if actual_statuses.get(assumption_ref) != expected_status
    )
    if missing_assumptions or unexpected_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if unexpected_statuses:
            detail_parts.append(f"status_mismatch={unexpected_statuses}")
        raise ValueError(
            "V56-C lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v56a_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V56A_EVIDENCE_SCHEMA:
        raise ValueError("V56-C requires the shipped V56-A starter evidence payload on main")
    required_true_fields = (
        "dry_run_membrane_checkpoint_required",
        "checkpoint_status_reason_separation_required",
        "surrogate_hidden_cognition_proxies_forbidden",
    )
    for field_name in required_true_fields:
        if payload.get(field_name) is not True:
            raise ValueError(f"V56-A evidence must preserve {field_name}")
    if payload.get("conformance_mode") != "typed_delta_surface":
        raise ValueError("V56-A evidence must preserve typed-delta conformance mode")
    if payload.get("conformance_effect_axis_mode_in_v56a") != "no_live_effect":
        raise ValueError("V56-A evidence must preserve no_live_effect conformance axis")
    if payload.get("runtime_state_selected") is not False:
        raise ValueError("V56-A evidence must keep runtime_state deferred")
    if payload.get("action_ticket_selected") is not False:
        raise ValueError("V56-A evidence must keep action_ticket deferred")
    return payload


def _validate_v56b_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V56B_EVIDENCE_SCHEMA:
        raise ValueError("V56-C requires the shipped V56-B live-gate evidence payload on main")
    if (
        payload.get("checkpoint_accepted_necessary_but_not_sufficient_for_ticket_issuance")
        is not True
    ):
        raise ValueError("V56-B evidence must preserve accepted-necessary-but-not-sufficient law")
    if payload.get("ticket_visibility_in_consequence_chain_required") is not True:
        raise ValueError(
            "V56-B evidence must preserve explicit ticket visibility in the "
            "consequence chain"
        )
    if payload.get("delegated_or_external_dispatch_selected_for_v56b") is not False:
        raise ValueError("V56-B evidence must keep delegated/external dispatch deferred")
    if payload.get("stronger_execute_selected_for_v56b") is not False:
        raise ValueError("V56-B evidence must keep stronger execute deferred")
    selected_live_classes = payload.get("selected_live_gate_action_classes_for_v56b")
    if selected_live_classes != list(EXPECTED_V56B_SELECTED_LIVE_CLASSES):
        raise ValueError("V56-B evidence must preserve the exact selected live class set")
    if (
        payload.get("selected_live_gate_class_definitions_for_v56b")
        != EXPECTED_V56B_LIVE_CLASS_DEFINITIONS
    ):
        raise ValueError("V56-B evidence must preserve the shipped live-class interpretation")
    return payload


def _validate_v56a_reference_surfaces(
    *,
    domain_packet: AgenticDeDomainPacket,
    morph_ir: AgenticDeMorphIr,
    contract: AgenticDeInteractionContract,
    proposal: AgenticDeActionProposal,
    checkpoint: AgenticDeMembraneCheckpoint,
    diagnostics: AgenticDeMorphDiagnostics,
    conformance: AgenticDeConformanceReport,
) -> None:
    if morph_ir.domain_packet_ref != domain_packet.packet_id:
        raise ValueError("V56-A morph IR does not bind the provided domain packet")
    if contract.domain_packet_ref != domain_packet.packet_id:
        raise ValueError("V56-A interaction contract does not bind the provided domain packet")
    if contract.morph_ir_ref != morph_ir.morph_ir_id:
        raise ValueError("V56-A interaction contract does not bind the provided morph IR")
    if proposal.domain_packet_ref != domain_packet.packet_id:
        raise ValueError("V56-A action proposal does not bind the provided domain packet")
    if proposal.contract_ref != contract.contract_id:
        raise ValueError("V56-A action proposal does not bind the provided interaction contract")
    if checkpoint.domain_packet_ref != domain_packet.packet_id:
        raise ValueError("V56-A checkpoint does not bind the provided domain packet")
    if checkpoint.contract_ref != contract.contract_id:
        raise ValueError("V56-A checkpoint does not bind the provided interaction contract")
    if checkpoint.proposal_ref != proposal.proposal_id:
        raise ValueError("V56-A checkpoint does not bind the provided action proposal")
    if diagnostics.packet_ref != domain_packet.packet_id:
        raise ValueError("V56-A diagnostics do not bind the provided domain packet")
    if diagnostics.proposal_ref != proposal.proposal_id:
        raise ValueError("V56-A diagnostics do not bind the provided action proposal")
    if diagnostics.checkpoint_ref != checkpoint.checkpoint_id:
        raise ValueError("V56-A diagnostics do not bind the provided checkpoint")
    if conformance.packet_ref != domain_packet.packet_id:
        raise ValueError("V56-A conformance does not bind the provided domain packet")
    if conformance.proposal_ref != proposal.proposal_id:
        raise ValueError("V56-A conformance does not bind the provided action proposal")
    if conformance.checkpoint_ref != checkpoint.checkpoint_id:
        raise ValueError("V56-A conformance does not bind the provided checkpoint")
    if conformance.executed_or_observed_effect != "no_live_effect":
        raise ValueError("V56-A conformance must preserve the no_live_effect axis")
    if conformance.live_effect_present is not False:
        raise ValueError("V56-A conformance must not claim a live effect")


def _validate_v56b_reference_surfaces(
    *,
    domain_packet: AgenticDeDomainPacket,
    contract: AgenticDeInteractionContract,
    proposal: AgenticDeActionProposal,
    checkpoint: AgenticDeMembraneCheckpoint,
    taxonomy: AgenticDeActionClassTaxonomy,
    runtime_state: AgenticDeRuntimeState,
    ticket: AgenticDeActionTicket,
    diagnostics: AgenticDeMorphDiagnostics,
    conformance: AgenticDeConformanceReport,
) -> None:
    taxonomy_entry = _taxonomy_entry_for_action(taxonomy, action_id=proposal.action_id)
    if taxonomy_entry is None:
        raise ValueError("V56-B taxonomy must classify the shipped reference action")
    if taxonomy_entry.exact_action_class != "local_write":
        raise ValueError("V56-C shipped reference action must remain classified as local_write")
    if taxonomy_entry.live_selected_in_v56b is not True:
        raise ValueError("V56-C shipped reference action must remain live-selected in V56-B")
    if runtime_state.domain_packet_ref != domain_packet.packet_id:
        raise ValueError("V56-B runtime state does not bind the provided domain packet")
    if runtime_state.contract_ref != contract.contract_id:
        raise ValueError("V56-B runtime state does not bind the provided interaction contract")
    if runtime_state.checkpoint_ref != checkpoint.checkpoint_id:
        raise ValueError("V56-B runtime state does not bind the provided checkpoint")
    if tuple(runtime_state.selected_live_action_classes) != EXPECTED_V56B_SELECTED_LIVE_CLASSES:
        raise ValueError("V56-B runtime state must preserve the shipped selected live class set")
    if runtime_state.compatibility_status != "compatible":
        raise ValueError(
            "V56-C reference consumption requires the shipped compatible V56-B runtime state"
        )
    if ticket.domain_packet_ref != domain_packet.packet_id:
        raise ValueError("V56-B action ticket does not bind the provided domain packet")
    if ticket.contract_ref != contract.contract_id:
        raise ValueError("V56-B action ticket does not bind the provided interaction contract")
    if ticket.proposal_ref != proposal.proposal_id:
        raise ValueError("V56-B action ticket does not bind the provided action proposal")
    if ticket.checkpoint_ref != checkpoint.checkpoint_id:
        raise ValueError("V56-B action ticket does not bind the provided checkpoint")
    if ticket.runtime_state_ref != runtime_state.state_id:
        raise ValueError("V56-B action ticket does not bind the provided runtime state")
    if ticket.taxonomy_ref != taxonomy.taxonomy_id:
        raise ValueError("V56-B action ticket does not bind the provided action taxonomy")
    if ticket.exact_action_class != "local_write":
        raise ValueError("V56-C reference path requires the shipped local_write ticket")
    if diagnostics.packet_ref != domain_packet.packet_id:
        raise ValueError("V56-B diagnostics do not bind the provided domain packet")
    if diagnostics.proposal_ref != proposal.proposal_id:
        raise ValueError("V56-B diagnostics do not bind the provided action proposal")
    if diagnostics.checkpoint_ref != checkpoint.checkpoint_id:
        raise ValueError("V56-B diagnostics do not bind the provided checkpoint")
    if conformance.packet_ref != domain_packet.packet_id:
        raise ValueError("V56-B conformance does not bind the provided domain packet")
    if conformance.proposal_ref != proposal.proposal_id:
        raise ValueError("V56-B conformance does not bind the provided action proposal")
    if conformance.checkpoint_ref != checkpoint.checkpoint_id:
        raise ValueError("V56-B conformance does not bind the provided checkpoint")
    if f"ticket_ref={ticket.ticket_id}" not in conformance.delta_notes:
        raise ValueError("V56-B conformance must preserve explicit ticket visibility")
    if "ticket_issued=true" not in conformance.delta_notes:
        raise ValueError("V56-B conformance must preserve explicit issued-ticket visibility")
    if taxonomy_entry.write_surface_category != "bounded_local_artifact":
        raise ValueError("V56-B local_write interpretation drifted from bounded_local_artifact")


def _governance_entry(
    *,
    subject_kind: str,
    subject_ref: str,
    current_posture: str,
    recommended_outcome: str,
    rationale: str,
    evidence_refs: list[str],
) -> AgenticDeGovernanceCalibrationEntry:
    return AgenticDeGovernanceCalibrationEntry(
        subject_kind=subject_kind,
        subject_ref=subject_ref,
        current_posture=current_posture,
        recommended_outcome=recommended_outcome,
        rationale=rationale,
        evidence_refs=evidence_refs,
    )


def _migration_entry(
    *,
    surface_id: str,
    current_posture: str,
    recommended_outcome: str,
    rationale: str,
    evidence_refs: list[str],
) -> AgenticDeMigrationDecisionEntry:
    return AgenticDeMigrationDecisionEntry(
        surface_id=surface_id,
        current_posture=current_posture,
        recommended_outcome=recommended_outcome,
        rationale=rationale,
        evidence_refs=evidence_refs,
    )


def _build_v56c_runtime_harvest_record(
    *,
    packet: AgenticDeDomainPacket,
    proposal: AgenticDeActionProposal,
    checkpoint: AgenticDeMembraneCheckpoint,
    runtime_state: AgenticDeRuntimeState,
    ticket: AgenticDeActionTicket,
    diagnostics: AgenticDeMorphDiagnostics,
    conformance: AgenticDeConformanceReport,
    evidence_refs: list[str],
) -> AgenticDeRuntimeHarvestRecord:
    return AgenticDeRuntimeHarvestRecord(
        target_arc=V56C_TARGET_ARC,
        target_path=V56C_TARGET_PATH,
        baseline_checker_version=V56B_CHECKER_VERSION,
        packet_ref=packet.packet_id,
        proposal_ref=proposal.proposal_id,
        checkpoint_ref=checkpoint.checkpoint_id,
        runtime_state_ref=runtime_state.state_id,
        ticket_ref=ticket.ticket_id,
        diagnostics_ref=diagnostics.diagnostics_id,
        conformance_ref=conformance.report_id,
        selected_live_action_classes=runtime_state.selected_live_action_classes,
        packed_state_summary=packet.task_scope_summary,
        proposed_action_summary=proposal.requested_effect_summary,
        checkpoint_entitlement_summary=conformance.checkpoint_entitlement_summary,
        ticket_issued=True,
        ticket_visibility_summary=f"explicit_ticket_ref:{ticket.ticket_id}",
        executed_or_observed_effect=conformance.executed_or_observed_effect,
        live_effect_present=conformance.live_effect_present,
        observed_pattern_summary=(
            "shipped V56-B evidence preserves one bounded local_write ticket over the "
            "frozen local-only live subset while conformance still records no_live_effect"
        ),
        delta_notes=[
            f"packed_state={packet.task_scope_summary}",
            f"proposed_action={proposal.requested_effect_summary}",
            f"checkpoint_entitlement={conformance.checkpoint_entitlement_summary}",
            "ticket_issued=true",
            f"ticket_ref={ticket.ticket_id}",
            f"executed_or_observed_effect={conformance.executed_or_observed_effect}",
        ],
        bounded_derived_summaries=[
            "observed pattern remains local_write-only in the shipped V56-B reference path",
            (
                "selected live class interpretation remains frozen to bounded local "
                "artifact write and locally reversible execute semantics"
            ),
            (
                "harvest stays observation-only and defers governance "
                "classification to advisory registers"
            ),
        ],
        evidence_refs=evidence_refs,
    )


def _build_v56c_governance_calibration_register(
    *,
    v56b_evidence_path: str,
    v56b_lane_drift_path: str,
    v56b_ticket_path: str,
    v56b_conformance_path: str,
    v56a_evidence_path: str,
) -> AgenticDeGovernanceCalibrationRegister:
    entries = [
        _governance_entry(
            subject_kind="action_class",
            subject_ref="local_write",
            current_posture=(
                "shipped V56-B exercises local_write only under bounded_local_artifact "
                "semantics with explicit ticket visibility and no_live_effect conformance"
            ),
            recommended_outcome="needs_more_evidence",
            rationale=(
                "the shipped reference path proves the bounded local_write issuance chain, "
                "but not an executed local effect, so later local hardening would require "
                "more post-effect evidence rather than immediate escalation"
            ),
            evidence_refs=[v56b_ticket_path, v56b_conformance_path, v56b_evidence_path],
        ),
        _governance_entry(
            subject_kind="action_class",
            subject_ref="local_reversible_execute",
            current_posture=(
                "selected in the frozen V56-B live subset but unexercised in the shipped "
                "reference path"
            ),
            recommended_outcome="not_selected_for_escalation",
            rationale=(
                "the class remains selected but unobserved in the shipped baseline, so "
                "V56-C should not infer stronger governance posture from narrative symmetry alone"
            ),
            evidence_refs=[v56b_lane_drift_path, v56b_evidence_path],
        ),
        _governance_entry(
            subject_kind="surface",
            subject_ref="checkpoint_to_ticket_boundary",
            current_posture=(
                "accepted remains necessary but not sufficient, with runtime compatibility "
                "and selected-class membership still required before ticket issuance"
            ),
            recommended_outcome="keep_warning_only",
            rationale=(
                "the shipped V56-B evidence shows the boundary law is already explicit and "
                "bounded; V56-C should preserve it without mutating live behavior by default"
            ),
            evidence_refs=[v56a_evidence_path, v56b_lane_drift_path, v56b_evidence_path],
        ),
        _governance_entry(
            subject_kind="surface",
            subject_ref="hidden_cognition_proxy_boundary",
            current_posture=(
                "only externalized packet/proposal/checkpoint/ticket/conformance artifacts "
                "are treated as governance-bearing inputs"
            ),
            recommended_outcome="keep_warning_only",
            rationale=(
                "the governed chain already excludes surrogate hidden-cognition and derived "
                "internalist proxies, and V56-C should preserve that boundary without "
                "inventing new internal telemetry surfaces"
            ),
            evidence_refs=[v56a_evidence_path, v56b_evidence_path],
        ),
    ]
    return AgenticDeGovernanceCalibrationRegister(
        target_arc=V56C_TARGET_ARC,
        target_path=V56C_TARGET_PATH,
        baseline_checker_version=V56B_CHECKER_VERSION,
        entry_count=len(entries),
        entries=entries,
    )


def _build_v56c_migration_decision_register(
    *,
    v56a_evidence_path: str,
    v56b_evidence_path: str,
    v56b_lane_drift_path: str,
    v56b_conformance_path: str,
) -> AgenticDeMigrationDecisionRegister:
    entries = [
        _migration_entry(
            surface_id="checkpoint_semantics",
            current_posture="reused_from_shipped_v56a_v56b_without_live_mutation",
            recommended_outcome="keep_warning_only",
            rationale=(
                "V56-C is advisory-only, so checkpoint semantics stay unchanged until a later "
                "explicit lock selects stronger local hardening"
            ),
            evidence_refs=[v56a_evidence_path, v56b_evidence_path],
        ),
        _migration_entry(
            surface_id="ticket_issuance_behavior",
            current_posture="accepted_necessary_but_not_sufficient_with_bounded_local_ticket_scope",
            recommended_outcome="keep_warning_only",
            rationale=(
                "the shipped live gate remains intentionally narrow and should not widen "
                "inside an advisory harvest/calibration slice"
            ),
            evidence_refs=[v56b_lane_drift_path, v56b_evidence_path],
        ),
        _migration_entry(
            surface_id="selected_live_action_classes",
            current_posture="local_reversible_execute_and_local_write_only",
            recommended_outcome="keep_warning_only",
            rationale=(
                "the selected live subset is frozen for V56-C and any widening requires a "
                "later lock rather than a calibration-side reinterpretation"
            ),
            evidence_refs=[v56b_lane_drift_path, v56b_evidence_path],
        ),
        _migration_entry(
            surface_id="selected_live_action_class_interpretation",
            current_posture="frozen_local_scope_reversible_scope_and_local_write_exclusions",
            recommended_outcome="keep_warning_only",
            rationale=(
                "V56-C may assess the shipped live classes but may not repartition or "
                "reinterpret their operative meaning in a way that changes live behavior by default"
            ),
            evidence_refs=[v56b_evidence_path],
        ),
        _migration_entry(
            surface_id="local_write_post_effect_observation_path",
            current_posture="ticket_visible_but_reference_conformance_still_reports_no_live_effect",
            recommended_outcome="candidate_for_later_local_hardening",
            rationale=(
                "if a later lane captures an actually observed bounded local effect under the "
                "same frozen local_write semantics, that path could become a narrow "
                "hardening candidate"
            ),
            evidence_refs=[v56b_conformance_path, v56b_evidence_path],
        ),
        _migration_entry(
            surface_id="stronger_execute_and_dispatch_rollout",
            current_posture="still_deferred_outside_v56b_selected_local_subset",
            recommended_outcome="not_selected_for_escalation",
            rationale=(
                "stronger execute and delegated or external dispatch remain outside the shipped "
                "live subset and are not selected for escalation in V56-C"
            ),
            evidence_refs=[v56b_evidence_path],
        ),
    ]
    return AgenticDeMigrationDecisionRegister(
        target_arc=V56C_TARGET_ARC,
        target_path=V56C_TARGET_PATH,
        baseline_checker_version=V56B_CHECKER_VERSION,
        entry_count=len(entries),
        entries=entries,
    )


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


def run_agentic_de_interaction_v56c(
    *,
    repo_root_path: Path | None = None,
    domain_packet_path: Path = DEFAULT_DOMAIN_PACKET_PATH,
    morph_ir_path: Path = DEFAULT_MORPH_IR_PATH,
    interaction_contract_path: Path = DEFAULT_INTERACTION_CONTRACT_PATH,
    action_proposal_path: Path = DEFAULT_ACTION_PROPOSAL_PATH,
    v56a_checkpoint_path: Path = DEFAULT_V56A_CHECKPOINT_PATH,
    v56a_diagnostics_path: Path = DEFAULT_V56A_DIAGNOSTICS_PATH,
    v56a_conformance_path: Path = DEFAULT_V56A_CONFORMANCE_PATH,
    v56b_lane_drift_path: Path = DEFAULT_V56B_LANE_DRIFT_PATH,
    v56b_action_class_taxonomy_path: Path = DEFAULT_V56B_ACTION_CLASS_TAXONOMY_PATH,
    v56b_runtime_state_path: Path = DEFAULT_V56B_RUNTIME_STATE_PATH,
    v56b_action_ticket_path: Path = DEFAULT_V56B_TICKET_PATH,
    v56b_diagnostics_path: Path = DEFAULT_V56B_DIAGNOSTICS_PATH,
    v56b_conformance_path: Path = DEFAULT_V56B_CONFORMANCE_PATH,
    lane_drift_path: Path = DEFAULT_V56C_LANE_DRIFT_PATH,
    v56a_evidence_path: Path = DEFAULT_V56C_V56A_EVIDENCE_PATH,
    v56b_evidence_path: Path = DEFAULT_V56C_V56B_EVIDENCE_PATH,
) -> tuple[
    AgenticDeRuntimeHarvestRecord,
    AgenticDeGovernanceCalibrationRegister,
    AgenticDeMigrationDecisionRegister,
]:
    if repo_root_path is None:
        root = repo_root(anchor=Path(__file__)).resolve()
    else:
        root = repo_root_path.resolve()

    domain_packet_path = _resolve_path(repo_root_path=root, path=domain_packet_path)
    morph_ir_path = _resolve_path(repo_root_path=root, path=morph_ir_path)
    interaction_contract_path = _resolve_path(repo_root_path=root, path=interaction_contract_path)
    action_proposal_path = _resolve_path(repo_root_path=root, path=action_proposal_path)
    v56a_checkpoint_path = _resolve_path(repo_root_path=root, path=v56a_checkpoint_path)
    v56a_diagnostics_path = _resolve_path(repo_root_path=root, path=v56a_diagnostics_path)
    v56a_conformance_path = _resolve_path(repo_root_path=root, path=v56a_conformance_path)
    v56b_lane_drift_path = _resolve_path(repo_root_path=root, path=v56b_lane_drift_path)
    v56b_action_class_taxonomy_path = _resolve_path(
        repo_root_path=root, path=v56b_action_class_taxonomy_path
    )
    v56b_runtime_state_path = _resolve_path(repo_root_path=root, path=v56b_runtime_state_path)
    v56b_action_ticket_path = _resolve_path(repo_root_path=root, path=v56b_action_ticket_path)
    v56b_diagnostics_path = _resolve_path(repo_root_path=root, path=v56b_diagnostics_path)
    v56b_conformance_path = _resolve_path(repo_root_path=root, path=v56b_conformance_path)
    lane_drift_path = _resolve_path(repo_root_path=root, path=lane_drift_path)
    v56a_evidence_path = _resolve_path(repo_root_path=root, path=v56a_evidence_path)
    v56b_evidence_path = _resolve_path(repo_root_path=root, path=v56b_evidence_path)

    _validate_v56c_lane_drift_record(load_lane_drift_record(lane_drift_path))
    _validate_v56b_lane_drift_record(load_lane_drift_record(v56b_lane_drift_path))
    _validate_v56a_evidence_payload(
        _load_json_object(v56a_evidence_path, error_label="V56-A evidence")
    )
    _validate_v56b_evidence_payload(
        _load_json_object(v56b_evidence_path, error_label="V56-B evidence")
    )

    domain_packet = load_domain_packet(domain_packet_path)
    morph_ir = load_morph_ir(morph_ir_path)
    contract = load_interaction_contract(interaction_contract_path)
    proposal = load_action_proposal(action_proposal_path)
    v56a_checkpoint = load_membrane_checkpoint(v56a_checkpoint_path)
    v56a_diagnostics = load_morph_diagnostics(v56a_diagnostics_path)
    v56a_conformance = load_conformance_report(v56a_conformance_path)
    v56b_taxonomy = load_action_class_taxonomy(v56b_action_class_taxonomy_path)
    v56b_runtime_state = load_runtime_state(v56b_runtime_state_path)
    v56b_ticket = load_action_ticket(v56b_action_ticket_path)
    v56b_diagnostics = load_morph_diagnostics(v56b_diagnostics_path)
    v56b_conformance = load_conformance_report(v56b_conformance_path)

    _validate_v56a_reference_surfaces(
        domain_packet=domain_packet,
        morph_ir=morph_ir,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        diagnostics=v56a_diagnostics,
        conformance=v56a_conformance,
    )
    _validate_v56b_reference_surfaces(
        domain_packet=domain_packet,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        taxonomy=v56b_taxonomy,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        diagnostics=v56b_diagnostics,
        conformance=v56b_conformance,
    )
    if v56b_conformance.delta_notes[:3] != v56a_conformance.delta_notes:
        raise ValueError("V56-B conformance must preserve the shipped V56-A typed delta base")
    if v56b_conformance.executed_or_observed_effect != v56a_conformance.executed_or_observed_effect:
        raise ValueError("V56-C requires the shipped no_live_effect conformance axis")
    if v56b_conformance.live_effect_present != v56a_conformance.live_effect_present:
        raise ValueError("V56-C requires the shipped V56-A/V56-B no-live-effect continuity")

    v56a_evidence_ref = _render_input_ref(repo_root_path=root, path=v56a_evidence_path)
    v56b_evidence_ref = _render_input_ref(repo_root_path=root, path=v56b_evidence_path)
    v56b_lane_drift_ref = _render_input_ref(repo_root_path=root, path=v56b_lane_drift_path)
    v56b_ticket_ref = _render_input_ref(repo_root_path=root, path=v56b_action_ticket_path)
    v56b_conformance_ref = _render_input_ref(repo_root_path=root, path=v56b_conformance_path)

    harvest = _build_v56c_runtime_harvest_record(
        packet=domain_packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        diagnostics=v56b_diagnostics,
        conformance=v56b_conformance,
        evidence_refs=[
            _render_input_ref(repo_root_path=root, path=domain_packet_path),
            _render_input_ref(repo_root_path=root, path=morph_ir_path),
            _render_input_ref(repo_root_path=root, path=interaction_contract_path),
            _render_input_ref(repo_root_path=root, path=action_proposal_path),
            _render_input_ref(repo_root_path=root, path=v56a_checkpoint_path),
            _render_input_ref(repo_root_path=root, path=v56a_diagnostics_path),
            _render_input_ref(repo_root_path=root, path=v56a_conformance_path),
            _render_input_ref(repo_root_path=root, path=v56b_action_class_taxonomy_path),
            _render_input_ref(repo_root_path=root, path=v56b_runtime_state_path),
            v56b_ticket_ref,
            v56b_lane_drift_ref,
            _render_input_ref(repo_root_path=root, path=v56b_diagnostics_path),
            v56b_conformance_ref,
            v56a_evidence_ref,
            v56b_evidence_ref,
        ],
    )
    governance = _build_v56c_governance_calibration_register(
        v56b_evidence_path=v56b_evidence_ref,
        v56b_lane_drift_path=v56b_lane_drift_ref,
        v56b_ticket_path=v56b_ticket_ref,
        v56b_conformance_path=v56b_conformance_ref,
        v56a_evidence_path=v56a_evidence_ref,
    )
    migration = _build_v56c_migration_decision_register(
        v56a_evidence_path=v56a_evidence_ref,
        v56b_evidence_path=v56b_evidence_ref,
        v56b_lane_drift_path=v56b_lane_drift_ref,
        v56b_conformance_path=v56b_conformance_ref,
    )
    return harvest, governance, migration


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


def render_runtime_harvest_record_payload(harvest: AgenticDeRuntimeHarvestRecord) -> str:
    return json.dumps(harvest.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_governance_calibration_register_payload(
    register: AgenticDeGovernanceCalibrationRegister,
) -> str:
    return json.dumps(register.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_migration_decision_register_payload(
    register: AgenticDeMigrationDecisionRegister,
) -> str:
    return json.dumps(register.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"
