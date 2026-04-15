from __future__ import annotations

import hashlib
import json
from pathlib import Path

from adeu_ir.repo import repo_root
from urm_runtime.models import CopilotTurnSnapshot

from .local_effect import (
    DEFAULT_LOCAL_EFFECT_PAYLOAD_SHA256,
    DEFAULT_LOCAL_EFFECT_PAYLOAD_TEXT,
    DEFAULT_LOCAL_EFFECT_TARGET_RELATIVE_PATH,
    DESIGNATED_LOCAL_EFFECT_SANDBOX_ROOT,
    observe_local_write_effect,
    observe_local_write_restoration_effect,
)
from .local_effect_conformance import build_local_effect_conformance_report
from .models import (
    AGENTIC_DE_ACTION_CLASS_TAXONOMY_SCHEMA,
    AGENTIC_DE_ACTION_PROPOSAL_SCHEMA,
    AGENTIC_DE_ACTION_TICKET_SCHEMA,
    AGENTIC_DE_CONFORMANCE_REPORT_SCHEMA,
    AGENTIC_DE_CONTINUATION_DECISION_RECORD_SCHEMA,
    AGENTIC_DE_DOMAIN_PACKET_SCHEMA,
    AGENTIC_DE_GOVERNANCE_CALIBRATION_REGISTER_SCHEMA,
    AGENTIC_DE_INTERACTION_CONTRACT_SCHEMA,
    AGENTIC_DE_LANE_DRIFT_RECORD_SCHEMA,
    AGENTIC_DE_LIVE_HARNESS_HARDENING_REGISTER_SCHEMA,
    AGENTIC_DE_LIVE_RESTORATION_HANDOFF_RECORD_SCHEMA,
    AGENTIC_DE_LIVE_RESTORATION_REINTEGRATION_REPORT_SCHEMA,
    AGENTIC_DE_LIVE_TURN_ADMISSION_RECORD_SCHEMA,
    AGENTIC_DE_LIVE_TURN_HANDOFF_RECORD_SCHEMA,
    AGENTIC_DE_LIVE_TURN_REINTEGRATION_REPORT_SCHEMA,
    AGENTIC_DE_LOCAL_EFFECT_CONFORMANCE_REPORT_SCHEMA,
    AGENTIC_DE_LOCAL_EFFECT_HARDENING_REGISTER_SCHEMA,
    AGENTIC_DE_LOCAL_EFFECT_OBSERVATION_RECORD_SCHEMA,
    AGENTIC_DE_LOCAL_EFFECT_RESTORATION_RECORD_SCHEMA,
    AGENTIC_DE_LOOP_STATE_LEDGER_SCHEMA,
    AGENTIC_DE_MEMBRANE_CHECKPOINT_SCHEMA,
    AGENTIC_DE_MIGRATION_DECISION_REGISTER_SCHEMA,
    AGENTIC_DE_MORPH_DIAGNOSTICS_SCHEMA,
    AGENTIC_DE_MORPH_IR_SCHEMA,
    AGENTIC_DE_RUNTIME_HARVEST_RECORD_SCHEMA,
    AGENTIC_DE_RUNTIME_STATE_SCHEMA,
    AGENTIC_DE_SEED_INTENT_RECORD_SCHEMA,
    AGENTIC_DE_TASK_CHARTER_PACKET_SCHEMA,
    AGENTIC_DE_TASK_RESIDUAL_PACKET_SCHEMA,
    AGENTIC_DE_WORKSPACE_CONTINUITY_ADMISSION_RECORD_SCHEMA,
    AGENTIC_DE_WORKSPACE_CONTINUITY_HARDENING_REGISTER_SCHEMA,
    AGENTIC_DE_WORKSPACE_CONTINUITY_REGION_DECLARATION_SCHEMA,
    AGENTIC_DE_WORKSPACE_CONTINUITY_REINTEGRATION_REPORT_SCHEMA,
    AGENTIC_DE_WORKSPACE_CONTINUITY_RESTORATION_HANDOFF_RECORD_SCHEMA,
    AGENTIC_DE_WORKSPACE_CONTINUITY_RESTORATION_REINTEGRATION_REPORT_SCHEMA,
    AGENTIC_DE_WORKSPACE_OCCUPANCY_REPORT_SCHEMA,
    AgenticDeActionClassTaxonomy,
    AgenticDeActionClassTaxonomyEntry,
    AgenticDeActionProposal,
    AgenticDeActionTicket,
    AgenticDeConformanceReport,
    AgenticDeContinuationDecisionRecord,
    AgenticDeDomainPacket,
    AgenticDeGovernanceCalibrationEntry,
    AgenticDeGovernanceCalibrationRegister,
    AgenticDeInteractionContract,
    AgenticDeInteractionContractEntry,
    AgenticDeLaneDriftRecord,
    AgenticDeLiveHarnessHardeningEntry,
    AgenticDeLiveHarnessHardeningRegister,
    AgenticDeLiveRestorationHandoffRecord,
    AgenticDeLiveRestorationReintegrationReport,
    AgenticDeLiveTurnAdmissionRecord,
    AgenticDeLiveTurnHandoffRecord,
    AgenticDeLiveTurnReintegrationReport,
    AgenticDeLocalEffectConformanceReport,
    AgenticDeLocalEffectHardeningEntry,
    AgenticDeLocalEffectHardeningRegister,
    AgenticDeLocalEffectObservationRecord,
    AgenticDeLocalEffectRestorationRecord,
    AgenticDeLoopStateLedger,
    AgenticDeMembraneCheckpoint,
    AgenticDeMigrationDecisionEntry,
    AgenticDeMigrationDecisionRegister,
    AgenticDeMorphDiagnosticFinding,
    AgenticDeMorphDiagnostics,
    AgenticDeMorphIr,
    AgenticDeRuntimeHarvestRecord,
    AgenticDeRuntimeState,
    AgenticDeSeedIntentRecord,
    AgenticDeTaskCharterPacket,
    AgenticDeTaskResidualPacket,
    AgenticDeWorkspaceContinuityAdmissionRecord,
    AgenticDeWorkspaceContinuityHardeningEntry,
    AgenticDeWorkspaceContinuityHardeningRegister,
    AgenticDeWorkspaceContinuityRegionDeclaration,
    AgenticDeWorkspaceContinuityReintegrationReport,
    AgenticDeWorkspaceContinuityRestorationHandoffRecord,
    AgenticDeWorkspaceContinuityRestorationReintegrationReport,
    AgenticDeWorkspaceOccupancyReport,
)
from .workspace_continuity import (
    DEFAULT_WORKSPACE_CONTINUITY_PAYLOAD_TEXT,
    DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH,
    DESIGNATED_WORKSPACE_CONTINUITY_ROOT,
    WorkspaceOccupancyAssessment,
    classify_workspace_occupancy,
    observe_workspace_continuity_create_new_effect,
    observe_workspace_continuity_create_new_restoration_effect,
    snapshot_workspace_continuity_state,
    write_workspace_governed_lineage_marker,
)

CHECKER_VERSION = "agentic_de_interaction_v56a"
V56A_CHECKER_VERSION = CHECKER_VERSION
V56B_CHECKER_VERSION = "agentic_de_interaction_v56b"
V56C_CHECKER_VERSION = "agentic_de_interaction_v56c"
V56C_TARGET_ARC = "vNext+154"
V56C_TARGET_PATH = "V56-C"
V57A_CHECKER_VERSION = "agentic_de_local_effect_v57a"
V57A_TARGET_ARC = "vNext+155"
V57A_TARGET_PATH = "V57-A"
V57B_CHECKER_VERSION = "agentic_de_local_effect_v57b"
V57B_TARGET_ARC = "vNext+156"
V57B_TARGET_PATH = "V57-B"
V57C_CHECKER_VERSION = "agentic_de_local_effect_v57c"
V57C_TARGET_ARC = "vNext+157"
V57C_TARGET_PATH = "V57-C"
V58A_CHECKER_VERSION = "agentic_de_live_harness_v58a"
V58A_TARGET_ARC = "vNext+158"
V58A_TARGET_PATH = "V58-A"
V58B_CHECKER_VERSION = "agentic_de_live_harness_v58b"
V58B_TARGET_ARC = "vNext+159"
V58B_TARGET_PATH = "V58-B"
V58C_CHECKER_VERSION = "agentic_de_live_harness_v58c"
V58C_TARGET_ARC = "vNext+160"
V58C_TARGET_PATH = "V58-C"
V59A_CHECKER_VERSION = "agentic_de_workspace_continuity_v59a"
V59A_TARGET_ARC = "vNext+161"
V59A_TARGET_PATH = "V59-A"
V59B_CHECKER_VERSION = "agentic_de_workspace_continuity_v59b"
V59B_TARGET_ARC = "vNext+162"
V59B_TARGET_PATH = "V59-B"
V59B_SELECTED_RESTORATION_SCOPE = (
    "bounded continuity-safe remove-create_new restore over the declared "
    "continuity root and selected target only"
)
V59B_RESTORATION_EXEMPLAR = "compensating_restore_of_v57a_create_new_artifact_only"
V59B_REPLAY_MODE = (
    "bounded_recomputation_and_re_evaluation_of_the_restoration_event_against_"
    "prior_observed_effect_lineage_only"
)
V59B_RESTORATION_ENTITLEMENT_MODE = (
    "lineage_bound_evidence_bound_bounded_compensating_scope_derivation_only"
)
V59C_CHECKER_VERSION = "agentic_de_workspace_continuity_v59c"
V59C_TARGET_ARC = "vNext+163"
V59C_TARGET_PATH = "V59-C"
V60A_CHECKER_VERSION = "agentic_de_continuation_v60a"
V60A_TARGET_ARC = "vNext+164"
V60A_TARGET_PATH = "V60-A"
V60A_FROZEN_POLICY_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS164.md#machine-checkable-contract"


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
DEFAULT_V56C_RUNTIME_HARVEST_PATH = _default_fixture_path(
    "v56c", "reference_agentic_de_runtime_harvest_record.json"
)
DEFAULT_V56C_GOVERNANCE_CALIBRATION_PATH = _default_fixture_path(
    "v56c", "reference_agentic_de_governance_calibration_register.json"
)
DEFAULT_V56C_MIGRATION_DECISION_PATH = _default_fixture_path(
    "v56c", "reference_agentic_de_migration_decision_register.json"
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
DEFAULT_V57A_LANE_DRIFT_PATH = _default_fixture_path(
    "v57a", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V57A_OBSERVATION_PATH = _default_fixture_path(
    "v57a", "reference_agentic_de_local_effect_observation_record.json"
)
DEFAULT_V57A_LOCAL_EFFECT_CONFORMANCE_PATH = _default_fixture_path(
    "v57a", "reference_agentic_de_local_effect_conformance_report.json"
)
DEFAULT_V57A_V56C_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v154"
    / "evidence_inputs"
    / "v56c_harvest_calibration_migration_evidence_v154.json"
)
DEFAULT_V57B_LANE_DRIFT_PATH = _default_fixture_path(
    "v57b", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V57B_RESTORATION_PATH = _default_fixture_path(
    "v57b", "reference_agentic_de_local_effect_restoration_record.json"
)
DEFAULT_V57A_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v155"
    / "evidence_inputs"
    / "v57a_local_effect_observation_evidence_v155.json"
)
DEFAULT_V57C_LANE_DRIFT_PATH = _default_fixture_path(
    "v57c", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V57C_HARDENING_PATH = _default_fixture_path(
    "v57c", "reference_agentic_de_local_effect_hardening_register.json"
)
DEFAULT_V57B_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v156"
    / "evidence_inputs"
    / "v57b_local_effect_restoration_evidence_v156.json"
)
DEFAULT_V57C_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v157"
    / "evidence_inputs"
    / "v57c_local_effect_hardening_evidence_v157.json"
)
DEFAULT_V58A_LANE_DRIFT_PATH = _default_fixture_path(
    "v58a", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V58A_LIVE_TURN_ADMISSION_PATH = _default_fixture_path(
    "v58a", "reference_agentic_de_live_turn_admission_record.json"
)
DEFAULT_V58A_LIVE_TURN_HANDOFF_PATH = _default_fixture_path(
    "v58a", "reference_agentic_de_live_turn_handoff_record.json"
)
DEFAULT_V58A_LIVE_TURN_REINTEGRATION_PATH = _default_fixture_path(
    "v58a", "reference_agentic_de_live_turn_reintegration_report.json"
)
DEFAULT_V58B_LANE_DRIFT_PATH = _default_fixture_path(
    "v58b", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V58B_LIVE_RESTORATION_HANDOFF_PATH = _default_fixture_path(
    "v58b", "reference_agentic_de_live_restoration_handoff_record.json"
)
DEFAULT_V58B_LIVE_RESTORATION_REINTEGRATION_PATH = _default_fixture_path(
    "v58b", "reference_agentic_de_live_restoration_reintegration_report.json"
)
DEFAULT_V58A_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v158"
    / "evidence_inputs"
    / "v58a_live_harness_bind_evidence_v158.json"
)
DEFAULT_V58C_LANE_DRIFT_PATH = _default_fixture_path(
    "v58c", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V58C_HARDENING_PATH = _default_fixture_path(
    "v58c", "reference_agentic_de_live_harness_hardening_register.json"
)
DEFAULT_V58B_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v159"
    / "evidence_inputs"
    / "v58b_live_restoration_state_evidence_v159.json"
)
DEFAULT_V59A_LANE_DRIFT_PATH = _default_fixture_path(
    "v59a", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V59A_CONTINUITY_REGION_DECLARATION_PATH = _default_fixture_path(
    "v59a", "reference_agentic_de_workspace_continuity_region_declaration.json"
)
DEFAULT_V59A_CONTINUITY_ADMISSION_PATH = _default_fixture_path(
    "v59a", "reference_agentic_de_workspace_continuity_admission_record.json"
)
DEFAULT_V59A_OCCUPANCY_REPORT_PATH = _default_fixture_path(
    "v59a", "reference_agentic_de_workspace_occupancy_report.json"
)
DEFAULT_V59A_LIVE_TURN_ADMISSION_PATH = _default_fixture_path(
    "v59a", "reference_agentic_de_live_turn_admission_record.json"
)
DEFAULT_V59A_LIVE_TURN_HANDOFF_PATH = _default_fixture_path(
    "v59a", "reference_agentic_de_live_turn_handoff_record.json"
)
DEFAULT_V59A_OBSERVATION_PATH = _default_fixture_path(
    "v59a", "reference_agentic_de_local_effect_observation_record.json"
)
DEFAULT_V59A_LOCAL_EFFECT_CONFORMANCE_PATH = _default_fixture_path(
    "v59a", "reference_agentic_de_local_effect_conformance_report.json"
)
DEFAULT_V59A_LIVE_TURN_REINTEGRATION_PATH = _default_fixture_path(
    "v59a", "reference_agentic_de_live_turn_reintegration_report.json"
)
DEFAULT_V59A_CONTINUITY_REINTEGRATION_PATH = _default_fixture_path(
    "v59a", "reference_agentic_de_workspace_continuity_reintegration_report.json"
)
DEFAULT_V59B_LANE_DRIFT_PATH = _default_fixture_path(
    "v59b", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V59B_CONTINUITY_RESTORATION_HANDOFF_PATH = _default_fixture_path(
    "v59b", "reference_agentic_de_workspace_continuity_restoration_handoff_record.json"
)
DEFAULT_V59B_RESTORATION_PATH = _default_fixture_path(
    "v59b", "reference_agentic_de_local_effect_restoration_record.json"
)
DEFAULT_V59B_CONTINUITY_RESTORATION_REINTEGRATION_PATH = _default_fixture_path(
    "v59b", "reference_agentic_de_workspace_continuity_restoration_reintegration_report.json"
)
DEFAULT_V59C_LANE_DRIFT_PATH = _default_fixture_path(
    "v59c", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V59C_HARDENING_PATH = _default_fixture_path(
    "v59c", "reference_agentic_de_workspace_continuity_hardening_register.json"
)
DEFAULT_V60A_LANE_DRIFT_PATH = _default_fixture_path(
    "v60a", "reference_agentic_de_lane_drift_record.json"
)
DEFAULT_V60A_SEED_INTENT_PATH = _default_fixture_path(
    "v60a", "reference_agentic_de_seed_intent_record.json"
)
DEFAULT_V60A_TASK_CHARTER_PATH = _default_fixture_path(
    "v60a", "reference_agentic_de_task_charter_packet.json"
)
DEFAULT_V60A_TASK_RESIDUAL_PATH = _default_fixture_path(
    "v60a", "reference_agentic_de_task_residual_packet.json"
)
DEFAULT_V60A_LOOP_STATE_LEDGER_PATH = _default_fixture_path(
    "v60a", "reference_agentic_de_loop_state_ledger.json"
)
DEFAULT_V60A_CONTINUATION_DECISION_PATH = _default_fixture_path(
    "v60a", "reference_agentic_de_continuation_decision_record.json"
)
DEFAULT_V58C_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v160"
    / "evidence_inputs"
    / "v58c_live_harness_hardening_evidence_v160.json"
)
DEFAULT_V59A_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v161"
    / "evidence_inputs"
    / "v59a_workspace_continuity_starter_evidence_v161.json"
)
DEFAULT_V59B_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v162"
    / "evidence_inputs"
    / "v59b_workspace_continuity_restoration_evidence_v162.json"
)
DEFAULT_V59C_EVIDENCE_PATH = (
    repo_root(anchor=Path(__file__))
    / "artifacts"
    / "agent_harness"
    / "v163"
    / "evidence_inputs"
    / "v59c_workspace_continuity_hardening_evidence_v163.json"
)

EXPECTED_V56A_EVIDENCE_SCHEMA = "v56a_agentic_de_interaction_governance_starter_evidence@1"
EXPECTED_V56B_EVIDENCE_SCHEMA = "v56b_bounded_live_gate_starter_evidence@1"
EXPECTED_V56C_EVIDENCE_SCHEMA = "v56c_harvest_calibration_migration_evidence@1"
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
EXPECTED_V57A_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS154.md"
REQUIRED_V57A_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v56_surface_reuse_default": "holds",
    "local_write_only_actual_effect": "amended",
    "selected_local_write_subset_create_new_append_only": "amended",
    "designated_sandbox_only": "amended",
    "effect_observation_outputs_evidence_only": "amended",
}
EXPECTED_V57A_EVIDENCE_SCHEMA = "v57a_local_effect_observation_evidence@1"
EXPECTED_V57B_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS155.md"
REQUIRED_V57B_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v57a_surface_reuse_default": "holds",
    "restoration_exemplar_create_new_only": "amended",
    "replay_mode_bounded_recomputation_only": "amended",
    "restoration_entitlement_derived_not_ambient": "amended",
    "restoration_outputs_evidence_only": "amended",
}
EXPECTED_V57B_EVIDENCE_SCHEMA = "v57b_local_effect_restoration_evidence@1"
EXPECTED_V57C_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS156.md"
REQUIRED_V57C_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v57b_surface_reuse_default": "holds",
    "hardening_target_create_new_only": "amended",
    "exemplar_evidence_non_generalizing": "amended",
    "hardening_outputs_advisory_only": "amended",
    "committed_lane_artifacts_outrank_narrative_docs": "amended",
}
EXPECTED_V57C_EVIDENCE_SCHEMA = "v57c_local_effect_hardening_evidence@1"
EXPECTED_V58A_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS157.md"
REQUIRED_V58A_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v57_surface_reuse_default": "holds",
    "current_turn_admission_required": "amended",
    "outer_harness_capability_not_inner_entitlement": "amended",
    "ticket_to_effect_handoff_required": "amended",
    "positive_reintegration_requires_declared_current_turn_witness": "amended",
    "observability_echo_dedup_required": "amended",
}
EXPECTED_V58A_EVIDENCE_SCHEMA = "v58a_live_harness_bind_evidence@1"
EXPECTED_V58B_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS158.md"
REQUIRED_V58B_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v58a_surface_reuse_default": "holds",
    "restoration_state_explicit_not_hidden_cleanup": "amended",
    "restoration_time_admission_resnapshot_required": "amended",
    "historical_lineage_refs_non_entitling": "amended",
    "replay_law_proof_embedded_in_reintegration_report": "amended",
}
EXPECTED_V58B_EVIDENCE_SCHEMA = "v58b_live_restoration_state_evidence@1"
EXPECTED_V58C_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS159.md"
REQUIRED_V58C_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v58b_surface_reuse_default": "holds",
    "hardening_target_create_new_only": "amended",
    "hardening_outputs_advisory_only": "amended",
    "committed_lane_artifacts_outrank_narrative_docs": "amended",
    "hardening_recommendation_extensional_and_replayable": "amended",
    "lineage_root_non_independence_dedup_required": "amended",
}
EXPECTED_V58C_EVIDENCE_SCHEMA = "v58c_live_harness_hardening_evidence@1"
EXPECTED_V59A_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS160.md"
REQUIRED_V59A_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v58_surface_reuse_default": "holds",
    "continuity_admission_additional_gate": "amended",
    "prior_workspace_state_context_not_authority": "amended",
    "create_new_requires_unoccupied_target": "amended",
    "non_target_occupants_contextual_only": "amended",
    "positive_continuity_reintegration_requires_witness_basis": "amended",
}
EXPECTED_V59A_EVIDENCE_SCHEMA = "v59a_workspace_continuity_starter_evidence@1"
EXPECTED_V59B_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS161.md"
REQUIRED_V59B_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v59a_surface_reuse_default": "holds",
    "continuity_safe_restoration_explicit_not_hidden_cleanup": "amended",
    "restoration_time_continuation_resnapshot_required": "amended",
    "historical_lineage_refs_non_entitling": "amended",
    "baseline_match_and_replay_law_proof_required": "amended",
}
EXPECTED_V59B_EVIDENCE_SCHEMA = "v59b_workspace_continuity_restoration_evidence@1"
EXPECTED_V59C_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS162.md"
REQUIRED_V59C_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v59a_v59b_surface_reuse_default": "holds",
    "path_level_only_not_family_migration": "amended",
    "hardening_recommendation_extensional_and_replayable": "amended",
    "explicit_frozen_policy_anchor_required": "amended",
    "restoration_freshness_and_baseline_verdicts_carried_forward": "amended",
    "lineage_root_non_independence_dedup_required": "amended",
}
EXPECTED_V59C_EVIDENCE_SCHEMA = "v59c_workspace_continuity_hardening_evidence@1"
EXPECTED_V60A_PRIOR_LANE_REF = "docs/LOCKED_CONTINUATION_vNEXT_PLUS163.md"
REQUIRED_V60A_DRIFT_ENTRY_STATUSES: dict[str, str] = {
    "v59_surface_reuse_default": "holds",
    "typed_seed_ingress_non_chat_native": "amended",
    "task_charter_compilation_extensional_and_replayable": "amended",
    "task_residual_derived_not_authorizing": "amended",
    "continue_to_governed_act_exact_path_only": "amended",
    "emit_governed_communication_posture_only": "amended",
    "single_step_local_ticket_duration_preserved": "amended",
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


def load_live_turn_admission_record(path: Path) -> AgenticDeLiveTurnAdmissionRecord:
    payload = AgenticDeLiveTurnAdmissionRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_LIVE_TURN_ADMISSION_RECORD_SCHEMA:
        raise ValueError(
            "unexpected schema marker for live-turn admission record: "
            f"{payload.schema}"
        )
    return payload


def load_live_turn_handoff_record(path: Path) -> AgenticDeLiveTurnHandoffRecord:
    payload = AgenticDeLiveTurnHandoffRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_LIVE_TURN_HANDOFF_RECORD_SCHEMA:
        raise ValueError(
            "unexpected schema marker for live-turn handoff record: "
            f"{payload.schema}"
        )
    return payload


def load_live_turn_reintegration_report(path: Path) -> AgenticDeLiveTurnReintegrationReport:
    payload = AgenticDeLiveTurnReintegrationReport.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_LIVE_TURN_REINTEGRATION_REPORT_SCHEMA:
        raise ValueError(
            "unexpected schema marker for live-turn reintegration report: "
            f"{payload.schema}"
        )
    return payload


def load_workspace_continuity_region_declaration(
    path: Path,
) -> AgenticDeWorkspaceContinuityRegionDeclaration:
    payload = AgenticDeWorkspaceContinuityRegionDeclaration.model_validate(
        _read_json_object(path)
    )
    if payload.schema != AGENTIC_DE_WORKSPACE_CONTINUITY_REGION_DECLARATION_SCHEMA:
        raise ValueError(
            "unexpected schema marker for workspace continuity region declaration: "
            f"{payload.schema}"
        )
    return payload


def load_workspace_continuity_admission_record(
    path: Path,
) -> AgenticDeWorkspaceContinuityAdmissionRecord:
    payload = AgenticDeWorkspaceContinuityAdmissionRecord.model_validate(
        _read_json_object(path)
    )
    if payload.schema != AGENTIC_DE_WORKSPACE_CONTINUITY_ADMISSION_RECORD_SCHEMA:
        raise ValueError(
            "unexpected schema marker for workspace continuity admission record: "
            f"{payload.schema}"
        )
    return payload


def load_workspace_occupancy_report(path: Path) -> AgenticDeWorkspaceOccupancyReport:
    payload = AgenticDeWorkspaceOccupancyReport.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_WORKSPACE_OCCUPANCY_REPORT_SCHEMA:
        raise ValueError(
            "unexpected schema marker for workspace occupancy report: "
            f"{payload.schema}"
        )
    return payload


def load_workspace_continuity_reintegration_report(
    path: Path,
) -> AgenticDeWorkspaceContinuityReintegrationReport:
    payload = AgenticDeWorkspaceContinuityReintegrationReport.model_validate(
        _read_json_object(path)
    )
    if payload.schema != AGENTIC_DE_WORKSPACE_CONTINUITY_REINTEGRATION_REPORT_SCHEMA:
        raise ValueError(
            "unexpected schema marker for workspace continuity reintegration report: "
            f"{payload.schema}"
        )
    return payload


def load_workspace_continuity_restoration_handoff_record(
    path: Path,
) -> AgenticDeWorkspaceContinuityRestorationHandoffRecord:
    payload = AgenticDeWorkspaceContinuityRestorationHandoffRecord.model_validate(
        _read_json_object(path)
    )
    if payload.schema != AGENTIC_DE_WORKSPACE_CONTINUITY_RESTORATION_HANDOFF_RECORD_SCHEMA:
        raise ValueError(
            "unexpected schema marker for workspace continuity restoration handoff record: "
            f"{payload.schema}"
        )
    return payload


def load_workspace_continuity_restoration_reintegration_report(
    path: Path,
) -> AgenticDeWorkspaceContinuityRestorationReintegrationReport:
    payload = AgenticDeWorkspaceContinuityRestorationReintegrationReport.model_validate(
        _read_json_object(path)
    )
    if (
        payload.schema
        != AGENTIC_DE_WORKSPACE_CONTINUITY_RESTORATION_REINTEGRATION_REPORT_SCHEMA
    ):
        raise ValueError(
            "unexpected schema marker for workspace continuity restoration reintegration "
            f"report: {payload.schema}"
        )
    return payload


def load_workspace_continuity_hardening_register(
    path: Path,
) -> AgenticDeWorkspaceContinuityHardeningRegister:
    payload = AgenticDeWorkspaceContinuityHardeningRegister.model_validate(
        _read_json_object(path)
    )
    if payload.schema != AGENTIC_DE_WORKSPACE_CONTINUITY_HARDENING_REGISTER_SCHEMA:
        raise ValueError(
            "unexpected schema marker for workspace continuity hardening register: "
            f"{payload.schema}"
        )
    return payload


def load_seed_intent_record(path: Path) -> AgenticDeSeedIntentRecord:
    payload = AgenticDeSeedIntentRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_SEED_INTENT_RECORD_SCHEMA:
        raise ValueError(f"unexpected schema marker for seed intent record: {payload.schema}")
    return payload


def load_task_charter_packet(path: Path) -> AgenticDeTaskCharterPacket:
    payload = AgenticDeTaskCharterPacket.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_TASK_CHARTER_PACKET_SCHEMA:
        raise ValueError(f"unexpected schema marker for task charter packet: {payload.schema}")
    return payload


def load_task_residual_packet(path: Path) -> AgenticDeTaskResidualPacket:
    payload = AgenticDeTaskResidualPacket.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_TASK_RESIDUAL_PACKET_SCHEMA:
        raise ValueError(f"unexpected schema marker for task residual packet: {payload.schema}")
    return payload


def load_loop_state_ledger(path: Path) -> AgenticDeLoopStateLedger:
    payload = AgenticDeLoopStateLedger.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_LOOP_STATE_LEDGER_SCHEMA:
        raise ValueError(f"unexpected schema marker for loop state ledger: {payload.schema}")
    return payload


def load_continuation_decision_record(path: Path) -> AgenticDeContinuationDecisionRecord:
    payload = AgenticDeContinuationDecisionRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_CONTINUATION_DECISION_RECORD_SCHEMA:
        raise ValueError(
            "unexpected schema marker for continuation decision record: "
            f"{payload.schema}"
        )
    return payload


def load_live_restoration_handoff_record(path: Path) -> AgenticDeLiveRestorationHandoffRecord:
    payload = AgenticDeLiveRestorationHandoffRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_LIVE_RESTORATION_HANDOFF_RECORD_SCHEMA:
        raise ValueError(
            "unexpected schema marker for live restoration handoff record: "
            f"{payload.schema}"
        )
    return payload


def load_live_restoration_reintegration_report(
    path: Path,
) -> AgenticDeLiveRestorationReintegrationReport:
    payload = AgenticDeLiveRestorationReintegrationReport.model_validate(
        _read_json_object(path)
    )
    if payload.schema != AGENTIC_DE_LIVE_RESTORATION_REINTEGRATION_REPORT_SCHEMA:
        raise ValueError(
            "unexpected schema marker for live restoration reintegration report: "
            f"{payload.schema}"
        )
    return payload


def load_live_harness_hardening_register(
    path: Path,
) -> AgenticDeLiveHarnessHardeningRegister:
    payload = AgenticDeLiveHarnessHardeningRegister.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_LIVE_HARNESS_HARDENING_REGISTER_SCHEMA:
        raise ValueError(
            "unexpected schema marker for live harness hardening register: "
            f"{payload.schema}"
        )
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


def load_runtime_harvest_record(path: Path) -> AgenticDeRuntimeHarvestRecord:
    payload = AgenticDeRuntimeHarvestRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_RUNTIME_HARVEST_RECORD_SCHEMA:
        raise ValueError(f"unexpected schema marker for runtime harvest record: {payload.schema}")
    return payload


def load_governance_calibration_register(
    path: Path,
) -> AgenticDeGovernanceCalibrationRegister:
    payload = AgenticDeGovernanceCalibrationRegister.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_GOVERNANCE_CALIBRATION_REGISTER_SCHEMA:
        raise ValueError(
            "unexpected schema marker for governance calibration register: "
            f"{payload.schema}"
        )
    return payload


def load_migration_decision_register(path: Path) -> AgenticDeMigrationDecisionRegister:
    payload = AgenticDeMigrationDecisionRegister.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_MIGRATION_DECISION_REGISTER_SCHEMA:
        raise ValueError(
            f"unexpected schema marker for migration decision register: {payload.schema}"
        )
    return payload


def load_local_effect_observation_record(path: Path) -> AgenticDeLocalEffectObservationRecord:
    payload = AgenticDeLocalEffectObservationRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_LOCAL_EFFECT_OBSERVATION_RECORD_SCHEMA:
        raise ValueError(
            "unexpected schema marker for local-effect observation record: "
            f"{payload.schema}"
        )
    return payload


def load_local_effect_conformance_report(path: Path) -> AgenticDeLocalEffectConformanceReport:
    payload = AgenticDeLocalEffectConformanceReport.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_LOCAL_EFFECT_CONFORMANCE_REPORT_SCHEMA:
        raise ValueError(
            "unexpected schema marker for local-effect conformance report: "
            f"{payload.schema}"
        )
    return payload


def load_local_effect_restoration_record(path: Path) -> AgenticDeLocalEffectRestorationRecord:
    payload = AgenticDeLocalEffectRestorationRecord.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_LOCAL_EFFECT_RESTORATION_RECORD_SCHEMA:
        raise ValueError(
            "unexpected schema marker for local-effect restoration record: "
            f"{payload.schema}"
        )
    return payload


def load_local_effect_hardening_register(path: Path) -> AgenticDeLocalEffectHardeningRegister:
    payload = AgenticDeLocalEffectHardeningRegister.model_validate(_read_json_object(path))
    if payload.schema != AGENTIC_DE_LOCAL_EFFECT_HARDENING_REGISTER_SCHEMA:
        raise ValueError(
            "unexpected schema marker for local-effect hardening register: "
            f"{payload.schema}"
        )
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
    if not path.is_absolute():
        return repo_root_path / path
    default_root = repo_root(anchor=Path(__file__)).resolve()
    try:
        relative = path.resolve().relative_to(default_root)
    except ValueError:
        return path
    return repo_root_path / relative


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


def _validate_v57a_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V57A_TARGET_ARC:
        raise ValueError(
            f"V57-A lane drift record must target {V57A_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V57A_TARGET_PATH:
        raise ValueError(
            f"V57-A lane drift record must target {V57A_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V57A_PRIOR_LANE_REF:
        raise ValueError(
            "V57-A lane drift record must point at "
            f"{EXPECTED_V57A_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V57A_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    unexpected_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V57A_DRIFT_ENTRY_STATUSES.items()
        if actual_statuses.get(assumption_ref) != expected_status
    )
    if missing_assumptions or unexpected_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if unexpected_statuses:
            detail_parts.append(f"status_mismatch={unexpected_statuses}")
        raise ValueError(
            "V57-A lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v57b_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V57B_TARGET_ARC:
        raise ValueError(
            f"V57-B lane drift record must target {V57B_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V57B_TARGET_PATH:
        raise ValueError(
            f"V57-B lane drift record must target {V57B_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V57B_PRIOR_LANE_REF:
        raise ValueError(
            "V57-B lane drift record must point at "
            f"{EXPECTED_V57B_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V57B_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V57B_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses
        and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V57-B lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v57c_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V57C_TARGET_ARC:
        raise ValueError(
            f"V57-C lane drift record must target {V57C_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V57C_TARGET_PATH:
        raise ValueError(
            f"V57-C lane drift record must target {V57C_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V57C_PRIOR_LANE_REF:
        raise ValueError(
            "V57-C lane drift record must point at "
            f"{EXPECTED_V57C_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V57C_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V57C_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses
        and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V57-C lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v58a_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V58A_TARGET_ARC:
        raise ValueError(
            f"V58-A lane drift record must target {V58A_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V58A_TARGET_PATH:
        raise ValueError(
            f"V58-A lane drift record must target {V58A_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V58A_PRIOR_LANE_REF:
        raise ValueError(
            "V58-A lane drift record must point at "
            f"{EXPECTED_V58A_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V58A_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V58A_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses
        and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V58-A lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
    )
    return record


def _validate_v58b_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V58B_TARGET_ARC:
        raise ValueError(
            f"V58-B lane drift record must target {V58B_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V58B_TARGET_PATH:
        raise ValueError(
            f"V58-B lane drift record must target {V58B_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V58B_PRIOR_LANE_REF:
        raise ValueError(
            "V58-B lane drift record must point at "
            f"{EXPECTED_V58B_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V58B_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V58B_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses
        and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V58-B lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v58c_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V58C_TARGET_ARC:
        raise ValueError(
            f"V58-C lane drift record must target {V58C_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V58C_TARGET_PATH:
        raise ValueError(
            f"V58-C lane drift record must target {V58C_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V58C_PRIOR_LANE_REF:
        raise ValueError(
            "V58-C lane drift record must point at "
            f"{EXPECTED_V58C_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V58C_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V58C_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses
        and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V58-C lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v59a_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V59A_TARGET_ARC:
        raise ValueError(
            f"V59-A lane drift record must target {V59A_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V59A_TARGET_PATH:
        raise ValueError(
            f"V59-A lane drift record must target {V59A_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V59A_PRIOR_LANE_REF:
        raise ValueError(
            "V59-A lane drift record must point at "
            f"{EXPECTED_V59A_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V59A_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V59A_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses
        and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V59-A lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v59b_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V59B_TARGET_ARC:
        raise ValueError(
            f"V59-B lane drift record must target {V59B_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V59B_TARGET_PATH:
        raise ValueError(
            f"V59-B lane drift record must target {V59B_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V59B_PRIOR_LANE_REF:
        raise ValueError(
            "V59-B lane drift record must point at "
            f"{EXPECTED_V59B_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V59B_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V59B_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses
        and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V59-B lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v59c_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V59C_TARGET_ARC:
        raise ValueError(
            f"V59-C lane drift record must target {V59C_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V59C_TARGET_PATH:
        raise ValueError(
            f"V59-C lane drift record must target {V59C_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V59C_PRIOR_LANE_REF:
        raise ValueError(
            "V59-C lane drift record must point at "
            f"{EXPECTED_V59C_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V59C_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V59C_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses
        and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V59-C lane drift record does not satisfy the required handoff posture; "
            + ", ".join(detail_parts)
        )
    return record


def _validate_v60a_lane_drift_record(record: AgenticDeLaneDriftRecord) -> AgenticDeLaneDriftRecord:
    if record.target_arc != V60A_TARGET_ARC:
        raise ValueError(
            f"V60-A lane drift record must target {V60A_TARGET_ARC!r}, got {record.target_arc!r}"
        )
    if record.target_path != V60A_TARGET_PATH:
        raise ValueError(
            f"V60-A lane drift record must target {V60A_TARGET_PATH!r}, got {record.target_path!r}"
        )
    if record.prior_lane_ref != EXPECTED_V60A_PRIOR_LANE_REF:
        raise ValueError(
            "V60-A lane drift record must point at "
            f"{EXPECTED_V60A_PRIOR_LANE_REF!r}, got {record.prior_lane_ref!r}"
        )
    actual_statuses = {entry.assumption_ref: entry.status for entry in record.entries}
    missing_assumptions = sorted(set(REQUIRED_V60A_DRIFT_ENTRY_STATUSES) - set(actual_statuses))
    mismatched_statuses = sorted(
        assumption_ref
        for assumption_ref, expected_status in REQUIRED_V60A_DRIFT_ENTRY_STATUSES.items()
        if assumption_ref in actual_statuses
        and actual_statuses[assumption_ref] != expected_status
    )
    if missing_assumptions or mismatched_statuses:
        detail_parts: list[str] = []
        if missing_assumptions:
            detail_parts.append(f"missing={missing_assumptions}")
        if mismatched_statuses:
            detail_parts.append(f"status_mismatch={mismatched_statuses}")
        raise ValueError(
            "V60-A lane drift record does not satisfy the required handoff posture; "
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


def _validate_v56c_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V56C_EVIDENCE_SCHEMA:
        raise ValueError("V57-A requires the shipped V56-C evidence payload on main")
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list) or {
        "agentic_de_runtime_harvest_record@1",
        "agentic_de_governance_calibration_register@1",
        "agentic_de_migration_decision_register@1",
    } - set(selected_shapes):
        raise ValueError("V56-C evidence must preserve the shipped harvest/calibration/migration")
    if payload.get("changes_live_behavior_by_default") is not False:
        raise ValueError("V56-C evidence must keep advisory outputs non-live by default")
    if payload.get("selected_live_gate_action_classes_reused_from_v56b") != list(
        EXPECTED_V56B_SELECTED_LIVE_CLASSES
    ):
        raise ValueError("V56-C evidence must preserve the shipped selected live class reuse")
    if payload.get("selected_live_gate_action_class_interpretation_closed_for_v56c") is not True:
        raise ValueError("V56-C evidence must preserve the frozen live-class interpretation")
    if payload.get("committed_lane_artifacts_outrank_narrative_docs_for_v56c") is not True:
        raise ValueError(
            "V56-C evidence must preserve committed-lane-artifacts-over-narrative ordering"
        )
    if payload.get("surrogate_hidden_cognition_proxies_forbidden") is not True:
        raise ValueError("V56-C evidence must preserve the hidden-cognition proxy boundary")
    return payload


def _validate_v57a_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V57A_EVIDENCE_SCHEMA:
        raise ValueError("V57-B requires the shipped V57-A local-effect evidence payload on main")
    if payload.get("effect_outputs_evidence_only") is not True:
        raise ValueError("V57-A evidence must preserve evidence-only local-effect outputs")
    if payload.get("effect_observation_outputs_change_live_behavior_by_default") is not False:
        raise ValueError("V57-A evidence must preserve non-live local-effect outputs")
    if payload.get("restoration_selected_for_v57a") is not False:
        raise ValueError("V57-A evidence must preserve restoration as deferred")
    if payload.get("selected_live_action_class_for_v57a") != "local_write":
        raise ValueError("V57-A evidence must preserve the local_write-only actual-effect path")
    if payload.get("selected_local_write_first_subset_for_v57a") != [
        "create_new",
        "append_only",
    ]:
        raise ValueError("V57-A evidence must preserve the shipped first local_write subset")
    if payload.get("ticket_to_effect_binding_required") is not True:
        raise ValueError("V57-A evidence must preserve ticket-to-effect binding")
    return payload


def _validate_v57b_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V57B_EVIDENCE_SCHEMA:
        raise ValueError("V57-C requires the shipped V57-B local-effect evidence payload on main")
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list) or (
        "agentic_de_local_effect_restoration_record@1" not in selected_shapes
    ):
        raise ValueError("V57-B evidence must preserve the shipped restoration surface")
    if payload.get("selected_live_action_class_for_v57b") != "local_write":
        raise ValueError("V57-B evidence must preserve the local_write-only live class")
    if (
        payload.get("selected_restoration_exemplar_for_v57b")
        != "compensating_restore_of_v57a_create_new_artifact_only"
    ):
        raise ValueError("V57-B evidence must preserve the shipped restoration exemplar")
    if payload.get("restoration_outputs_change_live_behavior_by_default") is not False:
        raise ValueError("V57-B evidence must keep restoration outputs non-live by default")
    if payload.get("hardening_register_selected_for_v57b") is not False:
        raise ValueError("V57-B evidence must keep hardening deferred")
    if (
        payload.get("restoration_record_may_not_nominate_policy_class_or_entitlement_changes")
        is not True
    ):
        raise ValueError(
            "V57-B evidence must preserve non-promoting restoration record semantics"
        )
    return payload


def _validate_v57c_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V57C_EVIDENCE_SCHEMA:
        raise ValueError("V58-A requires the shipped V57-C local-effect evidence payload on main")
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list) or (
        "agentic_de_local_effect_hardening_register@1" not in selected_shapes
    ):
        raise ValueError("V57-C evidence must preserve the shipped hardening register surface")
    if payload.get("selected_hardening_target_surface_for_v57c") != (
        "observed_and_restored_v57a_create_new_exemplar_only"
    ):
        raise ValueError("V57-C evidence must preserve the shipped hardening target surface")
    if payload.get("exemplar_evidence_non_generalizing_by_default") is not True:
        raise ValueError("V57-C evidence must preserve non-generalizing exemplar posture")
    if payload.get("path_level_only") is not True:
        raise ValueError("V57-C evidence must preserve path-level-only hardening posture")
    if payload.get("hardening_outputs_advisory_only") is not True:
        raise ValueError("V57-C evidence must preserve advisory-only hardening outputs")
    if payload.get("changes_live_behavior_by_default") is not False:
        raise ValueError("V57-C evidence must keep hardening outputs non-live by default")
    if payload.get("committed_lane_artifacts_outrank_narrative_docs_for_v57c") is not True:
        raise ValueError(
            "V57-C evidence must preserve committed-lane-artifacts-over-narrative ordering"
        )
    return payload


def _validate_v58a_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V58A_EVIDENCE_SCHEMA:
        raise ValueError("V58-B requires the shipped V58-A live harness evidence payload on main")
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list) or {
        "agentic_de_live_turn_admission_record@1",
        "agentic_de_live_turn_handoff_record@1",
        "agentic_de_live_turn_reintegration_report@1",
    } - set(selected_shapes):
        raise ValueError("V58-A evidence must preserve the shipped live-turn bind surfaces")
    if payload.get("selected_live_session_surface_for_v58a") != "urm_copilot_session_path_only":
        raise ValueError("V58-A evidence must preserve the URM copilot session path only")
    if payload.get("selected_live_action_class_for_v58a") != "local_write":
        raise ValueError("V58-A evidence must preserve the local_write-only live class")
    if payload.get("selected_local_write_kind_for_v58a") != "create_new":
        raise ValueError("V58-A evidence must preserve the create_new-only live write kind")
    if payload.get("restoration_selected_in_v58a") is not False:
        raise ValueError("V58-A evidence must preserve restoration as deferred")
    if payload.get("outer_harness_capability_necessary_but_not_sufficient") is not True:
        raise ValueError(
            "V58-A evidence must preserve outer-harness-necessary-but-not-sufficient law"
        )
    if payload.get("positive_reintegration_requires_witness_basis_or_certificate_ref") is not True:
        raise ValueError(
            "V58-A evidence must preserve witness-bearing positive reintegration"
        )
    if payload.get("root_origin_dedup_required_for_current_turn_support") is not True:
        raise ValueError("V58-A evidence must preserve current-turn root-origin dedup")
    return payload


def _validate_v58b_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V58B_EVIDENCE_SCHEMA:
        raise ValueError(
            "V58-C requires the shipped V58-B live restoration evidence payload on main"
        )
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list) or {
        "agentic_de_live_restoration_handoff_record@1",
        "agentic_de_live_restoration_reintegration_report@1",
    } - set(selected_shapes):
        raise ValueError("V58-B evidence must preserve the shipped live restoration surfaces")
    if payload.get("selected_live_session_surface_for_v58b") != "urm_copilot_session_path_only":
        raise ValueError("V58-B evidence must preserve the URM copilot session path only")
    if payload.get("selected_live_action_class_for_v58b") != "local_write":
        raise ValueError("V58-B evidence must preserve the local_write-only live class")
    if payload.get("selected_local_write_kind_for_v58b") != "create_new":
        raise ValueError("V58-B evidence must preserve the create_new-only live write kind")
    if payload.get("selected_restoration_surface_for_v58b") != (
        "v57b_create_new_compensating_restore_only"
    ):
        raise ValueError("V58-B evidence must preserve the shipped restoration surface")
    required_true_fields = (
        "restoration_is_new_live_act_not_ambient_authority",
        "original_ticket_not_ambient_ongoing_restoration_authority",
        "same_session_and_same_turn_restoration_continuation_required",
        "restoration_time_capability_and_approval_resnapshot_required",
        "action_ticket_ref_and_prior_reintegration_ref_are_historical_lineage_inputs_only",
        "positive_restoration_reintegration_requires_witness_basis_or_certificate_ref",
        "root_origin_dedup_required_for_current_turn_support",
        "replay_law_proof_surface_embedded_in_live_restoration_reintegration_report",
    )
    for field_name in required_true_fields:
        if payload.get(field_name) is not True:
            raise ValueError(f"V58-B evidence must preserve {field_name}")
    if payload.get("changes_live_behavior_by_default") is not False:
        raise ValueError("V58-B evidence must keep restoration outputs non-live by default")
    return payload


def _validate_v58c_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V58C_EVIDENCE_SCHEMA:
        raise ValueError("V59-A requires the shipped V58-C live harness evidence payload on main")
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list) or (
        "agentic_de_live_harness_hardening_register@1" not in selected_shapes
    ):
        raise ValueError("V58-C evidence must preserve the shipped live harness hardening surface")
    if payload.get("selected_live_session_surface_for_v58c") != "urm_copilot_session_path_only":
        raise ValueError("V58-C evidence must preserve the URM copilot session path only")
    if payload.get("selected_live_action_class_for_v58c") != "local_write":
        raise ValueError("V58-C evidence must preserve the local_write-only live class")
    if payload.get("selected_local_write_kind_for_v58c") != "create_new":
        raise ValueError("V58-C evidence must preserve the create_new-only live write kind")
    if payload.get("recommendation_function_extensional_and_replayable") is not True:
        raise ValueError(
            "V58-C evidence must preserve extensional and replayable advisory hardening"
        )
    if payload.get("lineage_root_non_independence_dedup_required") is not True:
        raise ValueError("V58-C evidence must preserve lineage-root non-independence dedup")
    if payload.get("changes_live_behavior_by_default") is not False:
        raise ValueError("V58-C evidence must preserve non-mutating live hardening posture")
    return payload


def _validate_v59a_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V59A_EVIDENCE_SCHEMA:
        raise ValueError(
            "V59-B requires the shipped V59-A workspace continuity evidence payload on main"
        )
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list) or {
        "agentic_de_workspace_continuity_region_declaration@1",
        "agentic_de_workspace_continuity_admission_record@1",
        "agentic_de_workspace_occupancy_report@1",
        "agentic_de_workspace_continuity_reintegration_report@1",
    } - set(selected_shapes):
        raise ValueError("V59-A evidence must preserve the shipped continuity surfaces")
    required_true_fields = (
        "continuity_admission_typed_and_replayable",
        "occupancy_typed_witness_bearing_and_replayable",
        "prior_workspace_state_context_not_standing_authority",
        "continuity_admission_additional_gate_not_v58_replacement",
        "positive_continuity_reintegration_requires_witness_basis_or_certificate_ref",
    )
    for field_name in required_true_fields:
        if payload.get(field_name) is not True:
            raise ValueError(f"V59-A evidence must preserve {field_name}")
    if payload.get("selected_live_session_surface_for_v59a") != "urm_copilot_session_path_only":
        raise ValueError("V59-A evidence must preserve the URM copilot session path only")
    if payload.get("selected_live_action_class_for_v59a") != "local_write":
        raise ValueError("V59-A evidence must preserve the local_write-only live class")
    if payload.get("selected_local_write_kind_for_v59a") != "create_new":
        raise ValueError("V59-A evidence must preserve the create_new-only live write kind")
    if payload.get("selected_continuity_root_for_v59a") != (
        DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix() + "/"
    ):
        raise ValueError("V59-A evidence must preserve the selected continuity root")
    if payload.get("changes_live_behavior_by_default") is not False:
        raise ValueError("V59-A evidence must preserve non-live continuity posture")
    return payload


def _validate_v59b_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V59B_EVIDENCE_SCHEMA:
        raise ValueError(
            "V59-C requires the shipped V59-B continuity restoration evidence payload on main"
        )
    selected_shapes = payload.get("selected_record_shapes")
    if not isinstance(selected_shapes, list) or {
        "agentic_de_local_effect_restoration_record@1",
        "agentic_de_workspace_continuity_restoration_handoff_record@1",
        "agentic_de_workspace_continuity_restoration_reintegration_report@1",
    } - set(selected_shapes):
        raise ValueError("V59-B evidence must preserve the shipped continuity restoration surfaces")
    required_true_fields = (
        "continuity_safe_restoration_is_new_live_act_not_ambient_authority",
        "same_session_and_same_turn_restoration_continuation_required",
        "restoration_time_resnapshot_required",
        "restoration_time_continuation_verdict_typed_witness_bearing_replayable",
        "historical_lineage_refs_lineage_only_not_entitlement",
        "prior_governed_state_baseline_match_required",
        "bounded_compensating_scope_match_required",
        "positive_continuity_restoration_reintegration_requires_witness_basis_or_certificate_ref",
        "replay_mode_bounded_to_exact_restoration_event_only",
    )
    for field_name in required_true_fields:
        if payload.get(field_name) is not True:
            raise ValueError(f"V59-B evidence must preserve {field_name}")
    if payload.get("selected_live_session_surface_for_v59b") != "urm_copilot_session_path_only":
        raise ValueError("V59-B evidence must preserve the URM copilot session path only")
    if payload.get("selected_live_action_class_for_v59b") != "local_write":
        raise ValueError("V59-B evidence must preserve the local_write-only live class")
    if payload.get("selected_local_write_kind_for_v59b") != "create_new":
        raise ValueError("V59-B evidence must preserve the create_new-only live write kind")
    if payload.get("selected_continuity_root_for_v59b") != (
        DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix() + "/"
    ):
        raise ValueError("V59-B evidence must preserve the selected continuity root")
    if payload.get("append_only_continuity_restoration_selected") is not False:
        raise ValueError("V59-B evidence must keep append-only restoration out of scope")
    if payload.get("overwrite_or_destructive_continuity_restoration_selected") is not False:
        raise ValueError(
            "V59-B evidence must keep overwrite or destructive restoration out of scope"
        )
    return payload


def _validate_v59c_evidence_payload(payload: dict[str, object]) -> dict[str, object]:
    if payload.get("schema") != EXPECTED_V59C_EVIDENCE_SCHEMA:
        raise ValueError(
            "V60-A requires the shipped V59-C continuity hardening evidence payload on main"
        )
    if (
        payload.get("contract_source")
        != "docs/LOCKED_CONTINUATION_vNEXT_PLUS163.md#machine-checkable-contract"
    ):
        raise ValueError("V59-C evidence must preserve the shipped contract source anchor")
    implementation_commit = payload.get("implementation_commit")
    if not isinstance(implementation_commit, str) or not implementation_commit:
        raise ValueError("V59-C evidence must preserve the shipped implementation commit ref")
    review_hardening_commit = payload.get("review_hardening_commit")
    if not isinstance(review_hardening_commit, str) or not review_hardening_commit:
        raise ValueError("V59-C evidence must preserve the shipped review hardening commit ref")
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
    if taxonomy.contract_ref != contract.contract_id:
        raise ValueError("V56-B taxonomy does not bind the provided interaction contract")
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


def _validate_v57a_reference_surfaces(
    *,
    packet: AgenticDeDomainPacket,
    proposal: AgenticDeActionProposal,
    checkpoint: AgenticDeMembraneCheckpoint,
    runtime_state: AgenticDeRuntimeState,
    ticket: AgenticDeActionTicket,
    taxonomy: AgenticDeActionClassTaxonomy,
    harvest: AgenticDeRuntimeHarvestRecord,
    governance: AgenticDeGovernanceCalibrationRegister,
    migration: AgenticDeMigrationDecisionRegister,
) -> None:
    if ticket.exact_action_class != "local_write":
        raise ValueError("V57-A requires the shipped V56-B local_write ticket")
    taxonomy_entry = _taxonomy_entry_for_action(taxonomy, action_id=proposal.action_id)
    if taxonomy_entry is None:
        raise ValueError("V57-A taxonomy must classify the shipped reference action")
    if taxonomy_entry.exact_action_class != "local_write":
        raise ValueError("V57-A requires the shipped local_write taxonomy classification")
    if taxonomy_entry.write_surface_category != "bounded_local_artifact":
        raise ValueError("V57-A requires the shipped bounded_local_artifact local_write meaning")
    if harvest.target_arc != V56C_TARGET_ARC or harvest.target_path != V56C_TARGET_PATH:
        raise ValueError("V57-A requires the shipped V56-C runtime harvest surface")
    if harvest.packet_ref != packet.packet_id:
        raise ValueError("V56-C harvest does not bind the provided domain packet")
    if harvest.proposal_ref != proposal.proposal_id:
        raise ValueError("V56-C harvest does not bind the provided action proposal")
    if harvest.checkpoint_ref != checkpoint.checkpoint_id:
        raise ValueError("V56-C harvest does not bind the provided checkpoint")
    if harvest.runtime_state_ref != runtime_state.state_id:
        raise ValueError("V56-C harvest does not bind the provided runtime state")
    if harvest.ticket_ref != ticket.ticket_id:
        raise ValueError("V56-C harvest does not bind the provided action ticket")
    if tuple(harvest.selected_live_action_classes) != EXPECTED_V56B_SELECTED_LIVE_CLASSES:
        raise ValueError("V57-A requires the shipped V56-C selected live class reuse")
    if harvest.selected_live_action_class_interpretation_frozen is not True:
        raise ValueError("V57-A requires the shipped frozen live-class interpretation")
    if harvest.executed_or_observed_effect != "no_live_effect" or harvest.live_effect_present:
        raise ValueError("V57-A requires the shipped pre-effect V56-C harvest posture")
    if not governance.entries:
        raise ValueError("V57-A requires the shipped V56-C governance register")
    if governance.advisory_only is not True or governance.changes_live_behavior_by_default:
        raise ValueError("V57-A requires advisory-only V56-C governance outputs")
    if migration.target_arc != V56C_TARGET_ARC or migration.target_path != V56C_TARGET_PATH:
        raise ValueError("V57-A requires the shipped V56-C migration register")
    candidate_entry = next(
        (
            entry
            for entry in migration.entries
            if entry.surface_id == "local_write_post_effect_observation_path"
        ),
        None,
    )
    if candidate_entry is None:
        raise ValueError("V57-A requires the shipped local_write_post_effect_observation_path")
    if candidate_entry.recommended_outcome != "candidate_for_later_local_hardening":
        raise ValueError(
            "V57-A requires the shipped V56-C local-write post-effect candidate outcome"
        )


def _validate_v57a_local_effect_surfaces(
    *,
    packet: AgenticDeDomainPacket,
    proposal: AgenticDeActionProposal,
    checkpoint: AgenticDeMembraneCheckpoint,
    runtime_state: AgenticDeRuntimeState,
    ticket: AgenticDeActionTicket,
    harvest: AgenticDeRuntimeHarvestRecord,
    observation: AgenticDeLocalEffectObservationRecord,
    conformance: AgenticDeLocalEffectConformanceReport,
) -> None:
    if observation.target_arc != V57A_TARGET_ARC or observation.target_path != V57A_TARGET_PATH:
        raise ValueError("V57-B requires the shipped V57-A observation surface")
    expected_designated_root = DESIGNATED_LOCAL_EFFECT_SANDBOX_ROOT.as_posix()
    if observation.designated_sandbox_root != expected_designated_root:
        raise ValueError(
            "V57-A observation designated_sandbox_root must preserve the shipped V57-A "
            "sandbox root before restoration replay is admitted"
        )
    if observation.packet_ref != packet.packet_id:
        raise ValueError("V57-A observation does not bind the provided domain packet")
    if observation.action_proposal_ref != proposal.proposal_id:
        raise ValueError("V57-A observation does not bind the provided action proposal")
    if observation.checkpoint_ref != checkpoint.checkpoint_id:
        raise ValueError("V57-A observation does not bind the provided checkpoint")
    if observation.runtime_state_ref != runtime_state.state_id:
        raise ValueError("V57-A observation does not bind the provided runtime state")
    if observation.ticket_ref != ticket.ticket_id:
        raise ValueError("V57-A observation does not bind the provided action ticket")
    if observation.harvest_ref != harvest.harvest_id:
        raise ValueError("V57-A observation does not bind the provided harvest")
    if observation.selected_live_action_class != "local_write":
        raise ValueError("V57-B requires the shipped local_write observation class")
    if observation.selected_local_write_kind != "create_new":
        raise ValueError("V57-B only admits compensating restore of the shipped create_new path")
    if observation.observation_outcome != "bounded_effect_observed":
        raise ValueError("V57-B requires one prior bounded_effect_observed outcome")
    if observation.boundedness_verdict != "bounded":
        raise ValueError("V57-B requires one prior bounded observation verdict")
    if len(observation.observed_write_set) != 1:
        raise ValueError("V57-B requires exactly one prior observed create_new artifact")
    observed_entry = observation.observed_write_set[0]
    if observed_entry.write_kind != "create_new":
        raise ValueError("V57-B only admits the shipped create_new observation exemplar")
    if observed_entry.existed_before:
        raise ValueError(
            "V57-B requires the shipped create_new artifact to have been absent before"
        )

    if conformance.target_arc != V57A_TARGET_ARC or conformance.target_path != V57A_TARGET_PATH:
        raise ValueError("V57-B requires the shipped V57-A conformance surface")
    if conformance.packet_ref != packet.packet_id:
        raise ValueError("V57-A conformance does not bind the provided domain packet")
    if conformance.action_proposal_ref != proposal.proposal_id:
        raise ValueError("V57-A conformance does not bind the provided action proposal")
    if conformance.checkpoint_ref != checkpoint.checkpoint_id:
        raise ValueError("V57-A conformance does not bind the provided checkpoint")
    if conformance.runtime_state_ref != runtime_state.state_id:
        raise ValueError("V57-A conformance does not bind the provided runtime state")
    if conformance.ticket_ref != ticket.ticket_id:
        raise ValueError("V57-A conformance does not bind the provided action ticket")
    if conformance.harvest_ref != harvest.harvest_id:
        raise ValueError("V57-A conformance does not bind the provided harvest")
    if conformance.observation_ref != observation.observation_id:
        raise ValueError("V57-A conformance does not bind the provided observation")
    if conformance.observation_outcome != observation.observation_outcome:
        raise ValueError("V57-A conformance must preserve the shipped observation outcome")
    if conformance.boundedness_verdict != observation.boundedness_verdict:
        raise ValueError("V57-A conformance must preserve the shipped boundedness verdict")
    if conformance.conformance_status != "effect_aligned":
        raise ValueError("V57-B requires the shipped aligned V57-A conformance path")


def _validate_v57b_local_effect_restoration_surface(
    *,
    packet: AgenticDeDomainPacket,
    proposal: AgenticDeActionProposal,
    checkpoint: AgenticDeMembraneCheckpoint,
    runtime_state: AgenticDeRuntimeState,
    ticket: AgenticDeActionTicket,
    harvest: AgenticDeRuntimeHarvestRecord,
    observation: AgenticDeLocalEffectObservationRecord,
    conformance: AgenticDeLocalEffectConformanceReport,
    restoration: AgenticDeLocalEffectRestorationRecord,
) -> None:
    if restoration.target_arc != V57B_TARGET_ARC or restoration.target_path != V57B_TARGET_PATH:
        raise ValueError("V57-C requires the shipped V57-B restoration surface")
    expected_designated_root = DESIGNATED_LOCAL_EFFECT_SANDBOX_ROOT.as_posix()
    if restoration.designated_sandbox_root != expected_designated_root:
        raise ValueError(
            "V57-B restoration designated_sandbox_root must preserve the shipped V57-B "
            "sandbox root before hardening evaluation is admitted"
        )
    if restoration.packet_ref != packet.packet_id:
        raise ValueError("V57-B restoration does not bind the provided domain packet")
    if restoration.action_proposal_ref != proposal.proposal_id:
        raise ValueError("V57-B restoration does not bind the provided action proposal")
    if restoration.checkpoint_ref != checkpoint.checkpoint_id:
        raise ValueError("V57-B restoration does not bind the provided checkpoint")
    if restoration.runtime_state_ref != runtime_state.state_id:
        raise ValueError("V57-B restoration does not bind the provided runtime state")
    if restoration.ticket_ref != ticket.ticket_id:
        raise ValueError("V57-B restoration does not bind the provided action ticket")
    if restoration.harvest_ref != harvest.harvest_id:
        raise ValueError("V57-B restoration does not bind the provided harvest")
    if restoration.observation_ref != observation.observation_id:
        raise ValueError("V57-B restoration does not bind the provided observation")
    if restoration.conformance_ref != conformance.report_id:
        raise ValueError("V57-B restoration does not bind the provided local-effect conformance")
    if restoration.restoration_boundedness_verdict != "bounded":
        raise ValueError("V57-C requires one prior bounded restoration verdict")
    if restoration.restoration_outcome != "restoration_effect_observed":
        raise ValueError("V57-C requires one prior restoration_effect_observed outcome")
    if len(restoration.restoration_observed_write_set) != 1:
        raise ValueError("V57-C requires exactly one prior observed restoration target")
    observed_entry = observation.observed_write_set[0]
    restoration_entry = restoration.restoration_observed_write_set[0]
    if restoration_entry.relative_path != observed_entry.relative_path:
        raise ValueError("V57-B restoration must preserve the shipped observed target path")
    if restoration_entry.existed_before_restoration is not True:
        raise ValueError(
            "V57-C requires the shipped restoration lineage to record an existing target "
            "before compensating removal"
        )
    if restoration_entry.bytes_removed != observed_entry.bytes_written:
        raise ValueError(
            "V57-C requires the shipped restoration lineage to preserve removed-bytes "
            "equivalence with the observed exemplar"
        )
    if restoration_entry.removed_content_sha256 != observed_entry.content_sha256:
        raise ValueError(
            "V57-C requires the shipped restoration lineage to preserve removed-content "
            "equivalence with the observed exemplar"
        )


def _validate_v57c_local_effect_hardening_surface(
    *,
    observation: AgenticDeLocalEffectObservationRecord,
    conformance: AgenticDeLocalEffectConformanceReport,
    restoration: AgenticDeLocalEffectRestorationRecord,
    hardening: AgenticDeLocalEffectHardeningRegister,
) -> None:
    if hardening.target_arc != V57C_TARGET_ARC or hardening.target_path != V57C_TARGET_PATH:
        raise ValueError("V58-A requires the shipped V57-C hardening surface")
    if hardening.advisory_only is not True or hardening.changes_live_behavior_by_default:
        raise ValueError("V58-A requires the shipped advisory-only V57-C hardening posture")
    if hardening.path_level_only is not True:
        raise ValueError("V58-A requires the shipped path-level-only V57-C hardening posture")
    if hardening.exemplar_evidence_non_generalizing_by_default is not True:
        raise ValueError("V58-A requires the shipped non-generalizing V57-C exemplar posture")
    if hardening.entry_count != 1:
        raise ValueError("V58-A requires exactly one shipped V57-C hardening entry")
    entry = hardening.entries[0]
    if entry.observation_ref != observation.observation_id:
        raise ValueError("V57-C hardening entry does not bind the shipped V57-A observation")
    if entry.local_effect_conformance_ref != conformance.report_id:
        raise ValueError("V57-C hardening entry does not bind the shipped V57-A conformance")
    if entry.restoration_ref != restoration.restoration_id:
        raise ValueError("V57-C hardening entry does not bind the shipped V57-B restoration")
    if (
        entry.selected_hardening_target_surface
        != "observed_and_restored_v57a_create_new_exemplar_only"
    ):
        raise ValueError("V58-A requires the shipped observed/restored create_new hardening target")


def _derived_restore_target_relative_path(
    observation: AgenticDeLocalEffectObservationRecord,
) -> str:
    sandbox_root = Path(observation.designated_sandbox_root)
    observed_path = Path(observation.observed_write_set[0].relative_path)
    try:
        relative_path = observed_path.relative_to(sandbox_root)
    except ValueError as exc:
        raise ValueError(
            "V57-B requires the shipped observation target to remain inside the designated "
            "sandbox effect region"
        ) from exc
    if not relative_path.parts:
        raise ValueError("V57-B requires a non-empty restoration target relative path")
    return relative_path.as_posix()


def _validate_restoration_materialization_lineage(
    *,
    observation: AgenticDeLocalEffectObservationRecord,
    materialized_observed_content_text: str,
) -> None:
    if materialized_observed_content_text == DEFAULT_LOCAL_EFFECT_PAYLOAD_TEXT:
        expected_sha256 = DEFAULT_LOCAL_EFFECT_PAYLOAD_SHA256
    else:
        expected_sha256 = hashlib.sha256(
            materialized_observed_content_text.encode("utf-8")
        ).hexdigest()
    observed_entry = observation.observed_write_set[0]
    if expected_sha256 != observed_entry.content_sha256:
        raise ValueError(
            "V57-B requires one explicit bounded compensating scope match against the shipped "
            "observed create_new artifact content"
        )


def _validate_v58b_live_restoration_surfaces(
    *,
    admission: AgenticDeLiveTurnAdmissionRecord,
    handoff: AgenticDeLiveTurnHandoffRecord,
    turn_reintegration: AgenticDeLiveTurnReintegrationReport,
    restoration: AgenticDeLocalEffectRestorationRecord,
    live_restoration_handoff: AgenticDeLiveRestorationHandoffRecord,
    live_restoration_reintegration: AgenticDeLiveRestorationReintegrationReport,
    ticket: AgenticDeActionTicket,
    observation: AgenticDeLocalEffectObservationRecord,
) -> None:
    if (
        live_restoration_handoff.target_arc != V58B_TARGET_ARC
        or live_restoration_handoff.target_path != V58B_TARGET_PATH
    ):
        raise ValueError("V58-C requires the shipped V58-B live restoration handoff surface")
    if (
        live_restoration_reintegration.target_arc != V58B_TARGET_ARC
        or live_restoration_reintegration.target_path != V58B_TARGET_PATH
    ):
        raise ValueError(
            "V58-C requires the shipped V58-B live restoration reintegration surface"
        )
    if live_restoration_handoff.evidence_only is not True:
        raise ValueError("V58-C requires the shipped evidence-only V58-B handoff posture")
    if live_restoration_handoff.changes_live_behavior_by_default:
        raise ValueError("V58-C requires the shipped non-live V58-B handoff posture")
    if live_restoration_reintegration.evidence_only is not True:
        raise ValueError("V58-C requires the shipped evidence-only V58-B reintegration posture")
    if live_restoration_reintegration.changes_live_behavior_by_default:
        raise ValueError("V58-C requires the shipped non-live V58-B reintegration posture")
    if live_restoration_handoff.turn_admission_ref != admission.admission_id:
        raise ValueError("V58-B handoff does not bind the shipped V58-A admission lineage")
    if live_restoration_handoff.turn_handoff_ref != handoff.handoff_id:
        raise ValueError("V58-B handoff does not bind the shipped V58-A handoff lineage")
    if live_restoration_handoff.prior_reintegration_ref != turn_reintegration.report_id:
        raise ValueError("V58-B handoff does not bind the shipped V58-A reintegration lineage")
    if live_restoration_handoff.restoration_record_ref != restoration.restoration_id:
        raise ValueError("V58-B handoff does not bind the shipped V57-B restoration lineage")
    if live_restoration_handoff.action_ticket_ref != ticket.ticket_id:
        raise ValueError("V58-B handoff does not bind the shipped V56-B ticket lineage")
    expected_target = _derived_restore_target_relative_path(observation)
    if live_restoration_handoff.target_relative_path != expected_target:
        raise ValueError("V58-B handoff does not preserve the shipped selected target")
    if live_restoration_handoff.restoration_time_continuation_verdict != "continued":
        raise ValueError("V58-C requires the shipped continued V58-B restoration posture")
    if live_restoration_reintegration.turn_admission_ref != admission.admission_id:
        raise ValueError("V58-B reintegration does not bind the shipped V58-A admission lineage")
    if (
        live_restoration_reintegration.live_restoration_handoff_ref
        != live_restoration_handoff.handoff_id
    ):
        raise ValueError("V58-B reintegration does not bind the shipped V58-B handoff")
    if live_restoration_reintegration.restoration_record_ref != restoration.restoration_id:
        raise ValueError("V58-B reintegration does not bind the shipped restoration record")
    if live_restoration_reintegration.restoration_reintegration_status != "reintegrated":
        raise ValueError("V58-C requires the shipped reintegrated V58-B restoration posture")
    if "observability refs remain non-independent support" not in (
        live_restoration_reintegration.root_origin_dedup_summary
    ):
        raise ValueError("V58-B reintegration must preserve non-independent observability posture")


def _build_v58c_live_harness_hardening_register(
    *,
    admission: AgenticDeLiveTurnAdmissionRecord,
    handoff: AgenticDeLiveTurnHandoffRecord,
    turn_reintegration: AgenticDeLiveTurnReintegrationReport,
    observation: AgenticDeLocalEffectObservationRecord,
    conformance: AgenticDeLocalEffectConformanceReport,
    restoration: AgenticDeLocalEffectRestorationRecord,
    live_restoration_handoff: AgenticDeLiveRestorationHandoffRecord,
    live_restoration_reintegration: AgenticDeLiveRestorationReintegrationReport,
    evidence_refs: list[str],
) -> AgenticDeLiveHarnessHardeningRegister:
    root_origin_ids = [
        f"session:{admission.live_session_id}",
        f"turn:{admission.live_turn_id}",
        f"ticket:{handoff.action_ticket_ref}",
        f"observation:{observation.observation_id}",
        f"conformance:{conformance.report_id}",
        f"restoration:{restoration.restoration_id}",
        f"target:{handoff.target_relative_path}",
    ]
    entry = AgenticDeLiveHarnessHardeningEntry(
        turn_admission_ref=admission.admission_id,
        turn_handoff_ref=handoff.handoff_id,
        turn_reintegration_ref=turn_reintegration.report_id,
        live_restoration_handoff_ref=live_restoration_handoff.handoff_id,
        restoration_ref=restoration.restoration_id,
        live_restoration_reintegration_ref=live_restoration_reintegration.report_id,
        observation_ref=observation.observation_id,
        local_effect_conformance_ref=conformance.report_id,
        observation_boundedness_verdict=observation.boundedness_verdict,
        restoration_boundedness_verdict=restoration.restoration_boundedness_verdict,
        turn_reintegration_status=turn_reintegration.reintegration_status,
        restoration_reintegration_status=(
            live_restoration_reintegration.restoration_reintegration_status
        ),
        selected_hardening_target_surface=(
            "observed_and_restored_live_harness_create_new_exemplar_only"
        ),
        evidence_basis_summary=(
            "shipped V58-A admission/handoff/reintegration plus shipped V58-B live "
            "restoration handoff/reintegration over the same live harness-bound "
            "create_new exemplar"
        ),
        boundedness_reintegration_summary=(
            "observation remained bounded and turn reintegration stayed reintegrated; "
            "restoration remained bounded and live restoration reintegration stayed "
            "reintegrated over the same selected target"
        ),
        root_origin_ids=root_origin_ids,
        root_origin_dedup_summary=(
            "dedup roots="
            + ",".join(root_origin_ids)
            + "; repeated lineage artifacts remain non-independent escalation support"
        ),
        recommended_outcome="candidate_for_later_harness_hardening",
        rationale=(
            "the exact live harness-bound observed/restored exemplar now has bounded "
            "effect, bounded compensating restoration, and witness-bearing "
            "reintegration across both live acts under frozen semantics, so it is a "
            "valid later path-level harness hardening candidate, but any broader "
            "class, restoration, replay, or migration scope still requires a later "
            "explicit lock"
        ),
        reason_codes=[
            "observation_bounded",
            "restoration_bounded",
            "turn_reintegrated",
            "restoration_reintegrated",
            "path_level_only",
            "later_lock_required_for_scope",
            "extensional_replayable_policy",
            "lineage_root_dedup_applied",
            "no_live_mutation_in_v58c",
        ],
        evidence_refs=evidence_refs,
    )
    return AgenticDeLiveHarnessHardeningRegister(
        target_arc=V58C_TARGET_ARC,
        target_path=V58C_TARGET_PATH,
        baseline_checker_version=V58B_CHECKER_VERSION,
        entry_count=1,
        entries=[entry],
    )


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


def _build_v57a_local_effect_observation_record(
    *,
    packet: AgenticDeDomainPacket,
    proposal: AgenticDeActionProposal,
    checkpoint: AgenticDeMembraneCheckpoint,
    runtime_state: AgenticDeRuntimeState,
    ticket: AgenticDeActionTicket,
    harvest: AgenticDeRuntimeHarvestRecord,
    selected_local_write_kind: str,
    designated_sandbox_root: str,
    pre_state_ref: str,
    observed_write_set: list[object],
    post_state_ref: str,
    observed_effect: str,
    observation_outcome: str,
    boundedness_verdict: str,
    boundedness_note: str,
    evidence_refs: list[str],
) -> AgenticDeLocalEffectObservationRecord:
    return AgenticDeLocalEffectObservationRecord(
        target_arc=V57A_TARGET_ARC,
        target_path=V57A_TARGET_PATH,
        selected_local_write_kind=selected_local_write_kind,
        designated_sandbox_root=designated_sandbox_root,
        packet_ref=packet.packet_id,
        action_proposal_ref=proposal.proposal_id,
        checkpoint_ref=checkpoint.checkpoint_id,
        runtime_state_ref=runtime_state.state_id,
        ticket_ref=ticket.ticket_id,
        harvest_ref=harvest.harvest_id,
        pre_state_ref=pre_state_ref,
        observed_write_set=observed_write_set,
        post_state_ref=post_state_ref,
        observed_effect=observed_effect,
        observation_outcome=observation_outcome,
        boundedness_verdict=boundedness_verdict,
        boundedness_note=boundedness_note,
        evidence_refs=evidence_refs,
    )


def _build_v57b_local_effect_restoration_record(
    *,
    target_arc: str = V57B_TARGET_ARC,
    target_path: str = V57B_TARGET_PATH,
    packet: AgenticDeDomainPacket,
    proposal: AgenticDeActionProposal,
    checkpoint: AgenticDeMembraneCheckpoint,
    runtime_state: AgenticDeRuntimeState,
    ticket: AgenticDeActionTicket,
    harvest: AgenticDeRuntimeHarvestRecord,
    observation: AgenticDeLocalEffectObservationRecord,
    conformance: AgenticDeLocalEffectConformanceReport,
    designated_sandbox_root: str,
    restoration_pre_state_ref: str,
    restoration_observed_write_set: list[object],
    restoration_post_state_ref: str,
    restoration_effect: str,
    restoration_outcome: str,
    restoration_boundedness_verdict: str,
    restoration_boundedness_note: str,
    evidence_refs: list[str],
) -> AgenticDeLocalEffectRestorationRecord:
    return AgenticDeLocalEffectRestorationRecord(
        target_arc=target_arc,
        target_path=target_path,
        designated_sandbox_root=designated_sandbox_root,
        packet_ref=packet.packet_id,
        action_proposal_ref=proposal.proposal_id,
        checkpoint_ref=checkpoint.checkpoint_id,
        runtime_state_ref=runtime_state.state_id,
        ticket_ref=ticket.ticket_id,
        harvest_ref=harvest.harvest_id,
        observation_ref=observation.observation_id,
        conformance_ref=conformance.report_id,
        restoration_pre_state_ref=restoration_pre_state_ref,
        restoration_observed_write_set=restoration_observed_write_set,
        restoration_post_state_ref=restoration_post_state_ref,
        restoration_effect=restoration_effect,
        restoration_outcome=restoration_outcome,
        restoration_boundedness_verdict=restoration_boundedness_verdict,
        restoration_boundedness_note=restoration_boundedness_note,
        evidence_refs=evidence_refs,
    )


def _build_v57c_local_effect_hardening_register(
    *,
    ticket: AgenticDeActionTicket,
    proposal: AgenticDeActionProposal,
    checkpoint: AgenticDeMembraneCheckpoint,
    observation: AgenticDeLocalEffectObservationRecord,
    conformance: AgenticDeLocalEffectConformanceReport,
    restoration: AgenticDeLocalEffectRestorationRecord,
    evidence_refs: list[str],
) -> AgenticDeLocalEffectHardeningRegister:
    selected_target = (
        "observed_and_restored_v57a_create_new_exemplar_only"
    )
    entry = AgenticDeLocalEffectHardeningEntry(
        ticket_ref=ticket.ticket_id,
        action_proposal_ref=proposal.proposal_id,
        checkpoint_ref=checkpoint.checkpoint_id,
        observation_ref=observation.observation_id,
        local_effect_conformance_ref=conformance.report_id,
        restoration_ref=restoration.restoration_id,
        observation_boundedness_verdict=observation.boundedness_verdict,
        restoration_boundedness_verdict=restoration.restoration_boundedness_verdict,
        selected_hardening_target_surface=selected_target,
        evidence_basis_summary=(
            "shipped V57-A observation/conformance and shipped V57-B restoration over the "
            "same create_new exemplar inside the designated sandbox root"
        ),
        boundedness_conformance_summary=(
            "observation remained bounded and effect_aligned; restoration remained bounded "
            "and lineage-bound over the same create_new target"
        ),
        recommended_outcome="candidate_for_later_local_hardening",
        rationale=(
            "the selected observed/restored exemplar now has one bounded effect and one "
            "bounded compensating restore under frozen semantics, so it is a valid later "
            "path-level hardening candidate, but any scope beyond this exact exemplar still "
            "requires a later explicit lock"
        ),
        reason_codes=[
            "observation_bounded",
            "restoration_bounded",
            "path_level_only",
            "later_lock_required_for_scope",
            "no_live_mutation_in_v57c",
        ],
        evidence_refs=evidence_refs,
    )
    return AgenticDeLocalEffectHardeningRegister(
        target_arc=V57C_TARGET_ARC,
        target_path=V57C_TARGET_PATH,
        baseline_checker_version=V57B_CHECKER_VERSION,
        entry_count=1,
        entries=[entry],
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
        if repo_root_path.exists() and repo_root_path.is_symlink():
            raise ValueError("repository root may not be a symlink for V59-A continuity")
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
    expected_v56b_delta_notes = [
        *v56a_conformance.delta_notes,
        "ticket_issued=true",
        f"ticket_ref={v56b_ticket.ticket_id}",
    ]
    if v56b_conformance.delta_notes != expected_v56b_delta_notes:
        raise ValueError(
            "V56-B conformance must preserve the shipped V56-A base plus explicit "
            "ticket visibility in exact deterministic order"
        )
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


def run_agentic_de_local_effect_v57a(
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
    v56c_lane_drift_path: Path = DEFAULT_V56C_LANE_DRIFT_PATH,
    v56c_runtime_harvest_path: Path = DEFAULT_V56C_RUNTIME_HARVEST_PATH,
    v56c_governance_calibration_path: Path = DEFAULT_V56C_GOVERNANCE_CALIBRATION_PATH,
    v56c_migration_decision_path: Path = DEFAULT_V56C_MIGRATION_DECISION_PATH,
    lane_drift_path: Path = DEFAULT_V57A_LANE_DRIFT_PATH,
    v56a_evidence_path: Path = DEFAULT_V56C_V56A_EVIDENCE_PATH,
    v56b_evidence_path: Path = DEFAULT_V56C_V56B_EVIDENCE_PATH,
    v56c_evidence_path: Path = DEFAULT_V57A_V56C_EVIDENCE_PATH,
    write_kind: str = "create_new",
    target_relative_path: str = str(DEFAULT_LOCAL_EFFECT_TARGET_RELATIVE_PATH),
    payload_text: str = DEFAULT_LOCAL_EFFECT_PAYLOAD_TEXT,
    expected_relative_paths: tuple[str, ...] | None = None,
    expected_content_contains: str | None = "bounded local effect patch candidate",
) -> tuple[
    AgenticDeLocalEffectObservationRecord,
    AgenticDeLocalEffectConformanceReport,
]:
    if repo_root_path is None:
        root = repo_root(anchor=Path(__file__)).resolve()
    else:
        if repo_root_path.exists() and repo_root_path.is_symlink():
            raise ValueError("repository root may not be a symlink for V59-A continuity")
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
    v56c_lane_drift_path = _resolve_path(repo_root_path=root, path=v56c_lane_drift_path)
    v56c_runtime_harvest_path = _resolve_path(repo_root_path=root, path=v56c_runtime_harvest_path)
    v56c_governance_calibration_path = _resolve_path(
        repo_root_path=root, path=v56c_governance_calibration_path
    )
    v56c_migration_decision_path = _resolve_path(
        repo_root_path=root, path=v56c_migration_decision_path
    )
    lane_drift_path = _resolve_path(repo_root_path=root, path=lane_drift_path)
    v56a_evidence_path = _resolve_path(repo_root_path=root, path=v56a_evidence_path)
    v56b_evidence_path = _resolve_path(repo_root_path=root, path=v56b_evidence_path)
    v56c_evidence_path = _resolve_path(repo_root_path=root, path=v56c_evidence_path)

    _validate_v57a_lane_drift_record(load_lane_drift_record(lane_drift_path))
    _validate_v56b_lane_drift_record(load_lane_drift_record(v56b_lane_drift_path))
    _validate_v56c_lane_drift_record(load_lane_drift_record(v56c_lane_drift_path))
    _validate_v56a_evidence_payload(
        _load_json_object(v56a_evidence_path, error_label="V56-A evidence")
    )
    _validate_v56b_evidence_payload(
        _load_json_object(v56b_evidence_path, error_label="V56-B evidence")
    )
    _validate_v56c_evidence_payload(
        _load_json_object(v56c_evidence_path, error_label="V56-C evidence")
    )

    packet = load_domain_packet(domain_packet_path)
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
    v56c_harvest = load_runtime_harvest_record(v56c_runtime_harvest_path)
    v56c_governance = load_governance_calibration_register(v56c_governance_calibration_path)
    v56c_migration = load_migration_decision_register(v56c_migration_decision_path)

    _validate_v56a_reference_surfaces(
        domain_packet=packet,
        morph_ir=morph_ir,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        diagnostics=v56a_diagnostics,
        conformance=v56a_conformance,
    )
    _validate_v56b_reference_surfaces(
        domain_packet=packet,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        taxonomy=v56b_taxonomy,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        diagnostics=v56b_diagnostics,
        conformance=v56b_conformance,
    )
    _validate_v57a_reference_surfaces(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        taxonomy=v56b_taxonomy,
        harvest=v56c_harvest,
        governance=v56c_governance,
        migration=v56c_migration,
    )

    observed_effect = observe_local_write_effect(
        repo_root_path=root,
        write_kind=write_kind,
        target_relative_path=target_relative_path,
        payload_text=payload_text,
        expected_relative_paths=expected_relative_paths,
        expected_content_contains=expected_content_contains,
    )
    evidence_refs = [
        _render_input_ref(repo_root_path=root, path=domain_packet_path),
        _render_input_ref(repo_root_path=root, path=morph_ir_path),
        _render_input_ref(repo_root_path=root, path=interaction_contract_path),
        _render_input_ref(repo_root_path=root, path=action_proposal_path),
        _render_input_ref(repo_root_path=root, path=v56a_checkpoint_path),
        _render_input_ref(repo_root_path=root, path=v56a_diagnostics_path),
        _render_input_ref(repo_root_path=root, path=v56a_conformance_path),
        _render_input_ref(repo_root_path=root, path=v56b_action_class_taxonomy_path),
        _render_input_ref(repo_root_path=root, path=v56b_runtime_state_path),
        _render_input_ref(repo_root_path=root, path=v56b_action_ticket_path),
        _render_input_ref(repo_root_path=root, path=v56b_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56b_diagnostics_path),
        _render_input_ref(repo_root_path=root, path=v56b_conformance_path),
        _render_input_ref(repo_root_path=root, path=v56c_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56c_runtime_harvest_path),
        _render_input_ref(repo_root_path=root, path=v56c_governance_calibration_path),
        _render_input_ref(repo_root_path=root, path=v56c_migration_decision_path),
        _render_input_ref(repo_root_path=root, path=lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56a_evidence_path),
        _render_input_ref(repo_root_path=root, path=v56b_evidence_path),
        _render_input_ref(repo_root_path=root, path=v56c_evidence_path),
        observed_effect.pre_state_ref,
        observed_effect.post_state_ref,
    ]
    observation = _build_v57a_local_effect_observation_record(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        harvest=v56c_harvest,
        selected_local_write_kind=write_kind,
        designated_sandbox_root=observed_effect.designated_sandbox_root,
        pre_state_ref=observed_effect.pre_state_ref,
        observed_write_set=observed_effect.observed_write_set,
        post_state_ref=observed_effect.post_state_ref,
        observed_effect=observed_effect.observed_effect,
        observation_outcome=observed_effect.observation_outcome,
        boundedness_verdict=observed_effect.boundedness_verdict,
        boundedness_note=observed_effect.boundedness_note,
        evidence_refs=evidence_refs,
    )
    conformance = build_local_effect_conformance_report(
        target_arc=V57A_TARGET_ARC,
        target_path=V57A_TARGET_PATH,
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        harvest=v56c_harvest,
        observation=observation,
        evidence_refs=[*evidence_refs, observation.observation_id],
    )
    return observation, conformance


def run_agentic_de_local_effect_v57b(
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
    v56c_lane_drift_path: Path = DEFAULT_V56C_LANE_DRIFT_PATH,
    v56c_runtime_harvest_path: Path = DEFAULT_V56C_RUNTIME_HARVEST_PATH,
    v56c_governance_calibration_path: Path = DEFAULT_V56C_GOVERNANCE_CALIBRATION_PATH,
    v56c_migration_decision_path: Path = DEFAULT_V56C_MIGRATION_DECISION_PATH,
    v57a_lane_drift_path: Path = DEFAULT_V57A_LANE_DRIFT_PATH,
    v57a_observation_path: Path = DEFAULT_V57A_OBSERVATION_PATH,
    v57a_local_effect_conformance_path: Path = DEFAULT_V57A_LOCAL_EFFECT_CONFORMANCE_PATH,
    lane_drift_path: Path = DEFAULT_V57B_LANE_DRIFT_PATH,
    v56a_evidence_path: Path = DEFAULT_V56C_V56A_EVIDENCE_PATH,
    v56b_evidence_path: Path = DEFAULT_V56C_V56B_EVIDENCE_PATH,
    v56c_evidence_path: Path = DEFAULT_V57A_V56C_EVIDENCE_PATH,
    v57a_evidence_path: Path = DEFAULT_V57A_EVIDENCE_PATH,
    materialized_observed_content_text: str = DEFAULT_LOCAL_EFFECT_PAYLOAD_TEXT,
    expected_relative_paths: tuple[str, ...] | None = None,
    materialize_observed_effect: bool = True,
) -> AgenticDeLocalEffectRestorationRecord:
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
    v56c_lane_drift_path = _resolve_path(repo_root_path=root, path=v56c_lane_drift_path)
    v56c_runtime_harvest_path = _resolve_path(repo_root_path=root, path=v56c_runtime_harvest_path)
    v56c_governance_calibration_path = _resolve_path(
        repo_root_path=root, path=v56c_governance_calibration_path
    )
    v56c_migration_decision_path = _resolve_path(
        repo_root_path=root, path=v56c_migration_decision_path
    )
    v57a_lane_drift_path = _resolve_path(repo_root_path=root, path=v57a_lane_drift_path)
    v57a_observation_path = _resolve_path(repo_root_path=root, path=v57a_observation_path)
    v57a_local_effect_conformance_path = _resolve_path(
        repo_root_path=root, path=v57a_local_effect_conformance_path
    )
    lane_drift_path = _resolve_path(repo_root_path=root, path=lane_drift_path)
    v56a_evidence_path = _resolve_path(repo_root_path=root, path=v56a_evidence_path)
    v56b_evidence_path = _resolve_path(repo_root_path=root, path=v56b_evidence_path)
    v56c_evidence_path = _resolve_path(repo_root_path=root, path=v56c_evidence_path)
    v57a_evidence_path = _resolve_path(repo_root_path=root, path=v57a_evidence_path)

    _validate_v57b_lane_drift_record(load_lane_drift_record(lane_drift_path))
    _validate_v57a_lane_drift_record(load_lane_drift_record(v57a_lane_drift_path))
    _validate_v56b_lane_drift_record(load_lane_drift_record(v56b_lane_drift_path))
    _validate_v56c_lane_drift_record(load_lane_drift_record(v56c_lane_drift_path))
    _validate_v56a_evidence_payload(
        _load_json_object(v56a_evidence_path, error_label="V56-A evidence")
    )
    _validate_v56b_evidence_payload(
        _load_json_object(v56b_evidence_path, error_label="V56-B evidence")
    )
    _validate_v56c_evidence_payload(
        _load_json_object(v56c_evidence_path, error_label="V56-C evidence")
    )
    _validate_v57a_evidence_payload(
        _load_json_object(v57a_evidence_path, error_label="V57-A evidence")
    )

    packet = load_domain_packet(domain_packet_path)
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
    v56c_harvest = load_runtime_harvest_record(v56c_runtime_harvest_path)
    v56c_governance = load_governance_calibration_register(v56c_governance_calibration_path)
    v56c_migration = load_migration_decision_register(v56c_migration_decision_path)
    v57a_observation = load_local_effect_observation_record(v57a_observation_path)
    v57a_local_effect_conformance = load_local_effect_conformance_report(
        v57a_local_effect_conformance_path
    )

    _validate_v56a_reference_surfaces(
        domain_packet=packet,
        morph_ir=morph_ir,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        diagnostics=v56a_diagnostics,
        conformance=v56a_conformance,
    )
    _validate_v56b_reference_surfaces(
        domain_packet=packet,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        taxonomy=v56b_taxonomy,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        diagnostics=v56b_diagnostics,
        conformance=v56b_conformance,
    )
    _validate_v57a_reference_surfaces(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        taxonomy=v56b_taxonomy,
        harvest=v56c_harvest,
        governance=v56c_governance,
        migration=v56c_migration,
    )
    _validate_v57a_local_effect_surfaces(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        harvest=v56c_harvest,
        observation=v57a_observation,
        conformance=v57a_local_effect_conformance,
    )
    _validate_restoration_materialization_lineage(
        observation=v57a_observation,
        materialized_observed_content_text=materialized_observed_content_text,
    )

    restoration_target_relative_path = _derived_restore_target_relative_path(v57a_observation)
    restoration_effect = observe_local_write_restoration_effect(
        repo_root_path=root,
        restoration_target_relative_path=restoration_target_relative_path,
        materialized_observed_content_text=materialized_observed_content_text,
        expected_relative_paths=expected_relative_paths,
        materialize_observed_effect=materialize_observed_effect,
    )

    evidence_refs = [
        _render_input_ref(repo_root_path=root, path=domain_packet_path),
        _render_input_ref(repo_root_path=root, path=morph_ir_path),
        _render_input_ref(repo_root_path=root, path=interaction_contract_path),
        _render_input_ref(repo_root_path=root, path=action_proposal_path),
        _render_input_ref(repo_root_path=root, path=v56a_checkpoint_path),
        _render_input_ref(repo_root_path=root, path=v56a_diagnostics_path),
        _render_input_ref(repo_root_path=root, path=v56a_conformance_path),
        _render_input_ref(repo_root_path=root, path=v56b_action_class_taxonomy_path),
        _render_input_ref(repo_root_path=root, path=v56b_runtime_state_path),
        _render_input_ref(repo_root_path=root, path=v56b_action_ticket_path),
        _render_input_ref(repo_root_path=root, path=v56b_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56b_diagnostics_path),
        _render_input_ref(repo_root_path=root, path=v56b_conformance_path),
        _render_input_ref(repo_root_path=root, path=v56c_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56c_runtime_harvest_path),
        _render_input_ref(repo_root_path=root, path=v56c_governance_calibration_path),
        _render_input_ref(repo_root_path=root, path=v56c_migration_decision_path),
        _render_input_ref(repo_root_path=root, path=v57a_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v57a_observation_path),
        _render_input_ref(repo_root_path=root, path=v57a_local_effect_conformance_path),
        _render_input_ref(repo_root_path=root, path=lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56a_evidence_path),
        _render_input_ref(repo_root_path=root, path=v56b_evidence_path),
        _render_input_ref(repo_root_path=root, path=v56c_evidence_path),
        _render_input_ref(repo_root_path=root, path=v57a_evidence_path),
        restoration_effect.restoration_pre_state_ref,
        restoration_effect.restoration_post_state_ref,
    ]
    return _build_v57b_local_effect_restoration_record(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        harvest=v56c_harvest,
        observation=v57a_observation,
        conformance=v57a_local_effect_conformance,
        designated_sandbox_root=restoration_effect.designated_sandbox_root,
        restoration_pre_state_ref=restoration_effect.restoration_pre_state_ref,
        restoration_observed_write_set=restoration_effect.restoration_observed_write_set,
        restoration_post_state_ref=restoration_effect.restoration_post_state_ref,
        restoration_effect=restoration_effect.restoration_effect,
        restoration_outcome=restoration_effect.restoration_outcome,
        restoration_boundedness_verdict=restoration_effect.restoration_boundedness_verdict,
        restoration_boundedness_note=restoration_effect.restoration_boundedness_note,
        evidence_refs=evidence_refs,
    )


def run_agentic_de_local_effect_v57c(
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
    v56c_lane_drift_path: Path = DEFAULT_V56C_LANE_DRIFT_PATH,
    v56c_runtime_harvest_path: Path = DEFAULT_V56C_RUNTIME_HARVEST_PATH,
    v56c_governance_calibration_path: Path = DEFAULT_V56C_GOVERNANCE_CALIBRATION_PATH,
    v56c_migration_decision_path: Path = DEFAULT_V56C_MIGRATION_DECISION_PATH,
    v57a_lane_drift_path: Path = DEFAULT_V57A_LANE_DRIFT_PATH,
    v57a_observation_path: Path = DEFAULT_V57A_OBSERVATION_PATH,
    v57a_local_effect_conformance_path: Path = DEFAULT_V57A_LOCAL_EFFECT_CONFORMANCE_PATH,
    v57b_lane_drift_path: Path = DEFAULT_V57B_LANE_DRIFT_PATH,
    v57b_restoration_path: Path = DEFAULT_V57B_RESTORATION_PATH,
    lane_drift_path: Path = DEFAULT_V57C_LANE_DRIFT_PATH,
    v56a_evidence_path: Path = DEFAULT_V56C_V56A_EVIDENCE_PATH,
    v56b_evidence_path: Path = DEFAULT_V56C_V56B_EVIDENCE_PATH,
    v56c_evidence_path: Path = DEFAULT_V57A_V56C_EVIDENCE_PATH,
    v57a_evidence_path: Path = DEFAULT_V57A_EVIDENCE_PATH,
    v57b_evidence_path: Path = DEFAULT_V57B_EVIDENCE_PATH,
) -> AgenticDeLocalEffectHardeningRegister:
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
    v56c_lane_drift_path = _resolve_path(repo_root_path=root, path=v56c_lane_drift_path)
    v56c_runtime_harvest_path = _resolve_path(repo_root_path=root, path=v56c_runtime_harvest_path)
    v56c_governance_calibration_path = _resolve_path(
        repo_root_path=root, path=v56c_governance_calibration_path
    )
    v56c_migration_decision_path = _resolve_path(
        repo_root_path=root, path=v56c_migration_decision_path
    )
    v57a_lane_drift_path = _resolve_path(repo_root_path=root, path=v57a_lane_drift_path)
    v57a_observation_path = _resolve_path(repo_root_path=root, path=v57a_observation_path)
    v57a_local_effect_conformance_path = _resolve_path(
        repo_root_path=root, path=v57a_local_effect_conformance_path
    )
    v57b_lane_drift_path = _resolve_path(repo_root_path=root, path=v57b_lane_drift_path)
    v57b_restoration_path = _resolve_path(repo_root_path=root, path=v57b_restoration_path)
    lane_drift_path = _resolve_path(repo_root_path=root, path=lane_drift_path)
    v56a_evidence_path = _resolve_path(repo_root_path=root, path=v56a_evidence_path)
    v56b_evidence_path = _resolve_path(repo_root_path=root, path=v56b_evidence_path)
    v56c_evidence_path = _resolve_path(repo_root_path=root, path=v56c_evidence_path)
    v57a_evidence_path = _resolve_path(repo_root_path=root, path=v57a_evidence_path)
    v57b_evidence_path = _resolve_path(repo_root_path=root, path=v57b_evidence_path)

    _validate_v57c_lane_drift_record(load_lane_drift_record(lane_drift_path))
    _validate_v57b_lane_drift_record(load_lane_drift_record(v57b_lane_drift_path))
    _validate_v57a_lane_drift_record(load_lane_drift_record(v57a_lane_drift_path))
    _validate_v56b_lane_drift_record(load_lane_drift_record(v56b_lane_drift_path))
    _validate_v56c_lane_drift_record(load_lane_drift_record(v56c_lane_drift_path))
    _validate_v56a_evidence_payload(
        _load_json_object(v56a_evidence_path, error_label="V56-A evidence")
    )
    _validate_v56b_evidence_payload(
        _load_json_object(v56b_evidence_path, error_label="V56-B evidence")
    )
    _validate_v56c_evidence_payload(
        _load_json_object(v56c_evidence_path, error_label="V56-C evidence")
    )
    _validate_v57a_evidence_payload(
        _load_json_object(v57a_evidence_path, error_label="V57-A evidence")
    )
    _validate_v57b_evidence_payload(
        _load_json_object(v57b_evidence_path, error_label="V57-B evidence")
    )

    packet = load_domain_packet(domain_packet_path)
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
    v56c_harvest = load_runtime_harvest_record(v56c_runtime_harvest_path)
    v56c_governance = load_governance_calibration_register(v56c_governance_calibration_path)
    v56c_migration = load_migration_decision_register(v56c_migration_decision_path)
    v57a_observation = load_local_effect_observation_record(v57a_observation_path)
    v57a_local_effect_conformance = load_local_effect_conformance_report(
        v57a_local_effect_conformance_path
    )
    v57b_restoration = load_local_effect_restoration_record(v57b_restoration_path)

    _validate_v56a_reference_surfaces(
        domain_packet=packet,
        morph_ir=morph_ir,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        diagnostics=v56a_diagnostics,
        conformance=v56a_conformance,
    )
    _validate_v56b_reference_surfaces(
        domain_packet=packet,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        taxonomy=v56b_taxonomy,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        diagnostics=v56b_diagnostics,
        conformance=v56b_conformance,
    )
    _validate_v57a_reference_surfaces(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        taxonomy=v56b_taxonomy,
        harvest=v56c_harvest,
        governance=v56c_governance,
        migration=v56c_migration,
    )
    _validate_v57a_local_effect_surfaces(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        harvest=v56c_harvest,
        observation=v57a_observation,
        conformance=v57a_local_effect_conformance,
    )
    _validate_v57b_local_effect_restoration_surface(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        harvest=v56c_harvest,
        observation=v57a_observation,
        conformance=v57a_local_effect_conformance,
        restoration=v57b_restoration,
    )

    evidence_refs = [
        _render_input_ref(repo_root_path=root, path=domain_packet_path),
        _render_input_ref(repo_root_path=root, path=morph_ir_path),
        _render_input_ref(repo_root_path=root, path=interaction_contract_path),
        _render_input_ref(repo_root_path=root, path=action_proposal_path),
        _render_input_ref(repo_root_path=root, path=v56a_checkpoint_path),
        _render_input_ref(repo_root_path=root, path=v56a_diagnostics_path),
        _render_input_ref(repo_root_path=root, path=v56a_conformance_path),
        _render_input_ref(repo_root_path=root, path=v56b_action_class_taxonomy_path),
        _render_input_ref(repo_root_path=root, path=v56b_runtime_state_path),
        _render_input_ref(repo_root_path=root, path=v56b_action_ticket_path),
        _render_input_ref(repo_root_path=root, path=v56b_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56b_diagnostics_path),
        _render_input_ref(repo_root_path=root, path=v56b_conformance_path),
        _render_input_ref(repo_root_path=root, path=v56c_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56c_runtime_harvest_path),
        _render_input_ref(repo_root_path=root, path=v56c_governance_calibration_path),
        _render_input_ref(repo_root_path=root, path=v56c_migration_decision_path),
        _render_input_ref(repo_root_path=root, path=v57a_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v57a_observation_path),
        _render_input_ref(repo_root_path=root, path=v57a_local_effect_conformance_path),
        _render_input_ref(repo_root_path=root, path=v57b_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v57b_restoration_path),
        _render_input_ref(repo_root_path=root, path=lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56a_evidence_path),
        _render_input_ref(repo_root_path=root, path=v56b_evidence_path),
        _render_input_ref(repo_root_path=root, path=v56c_evidence_path),
        _render_input_ref(repo_root_path=root, path=v57a_evidence_path),
        _render_input_ref(repo_root_path=root, path=v57b_evidence_path),
    ]

    return _build_v57c_local_effect_hardening_register(
        ticket=v56b_ticket,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        observation=v57a_observation,
        conformance=v57a_local_effect_conformance,
        restoration=v57b_restoration,
        evidence_refs=evidence_refs,
    )


def _resolve_snapshot_cwd_path(
    *,
    repo_root_path: Path,
    raw_value: str | None,
    field_name: str,
) -> Path:
    if raw_value is None or not raw_value.strip():
        raise ValueError(f"{field_name} must be present for V58-A live-turn admission")
    raw_path = Path(raw_value.strip())
    if raw_path.is_absolute():
        return raw_path.resolve()
    return (repo_root_path / raw_path).resolve()


def _snapshot_observability_refs(
    *,
    repo_root_path: Path,
    live_turn_snapshot: CopilotTurnSnapshot,
) -> list[str]:
    refs: list[str] = []
    if live_turn_snapshot.raw_jsonl_path:
        refs.append(
            _render_input_ref(
                repo_root_path=repo_root_path,
                path=_resolve_path(
                    repo_root_path=repo_root_path,
                    path=Path(live_turn_snapshot.raw_jsonl_path),
                ),
            )
        )
    if live_turn_snapshot.urm_events_path:
        refs.append(
            _render_input_ref(
                repo_root_path=repo_root_path,
                path=_resolve_path(
                    repo_root_path=repo_root_path,
                    path=Path(live_turn_snapshot.urm_events_path),
                ),
            )
        )
    return refs


def _session_capability_snapshot(live_turn_snapshot: CopilotTurnSnapshot) -> str:
    return (
        f"status={live_turn_snapshot.status};"
        f"writes_allowed={'true' if live_turn_snapshot.writes_allowed else 'false'};"
        f"profile={live_turn_snapshot.profile_id}@{live_turn_snapshot.profile_version}"
    )


def _approval_posture_snapshot(live_turn_snapshot: CopilotTurnSnapshot) -> str:
    return (
        "writes_allowed_enabled"
        if live_turn_snapshot.writes_allowed
        else "writes_allowed_disabled"
    )


def _build_v58a_live_turn_admission_record(
    *,
    repo_root_path: Path,
    live_turn_snapshot: CopilotTurnSnapshot,
    target_relative_path: str,
    evidence_refs: list[str],
) -> AgenticDeLiveTurnAdmissionRecord:
    session_capability_snapshot = _session_capability_snapshot(live_turn_snapshot)
    approval_posture_snapshot = _approval_posture_snapshot(live_turn_snapshot)
    cwd_resolved = _resolve_snapshot_cwd_path(
        repo_root_path=repo_root_path,
        raw_value=live_turn_snapshot.cwd,
        field_name="cwd",
    )
    cwd_path = _render_input_ref(repo_root_path=repo_root_path, path=cwd_resolved)
    designated_sandbox_root = DESIGNATED_LOCAL_EFFECT_SANDBOX_ROOT.as_posix()
    selected_live_path_identity = (
        "urm_copilot_session_path::local_write/create_new::"
        f"{designated_sandbox_root}/{target_relative_path}"
    )

    if live_turn_snapshot.status not in {"starting", "running"}:
        admission_verdict = "stale_or_expired"
        admission_reason_codes = [
            "session_not_live",
            "current_turn_witness_not_admissible",
        ]
    elif cwd_resolved != repo_root_path.resolve():
        admission_verdict = "rejected_inadmissible"
        admission_reason_codes = [
            "cwd_repo_root_mismatch",
            "selected_live_path_not_admissible_for_current_turn",
        ]
    elif not live_turn_snapshot.writes_allowed:
        admission_verdict = "withheld"
        admission_reason_codes = [
            "writes_allowed_not_enabled",
            "outer_harness_capability_necessary_not_sufficient",
        ]
    else:
        admission_verdict = "admitted"
        admission_reason_codes = [
            "current_turn_selected",
            "writes_allowed_present_but_not_ticket_equivalent",
            "approval_posture_observed_but_not_ticket_equivalent",
        ]

    observability_refs = _snapshot_observability_refs(
        repo_root_path=repo_root_path,
        live_turn_snapshot=live_turn_snapshot,
    )
    return AgenticDeLiveTurnAdmissionRecord(
        target_arc=V58A_TARGET_ARC,
        target_path=V58A_TARGET_PATH,
        live_session_id=live_turn_snapshot.session_id,
        live_turn_id=live_turn_snapshot.selected_turn_id,
        session_status=live_turn_snapshot.status,
        session_capability_snapshot=session_capability_snapshot,
        approval_posture_snapshot=approval_posture_snapshot,
        admission_verdict=admission_verdict,
        admission_reason_codes=admission_reason_codes,
        repo_root_path=".",
        cwd_path=cwd_path,
        designated_sandbox_root=designated_sandbox_root,
        selected_live_path_identity=selected_live_path_identity,
        observability_refs=observability_refs,
        evidence_refs=[*observability_refs, *evidence_refs],
    )


def _build_v58a_live_turn_handoff_record(
    *,
    admission: AgenticDeLiveTurnAdmissionRecord,
    domain_packet: AgenticDeDomainPacket,
    proposal: AgenticDeActionProposal,
    checkpoint: AgenticDeMembraneCheckpoint,
    ticket: AgenticDeActionTicket,
    target_relative_path: str,
    evidence_refs: list[str],
) -> AgenticDeLiveTurnHandoffRecord:
    field_origin_tags = {
        "turn_admission_ref": "current_turn_native",
        "domain_packet_ref": "prior_artifact",
        "action_proposal_ref": "prior_artifact",
        "checkpoint_ref": "prior_artifact",
        "action_ticket_ref": "prior_artifact",
        "target_relative_path": "current_turn_derived",
        "selected_effect_scope": "current_turn_derived",
    }
    field_dependence_tags = {
        "turn_admission_ref": [],
        "domain_packet_ref": [],
        "action_proposal_ref": [],
        "checkpoint_ref": [],
        "action_ticket_ref": [],
        "target_relative_path": [
            admission.selected_live_path_identity,
        ],
        "selected_effect_scope": [
            ticket.ticket_id,
            proposal.proposal_id,
            target_relative_path,
        ],
    }
    root_origin_ids = [
        f"session:{admission.live_session_id}",
        f"turn:{admission.live_turn_id}",
        f"ticket:{ticket.ticket_id}",
        f"target:{target_relative_path}",
    ]
    return AgenticDeLiveTurnHandoffRecord(
        target_arc=V58A_TARGET_ARC,
        target_path=V58A_TARGET_PATH,
        turn_admission_ref=admission.admission_id,
        domain_packet_ref=domain_packet.packet_id,
        action_proposal_ref=proposal.proposal_id,
        checkpoint_ref=checkpoint.checkpoint_id,
        action_ticket_ref=ticket.ticket_id,
        target_relative_path=target_relative_path,
        selected_effect_scope=(
            "bounded local_write/create_new over the designated sandbox root only"
        ),
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=root_origin_ids,
        evidence_refs=[admission.admission_id, *evidence_refs],
    )


def _build_v58a_live_turn_reintegration_report(
    *,
    live_turn_snapshot: CopilotTurnSnapshot,
    admission: AgenticDeLiveTurnAdmissionRecord,
    handoff: AgenticDeLiveTurnHandoffRecord,
    observation: AgenticDeLocalEffectObservationRecord,
    conformance: AgenticDeLocalEffectConformanceReport,
    evidence_refs: list[str],
) -> AgenticDeLiveTurnReintegrationReport:
    if (
        observation.observation_outcome == "bounded_effect_observed"
        and conformance.conformance_status == "effect_aligned"
        and observation.boundedness_verdict == "bounded"
    ):
        reintegration_status = "reintegrated"
        reason_codes = [
            "current_turn_witness_declared",
            "ticket_to_effect_handoff_bound",
            "observed_effect_aligned",
        ]
        certificate_ref = (
            "v58a_reintegration::"
            f"{live_turn_snapshot.session_id}::"
            f"{live_turn_snapshot.selected_turn_id}::"
            f"{observation.observation_id}"
        )
        six_lane_closeout_posture = (
            "current_turn_admitted_then_ticket_handoff_bound_then_"
            "bounded_local_effect_observed_then_reintegrated_without_restoration"
        )
    elif observation.observation_outcome == "no_effect_observed":
        reintegration_status = "residualized"
        reason_codes = [
            "no_current_turn_effect_observed",
            "positive_reintegration_not_declared",
        ]
        certificate_ref = None
        six_lane_closeout_posture = "current_turn_residualized_no_effect"
    elif observation.observation_outcome == "boundedness_verdict_failed":
        reintegration_status = "blocked"
        reason_codes = [
            "boundedness_verdict_failed",
            "positive_reintegration_not_declared",
        ]
        certificate_ref = None
        six_lane_closeout_posture = "current_turn_blocked_boundedness_failed"
    else:
        reintegration_status = "blocked"
        reason_codes = [
            "observed_effect_not_reintegrable",
            "positive_reintegration_not_declared",
        ]
        certificate_ref = None
        six_lane_closeout_posture = "current_turn_blocked_non_aligned_effect"

    field_origin_tags = {
        "observed_effect_summary": "current_turn_derived",
        "reintegration_witness_basis_summary": "current_turn_derived",
        "six_lane_closeout_posture": "current_turn_derived",
    }
    field_dependence_tags = {
        "observed_effect_summary": [
            observation.observation_id,
            conformance.report_id,
        ],
        "reintegration_witness_basis_summary": [
            admission.admission_id,
            handoff.handoff_id,
            observation.observation_id,
            conformance.report_id,
        ],
        "six_lane_closeout_posture": [
            admission.admission_id,
            handoff.handoff_id,
            observation.observation_id,
            conformance.report_id,
        ],
    }
    root_origin_dedup_summary = (
        "dedup roots="
        f"session:{live_turn_snapshot.session_id},"
        f"turn:{live_turn_snapshot.selected_turn_id},"
        f"ticket:{handoff.action_ticket_ref},"
        f"observation:{observation.observation_id},"
        f"conformance:{conformance.report_id};"
        " observability refs remain non-independent support"
    )
    return AgenticDeLiveTurnReintegrationReport(
        target_arc=V58A_TARGET_ARC,
        target_path=V58A_TARGET_PATH,
        turn_admission_ref=admission.admission_id,
        turn_handoff_ref=handoff.handoff_id,
        observation_ref=observation.observation_id,
        local_effect_conformance_ref=conformance.report_id,
        observed_effect_summary=observation.observed_effect,
        reintegration_status=reintegration_status,
        reason_codes=reason_codes,
        reintegration_witness_basis_summary=(
            "current-turn admission + ticket lineage + observed pre/post state + "
            "observation/conformance chain"
        ),
        reintegration_certificate_ref_or_equivalent=certificate_ref,
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_dedup_summary=root_origin_dedup_summary,
        six_lane_closeout_posture=six_lane_closeout_posture,
        evidence_refs=[
            admission.admission_id,
            handoff.handoff_id,
            observation.observation_id,
            conformance.report_id,
            *evidence_refs,
        ],
    )


def _build_v59a_live_turn_admission_record(
    *,
    repo_root_path: Path,
    live_turn_snapshot: CopilotTurnSnapshot,
    target_relative_path: str,
    evidence_refs: list[str],
) -> AgenticDeLiveTurnAdmissionRecord:
    session_capability_snapshot = _session_capability_snapshot(live_turn_snapshot)
    approval_posture_snapshot = _approval_posture_snapshot(live_turn_snapshot)
    cwd_resolved = _resolve_snapshot_cwd_path(
        repo_root_path=repo_root_path,
        raw_value=live_turn_snapshot.cwd,
        field_name="cwd",
    )
    cwd_path = _render_input_ref(repo_root_path=repo_root_path, path=cwd_resolved)
    continuity_root = DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix()
    selected_live_path_identity = (
        "urm_copilot_session_path::local_write/create_new::"
        f"{continuity_root}/{target_relative_path}"
    )

    if live_turn_snapshot.status not in {"starting", "running"}:
        admission_verdict = "stale_or_expired"
        admission_reason_codes = [
            "session_not_live",
            "current_turn_witness_not_admissible",
        ]
    elif cwd_resolved != repo_root_path.resolve():
        admission_verdict = "rejected_inadmissible"
        admission_reason_codes = [
            "cwd_repo_root_mismatch",
            "selected_live_path_not_admissible_for_current_turn",
        ]
    elif not live_turn_snapshot.writes_allowed:
        admission_verdict = "withheld"
        admission_reason_codes = [
            "writes_allowed_not_enabled",
            "outer_harness_capability_necessary_not_sufficient",
        ]
    else:
        admission_verdict = "admitted"
        admission_reason_codes = [
            "current_turn_selected",
            "writes_allowed_present_but_not_ticket_equivalent",
            "approval_posture_observed_but_not_ticket_equivalent",
        ]

    observability_refs = _snapshot_observability_refs(
        repo_root_path=repo_root_path,
        live_turn_snapshot=live_turn_snapshot,
    )
    return AgenticDeLiveTurnAdmissionRecord(
        target_arc=V59A_TARGET_ARC,
        target_path=V59A_TARGET_PATH,
        live_session_id=live_turn_snapshot.session_id,
        live_turn_id=live_turn_snapshot.selected_turn_id,
        session_status=live_turn_snapshot.status,
        session_capability_snapshot=session_capability_snapshot,
        approval_posture_snapshot=approval_posture_snapshot,
        admission_verdict=admission_verdict,
        admission_reason_codes=admission_reason_codes,
        repo_root_path=".",
        cwd_path=cwd_path,
        designated_sandbox_root=continuity_root,
        selected_live_path_identity=selected_live_path_identity,
        observability_refs=observability_refs,
        evidence_refs=[*observability_refs, *evidence_refs],
    )


def _build_v59a_live_turn_handoff_record(
    *,
    admission: AgenticDeLiveTurnAdmissionRecord,
    domain_packet: AgenticDeDomainPacket,
    proposal: AgenticDeActionProposal,
    checkpoint: AgenticDeMembraneCheckpoint,
    ticket: AgenticDeActionTicket,
    target_relative_path: str,
    evidence_refs: list[str],
) -> AgenticDeLiveTurnHandoffRecord:
    field_origin_tags = {
        "turn_admission_ref": "current_turn_native",
        "domain_packet_ref": "prior_artifact",
        "action_proposal_ref": "prior_artifact",
        "checkpoint_ref": "prior_artifact",
        "action_ticket_ref": "prior_artifact",
        "target_relative_path": "current_turn_derived",
        "selected_effect_scope": "current_turn_derived",
    }
    field_dependence_tags = {
        "turn_admission_ref": [],
        "domain_packet_ref": [],
        "action_proposal_ref": [],
        "checkpoint_ref": [],
        "action_ticket_ref": [],
        "target_relative_path": [admission.selected_live_path_identity],
        "selected_effect_scope": [
            ticket.ticket_id,
            proposal.proposal_id,
            target_relative_path,
        ],
    }
    root_origin_ids = [
        f"session:{admission.live_session_id}",
        f"turn:{admission.live_turn_id}",
        f"ticket:{ticket.ticket_id}",
        f"target:{target_relative_path}",
    ]
    return AgenticDeLiveTurnHandoffRecord(
        target_arc=V59A_TARGET_ARC,
        target_path=V59A_TARGET_PATH,
        turn_admission_ref=admission.admission_id,
        domain_packet_ref=domain_packet.packet_id,
        action_proposal_ref=proposal.proposal_id,
        checkpoint_ref=checkpoint.checkpoint_id,
        action_ticket_ref=ticket.ticket_id,
        target_relative_path=target_relative_path,
        selected_effect_scope=(
            "bounded local_write/create_new over the declared continuity root only"
        ),
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=root_origin_ids,
        evidence_refs=[admission.admission_id, *evidence_refs],
    )


def _build_v59a_local_effect_observation_record(
    *,
    packet: AgenticDeDomainPacket,
    proposal: AgenticDeActionProposal,
    checkpoint: AgenticDeMembraneCheckpoint,
    runtime_state: AgenticDeRuntimeState,
    ticket: AgenticDeActionTicket,
    harvest: AgenticDeRuntimeHarvestRecord,
    selected_local_write_kind: str,
    declared_continuity_root: str,
    pre_state_ref: str,
    observed_write_set: list[object],
    post_state_ref: str,
    observed_effect: str,
    observation_outcome: str,
    boundedness_verdict: str,
    boundedness_note: str,
    evidence_refs: list[str],
) -> AgenticDeLocalEffectObservationRecord:
    return AgenticDeLocalEffectObservationRecord(
        target_arc=V59A_TARGET_ARC,
        target_path=V59A_TARGET_PATH,
        selected_local_write_kind=selected_local_write_kind,
        designated_sandbox_root=declared_continuity_root,
        packet_ref=packet.packet_id,
        action_proposal_ref=proposal.proposal_id,
        checkpoint_ref=checkpoint.checkpoint_id,
        runtime_state_ref=runtime_state.state_id,
        ticket_ref=ticket.ticket_id,
        harvest_ref=harvest.harvest_id,
        pre_state_ref=pre_state_ref,
        observed_write_set=observed_write_set,
        post_state_ref=post_state_ref,
        observed_effect=observed_effect,
        observation_outcome=observation_outcome,
        boundedness_verdict=boundedness_verdict,
        boundedness_note=boundedness_note,
        evidence_refs=evidence_refs,
    )


def _build_v59a_live_turn_reintegration_report(
    *,
    live_turn_snapshot: CopilotTurnSnapshot,
    admission: AgenticDeLiveTurnAdmissionRecord,
    handoff: AgenticDeLiveTurnHandoffRecord,
    observation: AgenticDeLocalEffectObservationRecord,
    conformance: AgenticDeLocalEffectConformanceReport,
    evidence_refs: list[str],
) -> AgenticDeLiveTurnReintegrationReport:
    if (
        observation.observation_outcome == "bounded_effect_observed"
        and conformance.conformance_status == "effect_aligned"
        and observation.boundedness_verdict == "bounded"
    ):
        reintegration_status = "reintegrated"
        reason_codes = [
            "current_turn_witness_declared",
            "ticket_to_effect_handoff_bound",
            "observed_effect_aligned",
        ]
        certificate_ref = (
            "v59a_live_reintegration::"
            f"{live_turn_snapshot.session_id}::"
            f"{live_turn_snapshot.selected_turn_id}::"
            f"{observation.observation_id}"
        )
        six_lane_closeout_posture = (
            "current_turn_admitted_then_ticket_handoff_bound_then_"
            "bounded_continuity_local_effect_observed_then_reintegrated_without_restoration"
        )
    elif observation.observation_outcome == "no_effect_observed":
        reintegration_status = "residualized"
        reason_codes = [
            "no_current_turn_effect_observed",
            "positive_reintegration_not_declared",
        ]
        certificate_ref = None
        six_lane_closeout_posture = "current_turn_residualized_no_effect"
    elif observation.observation_outcome == "boundedness_verdict_failed":
        reintegration_status = "blocked"
        reason_codes = [
            "boundedness_verdict_failed",
            "positive_reintegration_not_declared",
        ]
        certificate_ref = None
        six_lane_closeout_posture = "current_turn_blocked_boundedness_failed"
    else:
        reintegration_status = "blocked"
        reason_codes = [
            "observed_effect_not_reintegrable",
            "positive_reintegration_not_declared",
        ]
        certificate_ref = None
        six_lane_closeout_posture = "current_turn_blocked_non_aligned_effect"

    field_origin_tags = {
        "observed_effect_summary": "current_turn_derived",
        "reintegration_witness_basis_summary": "current_turn_derived",
        "six_lane_closeout_posture": "current_turn_derived",
    }
    field_dependence_tags = {
        "observed_effect_summary": [observation.observation_id, conformance.report_id],
        "reintegration_witness_basis_summary": [
            admission.admission_id,
            handoff.handoff_id,
            observation.observation_id,
            conformance.report_id,
        ],
        "six_lane_closeout_posture": [
            admission.admission_id,
            handoff.handoff_id,
            observation.observation_id,
            conformance.report_id,
        ],
    }
    root_origin_dedup_summary = (
        "dedup roots="
        f"session:{live_turn_snapshot.session_id},"
        f"turn:{live_turn_snapshot.selected_turn_id},"
        f"ticket:{handoff.action_ticket_ref},"
        f"observation:{observation.observation_id},"
        f"conformance:{conformance.report_id};"
        " observability refs remain non-independent support"
    )
    return AgenticDeLiveTurnReintegrationReport(
        target_arc=V59A_TARGET_ARC,
        target_path=V59A_TARGET_PATH,
        turn_admission_ref=admission.admission_id,
        turn_handoff_ref=handoff.handoff_id,
        observation_ref=observation.observation_id,
        local_effect_conformance_ref=conformance.report_id,
        observed_effect_summary=observation.observed_effect,
        reintegration_status=reintegration_status,
        reason_codes=reason_codes,
        reintegration_witness_basis_summary=(
            "current-turn admission + ticket lineage + continuity-root pre/post state + "
            "observation/conformance chain"
        ),
        reintegration_certificate_ref_or_equivalent=certificate_ref,
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_dedup_summary=root_origin_dedup_summary,
        six_lane_closeout_posture=six_lane_closeout_posture,
        evidence_refs=[
            admission.admission_id,
            handoff.handoff_id,
            observation.observation_id,
            conformance.report_id,
            *evidence_refs,
        ],
    )


def _build_v59a_workspace_continuity_region_declaration(
    *,
    evidence_refs: list[str],
) -> AgenticDeWorkspaceContinuityRegionDeclaration:
    return AgenticDeWorkspaceContinuityRegionDeclaration(
        target_arc=V59A_TARGET_ARC,
        target_path=V59A_TARGET_PATH,
        declared_continuity_root=DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix(),
        target_identity_or_target_set=str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
        allowed_write_kind_subset=["create_new"],
        occupancy_policy="only_unoccupied_target_is_entitling_for_create_new_in_v59a",
        region_origin_tags={
            "declared_continuity_root": "current_turn_derived",
            "target_identity_or_target_set": "current_turn_derived",
            "allowed_write_kind_subset": "current_turn_derived",
            "occupancy_policy": "current_turn_derived",
        },
        evidence_refs=evidence_refs,
    )


def _build_v59a_workspace_continuity_admission_record(
    *,
    repo_root_path: Path,
    admission: AgenticDeLiveTurnAdmissionRecord,
    handoff: AgenticDeLiveTurnHandoffRecord,
    region: AgenticDeWorkspaceContinuityRegionDeclaration,
    pre_state_summary: str,
    evidence_refs: list[str],
) -> AgenticDeWorkspaceContinuityAdmissionRecord:
    if admission.admission_verdict == "admitted":
        continuity_verdict = "admitted"
        continuity_reason_codes = [
            "current_turn_live_admission_preserved",
            "continuity_region_declared",
            "continuity_snapshot_replayed",
        ]
    elif admission.admission_verdict == "stale_or_expired":
        continuity_verdict = "stale_continuity_basis"
        continuity_reason_codes = [
            "live_turn_not_currently_live",
            "continuity_not_admitted",
        ]
    elif admission.admission_verdict == "withheld":
        continuity_verdict = "withheld_by_policy"
        continuity_reason_codes = [
            "live_turn_writes_not_enabled",
            "continuity_not_admitted",
        ]
    else:
        continuity_verdict = "rejected_inadmissible"
        continuity_reason_codes = [
            "live_turn_not_admitted",
            "continuity_not_admitted",
        ]

    field_origin_tags = {
        "continuity_snapshot_summary": "current_turn_derived",
        "continuity_root_identity": "current_turn_derived",
    }
    field_dependence_tags = {
        "continuity_snapshot_summary": [
            region.continuity_region_id,
            admission.admission_id,
        ],
        "continuity_root_identity": [region.continuity_region_id],
    }
    return AgenticDeWorkspaceContinuityAdmissionRecord(
        target_arc=V59A_TARGET_ARC,
        target_path=V59A_TARGET_PATH,
        live_turn_admission_ref=admission.admission_id,
        live_turn_handoff_ref=handoff.handoff_id,
        continuity_region_declaration_ref=region.continuity_region_id,
        continuity_verdict=continuity_verdict,
        continuity_reason_codes=continuity_reason_codes,
        continuity_snapshot_summary=pre_state_summary,
        repo_root_path=".",
        cwd_path=admission.cwd_path,
        continuity_root_identity=region.declared_continuity_root,
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        evidence_refs=[
            admission.admission_id,
            handoff.handoff_id,
            region.continuity_region_id,
            *evidence_refs,
        ],
    )


def _build_v59a_workspace_occupancy_report(
    *,
    continuity_admission: AgenticDeWorkspaceContinuityAdmissionRecord,
    target_relative_path: str,
    occupancy_assessment: WorkspaceOccupancyAssessment,
    evidence_refs: list[str],
) -> AgenticDeWorkspaceOccupancyReport:
    field_origin_tags = {
        "drift_posture_summary": "current_turn_derived",
        "out_of_band_evidence_summary": "current_turn_derived",
        "occupancy_witness_basis_summary": "current_turn_derived",
    }
    field_dependence_tags = {
        "drift_posture_summary": [continuity_admission.continuity_admission_id],
        "out_of_band_evidence_summary": [continuity_admission.continuity_admission_id],
        "occupancy_witness_basis_summary": [continuity_admission.continuity_admission_id],
    }
    return AgenticDeWorkspaceOccupancyReport(
        target_arc=V59A_TARGET_ARC,
        target_path=V59A_TARGET_PATH,
        continuity_admission_ref=continuity_admission.continuity_admission_id,
        target_relative_path=target_relative_path,
        occupancy_verdict=occupancy_assessment.occupancy_verdict,
        prior_governed_lineage_ref=occupancy_assessment.prior_governed_lineage_ref,
        drift_posture_summary=occupancy_assessment.drift_posture_summary,
        out_of_band_evidence_summary=occupancy_assessment.out_of_band_evidence_summary,
        occupancy_witness_basis_summary=occupancy_assessment.occupancy_witness_basis_summary,
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=occupancy_assessment.root_origin_ids,
        evidence_refs=[continuity_admission.continuity_admission_id, *evidence_refs],
    )


def _build_v59a_workspace_continuity_reintegration_report(
    *,
    live_turn_snapshot: CopilotTurnSnapshot,
    live_turn_reintegration: AgenticDeLiveTurnReintegrationReport,
    continuity_admission: AgenticDeWorkspaceContinuityAdmissionRecord,
    occupancy: AgenticDeWorkspaceOccupancyReport,
    observation: AgenticDeLocalEffectObservationRecord,
    conformance: AgenticDeLocalEffectConformanceReport,
    continuity_region_state_summary_after_act: str,
    evidence_refs: list[str],
) -> AgenticDeWorkspaceContinuityReintegrationReport:
    if (
        live_turn_reintegration.reintegration_status == "reintegrated"
        and continuity_admission.continuity_verdict == "admitted"
        and occupancy.occupancy_verdict == "unoccupied"
        and observation.observation_outcome == "bounded_effect_observed"
        and conformance.conformance_status == "effect_aligned"
    ):
        reintegration_status = "reintegrated"
        reason_codes = [
            "current_turn_continuity_witness_declared",
            "unoccupied_target_entitlement_bound",
            "continuity_effect_aligned",
        ]
        certificate_ref = (
            "v59a_continuity_reintegration::"
            f"{live_turn_snapshot.session_id}::"
            f"{live_turn_snapshot.selected_turn_id}::"
            f"{observation.observation_id}"
        )
    elif observation.observation_outcome == "no_effect_observed":
        reintegration_status = "residualized"
        reason_codes = [
            "no_current_turn_effect_observed",
            "positive_continuity_reintegration_not_declared",
        ]
        certificate_ref = None
    else:
        reintegration_status = "blocked"
        reason_codes = [
            "continuity_not_reintegrable",
            "positive_continuity_reintegration_not_declared",
        ]
        certificate_ref = None

    field_origin_tags = {
        "observed_effect_summary": "current_turn_derived",
        "continuity_witness_basis_summary": "current_turn_derived",
        "continuity_region_state_summary_after_act": "current_turn_derived",
    }
    field_dependence_tags = {
        "observed_effect_summary": [observation.observation_id, conformance.report_id],
        "continuity_witness_basis_summary": [
            live_turn_reintegration.report_id,
            continuity_admission.continuity_admission_id,
            occupancy.occupancy_report_id,
            observation.observation_id,
            conformance.report_id,
        ],
        "continuity_region_state_summary_after_act": [
            occupancy.occupancy_report_id,
            observation.observation_id,
        ],
    }
    root_origin_dedup_summary = (
        "dedup roots="
        f"session:{live_turn_snapshot.session_id},"
        f"turn:{live_turn_snapshot.selected_turn_id},"
        f"occupancy:{occupancy.occupancy_report_id},"
        f"observation:{observation.observation_id},"
        f"conformance:{conformance.report_id};"
        " repeated observability and prior-artifact refs remain non-independent support"
    )
    return AgenticDeWorkspaceContinuityReintegrationReport(
        target_arc=V59A_TARGET_ARC,
        target_path=V59A_TARGET_PATH,
        live_turn_reintegration_ref=live_turn_reintegration.report_id,
        continuity_admission_ref=continuity_admission.continuity_admission_id,
        occupancy_report_ref=occupancy.occupancy_report_id,
        observation_ref=observation.observation_id,
        local_effect_conformance_ref=conformance.report_id,
        observed_effect_summary=observation.observed_effect,
        continuity_reintegration_status=reintegration_status,
        reason_codes=reason_codes,
        continuity_witness_basis_summary=(
            "current-turn live admission/handoff/reintegration + continuity admission + "
            "occupancy witness + continuity-root pre/post state + observation/conformance chain"
        ),
        continuity_witness_certificate_ref_or_equivalent=certificate_ref,
        continuity_region_state_summary_after_act=continuity_region_state_summary_after_act,
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_dedup_summary=root_origin_dedup_summary,
        evidence_refs=[
            live_turn_reintegration.report_id,
            continuity_admission.continuity_admission_id,
            occupancy.occupancy_report_id,
            observation.observation_id,
            conformance.report_id,
            *evidence_refs,
        ],
    )


def run_agentic_de_live_harness_v58a(
    *,
    live_turn_snapshot: CopilotTurnSnapshot,
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
    v56c_lane_drift_path: Path = DEFAULT_V56C_LANE_DRIFT_PATH,
    v56c_runtime_harvest_path: Path = DEFAULT_V56C_RUNTIME_HARVEST_PATH,
    v56c_governance_calibration_path: Path = DEFAULT_V56C_GOVERNANCE_CALIBRATION_PATH,
    v56c_migration_decision_path: Path = DEFAULT_V56C_MIGRATION_DECISION_PATH,
    v57a_lane_drift_path: Path = DEFAULT_V57A_LANE_DRIFT_PATH,
    v57a_observation_path: Path = DEFAULT_V57A_OBSERVATION_PATH,
    v57a_local_effect_conformance_path: Path = DEFAULT_V57A_LOCAL_EFFECT_CONFORMANCE_PATH,
    v57b_lane_drift_path: Path = DEFAULT_V57B_LANE_DRIFT_PATH,
    v57b_restoration_path: Path = DEFAULT_V57B_RESTORATION_PATH,
    v57c_lane_drift_path: Path = DEFAULT_V57C_LANE_DRIFT_PATH,
    v57c_hardening_path: Path = DEFAULT_V57C_HARDENING_PATH,
    lane_drift_path: Path = DEFAULT_V58A_LANE_DRIFT_PATH,
    v56a_evidence_path: Path = DEFAULT_V56C_V56A_EVIDENCE_PATH,
    v56b_evidence_path: Path = DEFAULT_V56C_V56B_EVIDENCE_PATH,
    v56c_evidence_path: Path = DEFAULT_V57A_V56C_EVIDENCE_PATH,
    v57a_evidence_path: Path = DEFAULT_V57A_EVIDENCE_PATH,
    v57b_evidence_path: Path = DEFAULT_V57B_EVIDENCE_PATH,
    v57c_evidence_path: Path = DEFAULT_V57C_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_LOCAL_EFFECT_TARGET_RELATIVE_PATH),
    payload_text: str = DEFAULT_LOCAL_EFFECT_PAYLOAD_TEXT,
    expected_relative_paths: tuple[str, ...] | None = None,
    expected_content_contains: str | None = "bounded local effect patch candidate",
) -> tuple[
    AgenticDeLiveTurnAdmissionRecord,
    AgenticDeLiveTurnHandoffRecord,
    AgenticDeLocalEffectObservationRecord,
    AgenticDeLocalEffectConformanceReport,
    AgenticDeLiveTurnReintegrationReport,
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
    v56c_lane_drift_path = _resolve_path(repo_root_path=root, path=v56c_lane_drift_path)
    v56c_runtime_harvest_path = _resolve_path(repo_root_path=root, path=v56c_runtime_harvest_path)
    v56c_governance_calibration_path = _resolve_path(
        repo_root_path=root, path=v56c_governance_calibration_path
    )
    v56c_migration_decision_path = _resolve_path(
        repo_root_path=root, path=v56c_migration_decision_path
    )
    v57a_lane_drift_path = _resolve_path(repo_root_path=root, path=v57a_lane_drift_path)
    v57a_observation_path = _resolve_path(repo_root_path=root, path=v57a_observation_path)
    v57a_local_effect_conformance_path = _resolve_path(
        repo_root_path=root, path=v57a_local_effect_conformance_path
    )
    v57b_lane_drift_path = _resolve_path(repo_root_path=root, path=v57b_lane_drift_path)
    v57b_restoration_path = _resolve_path(repo_root_path=root, path=v57b_restoration_path)
    v57c_lane_drift_path = _resolve_path(repo_root_path=root, path=v57c_lane_drift_path)
    v57c_hardening_path = _resolve_path(repo_root_path=root, path=v57c_hardening_path)
    lane_drift_path = _resolve_path(repo_root_path=root, path=lane_drift_path)
    v56a_evidence_path = _resolve_path(repo_root_path=root, path=v56a_evidence_path)
    v56b_evidence_path = _resolve_path(repo_root_path=root, path=v56b_evidence_path)
    v56c_evidence_path = _resolve_path(repo_root_path=root, path=v56c_evidence_path)
    v57a_evidence_path = _resolve_path(repo_root_path=root, path=v57a_evidence_path)
    v57b_evidence_path = _resolve_path(repo_root_path=root, path=v57b_evidence_path)
    v57c_evidence_path = _resolve_path(repo_root_path=root, path=v57c_evidence_path)

    _validate_v58a_lane_drift_record(load_lane_drift_record(lane_drift_path))
    _validate_v57c_lane_drift_record(load_lane_drift_record(v57c_lane_drift_path))
    _validate_v57b_lane_drift_record(load_lane_drift_record(v57b_lane_drift_path))
    _validate_v57a_lane_drift_record(load_lane_drift_record(v57a_lane_drift_path))
    _validate_v56b_lane_drift_record(load_lane_drift_record(v56b_lane_drift_path))
    _validate_v56c_lane_drift_record(load_lane_drift_record(v56c_lane_drift_path))
    _validate_v56a_evidence_payload(
        _load_json_object(v56a_evidence_path, error_label="V56-A evidence")
    )
    _validate_v56b_evidence_payload(
        _load_json_object(v56b_evidence_path, error_label="V56-B evidence")
    )
    _validate_v56c_evidence_payload(
        _load_json_object(v56c_evidence_path, error_label="V56-C evidence")
    )
    _validate_v57a_evidence_payload(
        _load_json_object(v57a_evidence_path, error_label="V57-A evidence")
    )
    _validate_v57b_evidence_payload(
        _load_json_object(v57b_evidence_path, error_label="V57-B evidence")
    )
    _validate_v57c_evidence_payload(
        _load_json_object(v57c_evidence_path, error_label="V57-C evidence")
    )

    packet = load_domain_packet(domain_packet_path)
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
    v56c_harvest = load_runtime_harvest_record(v56c_runtime_harvest_path)
    v56c_governance = load_governance_calibration_register(v56c_governance_calibration_path)
    v56c_migration = load_migration_decision_register(v56c_migration_decision_path)
    reference_v57a_observation = load_local_effect_observation_record(v57a_observation_path)
    reference_v57a_conformance = load_local_effect_conformance_report(
        v57a_local_effect_conformance_path
    )
    v57b_restoration = load_local_effect_restoration_record(v57b_restoration_path)
    v57c_hardening = load_local_effect_hardening_register(v57c_hardening_path)

    _validate_v56a_reference_surfaces(
        domain_packet=packet,
        morph_ir=morph_ir,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        diagnostics=v56a_diagnostics,
        conformance=v56a_conformance,
    )
    _validate_v56b_reference_surfaces(
        domain_packet=packet,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        taxonomy=v56b_taxonomy,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        diagnostics=v56b_diagnostics,
        conformance=v56b_conformance,
    )
    _validate_v57a_reference_surfaces(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        taxonomy=v56b_taxonomy,
        harvest=v56c_harvest,
        governance=v56c_governance,
        migration=v56c_migration,
    )
    _validate_v57a_local_effect_surfaces(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        harvest=v56c_harvest,
        observation=reference_v57a_observation,
        conformance=reference_v57a_conformance,
    )
    _validate_v57b_local_effect_restoration_surface(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        harvest=v56c_harvest,
        observation=reference_v57a_observation,
        conformance=reference_v57a_conformance,
        restoration=v57b_restoration,
    )
    _validate_v57c_local_effect_hardening_surface(
        observation=reference_v57a_observation,
        conformance=reference_v57a_conformance,
        restoration=v57b_restoration,
        hardening=v57c_hardening,
    )

    base_evidence_refs = [
        _render_input_ref(repo_root_path=root, path=domain_packet_path),
        _render_input_ref(repo_root_path=root, path=morph_ir_path),
        _render_input_ref(repo_root_path=root, path=interaction_contract_path),
        _render_input_ref(repo_root_path=root, path=action_proposal_path),
        _render_input_ref(repo_root_path=root, path=v56a_checkpoint_path),
        _render_input_ref(repo_root_path=root, path=v56a_diagnostics_path),
        _render_input_ref(repo_root_path=root, path=v56a_conformance_path),
        _render_input_ref(repo_root_path=root, path=v56b_action_class_taxonomy_path),
        _render_input_ref(repo_root_path=root, path=v56b_runtime_state_path),
        _render_input_ref(repo_root_path=root, path=v56b_action_ticket_path),
        _render_input_ref(repo_root_path=root, path=v56b_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56b_diagnostics_path),
        _render_input_ref(repo_root_path=root, path=v56b_conformance_path),
        _render_input_ref(repo_root_path=root, path=v56c_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56c_runtime_harvest_path),
        _render_input_ref(repo_root_path=root, path=v56c_governance_calibration_path),
        _render_input_ref(repo_root_path=root, path=v56c_migration_decision_path),
        _render_input_ref(repo_root_path=root, path=v57a_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v57a_observation_path),
        _render_input_ref(repo_root_path=root, path=v57a_local_effect_conformance_path),
        _render_input_ref(repo_root_path=root, path=v57b_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v57b_restoration_path),
        _render_input_ref(repo_root_path=root, path=v57c_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v57c_hardening_path),
        _render_input_ref(repo_root_path=root, path=lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56a_evidence_path),
        _render_input_ref(repo_root_path=root, path=v56b_evidence_path),
        _render_input_ref(repo_root_path=root, path=v56c_evidence_path),
        _render_input_ref(repo_root_path=root, path=v57a_evidence_path),
        _render_input_ref(repo_root_path=root, path=v57b_evidence_path),
        _render_input_ref(repo_root_path=root, path=v57c_evidence_path),
    ]
    admission = _build_v58a_live_turn_admission_record(
        repo_root_path=root,
        live_turn_snapshot=live_turn_snapshot,
        target_relative_path=target_relative_path,
        evidence_refs=base_evidence_refs,
    )
    if admission.admission_verdict != "admitted":
        raise ValueError(
            "V58-A live turn admission must resolve to admitted before live harness "
            f"bind proceeds, got {admission.admission_verdict!r}"
        )
    handoff = _build_v58a_live_turn_handoff_record(
        admission=admission,
        domain_packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        ticket=v56b_ticket,
        target_relative_path=target_relative_path,
        evidence_refs=base_evidence_refs,
    )
    observation, local_effect_conformance = run_agentic_de_local_effect_v57a(
        repo_root_path=root,
        domain_packet_path=domain_packet_path,
        morph_ir_path=morph_ir_path,
        interaction_contract_path=interaction_contract_path,
        action_proposal_path=action_proposal_path,
        v56a_checkpoint_path=v56a_checkpoint_path,
        v56a_diagnostics_path=v56a_diagnostics_path,
        v56a_conformance_path=v56a_conformance_path,
        v56b_lane_drift_path=v56b_lane_drift_path,
        v56b_action_class_taxonomy_path=v56b_action_class_taxonomy_path,
        v56b_runtime_state_path=v56b_runtime_state_path,
        v56b_action_ticket_path=v56b_action_ticket_path,
        v56b_diagnostics_path=v56b_diagnostics_path,
        v56b_conformance_path=v56b_conformance_path,
        v56c_lane_drift_path=v56c_lane_drift_path,
        v56c_runtime_harvest_path=v56c_runtime_harvest_path,
        v56c_governance_calibration_path=v56c_governance_calibration_path,
        v56c_migration_decision_path=v56c_migration_decision_path,
        lane_drift_path=v57a_lane_drift_path,
        v56a_evidence_path=v56a_evidence_path,
        v56b_evidence_path=v56b_evidence_path,
        v56c_evidence_path=v56c_evidence_path,
        write_kind="create_new",
        target_relative_path=target_relative_path,
        payload_text=payload_text,
        expected_relative_paths=expected_relative_paths,
        expected_content_contains=expected_content_contains,
    )
    expected_observed_relative_path = (
        DESIGNATED_LOCAL_EFFECT_SANDBOX_ROOT / target_relative_path
    ).as_posix()
    if len(observation.observed_write_set) != 1:
        raise ValueError("V58-A requires exactly one observed create_new target")
    if observation.observed_write_set[0].relative_path != expected_observed_relative_path:
        raise ValueError("V58-A observed write path must preserve the selected live target")
    if observation.ticket_ref != v56b_ticket.ticket_id:
        raise ValueError("V58-A observed effect must bind the shipped V56-B ticket lineage")
    reintegration = _build_v58a_live_turn_reintegration_report(
        live_turn_snapshot=live_turn_snapshot,
        admission=admission,
        handoff=handoff,
        observation=observation,
        conformance=local_effect_conformance,
        evidence_refs=[
            *base_evidence_refs,
            observation.pre_state_ref,
            observation.post_state_ref,
        ],
    )
    return (
        admission,
        handoff,
        observation,
        local_effect_conformance,
        reintegration,
    )


def _validate_v58a_live_turn_surfaces(
    *,
    live_turn_snapshot: CopilotTurnSnapshot | None,
    admission: AgenticDeLiveTurnAdmissionRecord,
    handoff: AgenticDeLiveTurnHandoffRecord,
    reintegration: AgenticDeLiveTurnReintegrationReport,
    packet: AgenticDeDomainPacket,
    proposal: AgenticDeActionProposal,
    checkpoint: AgenticDeMembraneCheckpoint,
    ticket: AgenticDeActionTicket,
    observation: AgenticDeLocalEffectObservationRecord,
    conformance: AgenticDeLocalEffectConformanceReport,
    target_relative_path: str,
) -> None:
    if admission.target_arc != V58A_TARGET_ARC or admission.target_path != V58A_TARGET_PATH:
        raise ValueError("V58-B requires the shipped V58-A admission surface")
    if handoff.target_arc != V58A_TARGET_ARC or handoff.target_path != V58A_TARGET_PATH:
        raise ValueError("V58-B requires the shipped V58-A handoff surface")
    if (
        reintegration.target_arc != V58A_TARGET_ARC
        or reintegration.target_path != V58A_TARGET_PATH
    ):
        raise ValueError("V58-B requires the shipped V58-A reintegration surface")
    if admission.admission_verdict != "admitted":
        raise ValueError("V58-B requires one prior admitted V58-A live turn")
    if handoff.turn_admission_ref != admission.admission_id:
        raise ValueError("V58-A handoff must bind the provided admission record")
    if handoff.domain_packet_ref != packet.packet_id:
        raise ValueError("V58-A handoff does not bind the provided domain packet")
    if handoff.action_proposal_ref != proposal.proposal_id:
        raise ValueError("V58-A handoff does not bind the provided action proposal")
    if handoff.checkpoint_ref != checkpoint.checkpoint_id:
        raise ValueError("V58-A handoff does not bind the provided checkpoint")
    if handoff.action_ticket_ref != ticket.ticket_id:
        raise ValueError("V58-A handoff does not bind the provided action ticket")
    if handoff.target_relative_path != target_relative_path:
        raise ValueError("V58-A handoff must preserve the selected target relative path")
    if reintegration.turn_admission_ref != admission.admission_id:
        raise ValueError("V58-A reintegration must bind the provided admission record")
    if reintegration.turn_handoff_ref != handoff.handoff_id:
        raise ValueError("V58-A reintegration must bind the provided handoff record")
    if reintegration.observation_ref != observation.observation_id:
        raise ValueError("V58-A reintegration must bind the shipped V57-A observation")
    if reintegration.local_effect_conformance_ref != conformance.report_id:
        raise ValueError("V58-A reintegration must bind the shipped V57-A conformance")
    if reintegration.reintegration_status != "reintegrated":
        raise ValueError("V58-B requires one prior reintegrated V58-A live turn")
    if reintegration.reintegration_certificate_ref_or_equivalent is None:
        raise ValueError("V58-B requires one prior witness-bearing V58-A reintegration")
    if live_turn_snapshot is not None:
        if admission.live_session_id != live_turn_snapshot.session_id:
            raise ValueError("V58-B requires the same live session as the shipped V58-A admission")
        if admission.live_turn_id != live_turn_snapshot.selected_turn_id:
            raise ValueError("V58-B requires the same live turn as the shipped V58-A admission")


def _validate_v58b_restoration_time_continuation(
    *,
    repo_root_path: Path,
    live_turn_snapshot: CopilotTurnSnapshot,
    admission: AgenticDeLiveTurnAdmissionRecord,
    target_relative_path: str,
) -> tuple[str, str]:
    if live_turn_snapshot.session_id != admission.live_session_id:
        raise ValueError("V58-B requires same-session continuation from the shipped V58-A turn")
    if live_turn_snapshot.selected_turn_id != admission.live_turn_id:
        raise ValueError("V58-B requires same-turn continuation from the shipped V58-A turn")
    current_capability_snapshot = _session_capability_snapshot(live_turn_snapshot)
    current_approval_posture_snapshot = _approval_posture_snapshot(live_turn_snapshot)
    if current_capability_snapshot != admission.session_capability_snapshot:
        raise ValueError(
            "V58-B restoration-time session capability snapshot must match the admitted "
            "V58-A continuation posture"
        )
    if current_approval_posture_snapshot != admission.approval_posture_snapshot:
        raise ValueError(
            "V58-B restoration-time approval posture snapshot must match the admitted "
            "V58-A continuation posture"
        )
    cwd_resolved = _resolve_snapshot_cwd_path(
        repo_root_path=repo_root_path,
        raw_value=live_turn_snapshot.cwd,
        field_name="cwd",
    )
    if cwd_resolved != repo_root_path.resolve():
        raise ValueError(
            "V58-B restoration-time cwd must resolve to the admitted repository root"
        )
    if live_turn_snapshot.status not in {"starting", "running"}:
        raise ValueError("V58-B restoration-time session must remain live for continuation")
    selected_live_path_identity = (
        "urm_copilot_session_path::local_write/create_new::"
        f"{DESIGNATED_LOCAL_EFFECT_SANDBOX_ROOT.as_posix()}/{target_relative_path}"
    )
    if admission.selected_live_path_identity != selected_live_path_identity:
        raise ValueError("V58-B requires the shipped V58-A selected live path identity")
    return current_capability_snapshot, current_approval_posture_snapshot


def _build_v58b_live_restoration_handoff_record(
    *,
    live_turn_snapshot: CopilotTurnSnapshot,
    admission: AgenticDeLiveTurnAdmissionRecord,
    handoff: AgenticDeLiveTurnHandoffRecord,
    prior_reintegration: AgenticDeLiveTurnReintegrationReport,
    restoration: AgenticDeLocalEffectRestorationRecord,
    restoration_time_session_capability_snapshot: str,
    restoration_time_approval_posture_snapshot: str,
    target_relative_path: str,
    evidence_refs: list[str],
) -> AgenticDeLiveRestorationHandoffRecord:
    field_origin_tags = {
        "turn_admission_ref": "prior_artifact",
        "turn_handoff_ref": "prior_artifact",
        "prior_reintegration_ref": "prior_artifact",
        "restoration_time_session_capability_snapshot": "current_turn_native",
        "restoration_time_approval_posture_snapshot": "current_turn_native",
        "restoration_time_continuation_verdict": "current_turn_derived",
        "restoration_record_ref": "current_turn_derived",
        "action_ticket_ref": "prior_artifact",
        "bounded_compensating_scope_derivation_summary": "current_turn_derived",
        "target_relative_path": "current_turn_derived",
        "selected_restoration_scope": "current_turn_derived",
    }
    field_dependence_tags = {
        "turn_admission_ref": [],
        "turn_handoff_ref": [],
        "prior_reintegration_ref": [],
        "restoration_time_session_capability_snapshot": [],
        "restoration_time_approval_posture_snapshot": [],
        "restoration_time_continuation_verdict": [
            admission.admission_id,
            handoff.handoff_id,
            prior_reintegration.report_id,
        ],
        "restoration_record_ref": [],
        "action_ticket_ref": [],
        "bounded_compensating_scope_derivation_summary": [
            handoff.action_ticket_ref,
            prior_reintegration.report_id,
            restoration.restoration_id,
        ],
        "target_relative_path": [
            admission.selected_live_path_identity,
        ],
        "selected_restoration_scope": [
            handoff.action_ticket_ref,
            prior_reintegration.report_id,
            restoration.restoration_id,
            target_relative_path,
        ],
    }
    root_origin_ids = [
        f"session:{live_turn_snapshot.session_id}",
        f"turn:{live_turn_snapshot.selected_turn_id}",
        f"ticket:{handoff.action_ticket_ref}",
        f"restoration:{restoration.restoration_id}",
        f"target:{target_relative_path}",
    ]
    return AgenticDeLiveRestorationHandoffRecord(
        target_arc=V58B_TARGET_ARC,
        target_path=V58B_TARGET_PATH,
        turn_admission_ref=admission.admission_id,
        turn_handoff_ref=handoff.handoff_id,
        prior_reintegration_ref=prior_reintegration.report_id,
        restoration_time_session_capability_snapshot=restoration_time_session_capability_snapshot,
        restoration_time_approval_posture_snapshot=restoration_time_approval_posture_snapshot,
        restoration_time_continuation_verdict="continued",
        restoration_record_ref=restoration.restoration_id,
        action_ticket_ref=handoff.action_ticket_ref,
        bounded_compensating_scope_derivation_summary=(
            "bounded compensating scope derived from historical ticket/reintegration lineage "
            "+ current-turn restoration witness; historical refs remain non-entitling by "
            "themselves"
        ),
        target_relative_path=target_relative_path,
        selected_restoration_scope=(
            "bounded compensating remove-create-new restore over the designated sandbox "
            "root and selected target only"
        ),
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=root_origin_ids,
        evidence_refs=[
            admission.admission_id,
            handoff.handoff_id,
            prior_reintegration.report_id,
            restoration.restoration_id,
            *evidence_refs,
        ],
    )


def _build_v58b_live_restoration_reintegration_report(
    *,
    live_turn_snapshot: CopilotTurnSnapshot,
    admission: AgenticDeLiveTurnAdmissionRecord,
    live_restoration_handoff: AgenticDeLiveRestorationHandoffRecord,
    restoration: AgenticDeLocalEffectRestorationRecord,
    evidence_refs: list[str],
) -> AgenticDeLiveRestorationReintegrationReport:
    if (
        restoration.restoration_outcome == "restoration_effect_observed"
        and restoration.restoration_boundedness_verdict == "bounded"
    ):
        reintegration_status = "reintegrated"
        reason_codes = [
            "current_turn_restoration_witness_declared",
            "bounded_compensating_scope_matched",
            "restoration_effect_aligned",
        ]
        certificate_ref = (
            "v58b_restoration_reintegration::"
            f"{live_turn_snapshot.session_id}::"
            f"{live_turn_snapshot.selected_turn_id}::"
            f"{restoration.restoration_id}"
        )
        six_lane_closeout_posture = (
            "current_turn_admitted_then_ticket_handoff_bound_then_observed_effect_"
            "reintegrated_then_bounded_compensating_restore_reintegrated"
        )
    elif restoration.restoration_outcome == "no_restoration_effect_observed":
        reintegration_status = "residualized"
        reason_codes = [
            "no_current_turn_restoration_effect_observed",
            "positive_restoration_reintegration_not_declared",
        ]
        certificate_ref = None
        six_lane_closeout_posture = "current_turn_restoration_residualized_no_effect"
    elif restoration.restoration_outcome == "restoration_boundedness_verdict_failed":
        reintegration_status = "blocked"
        reason_codes = [
            "restoration_boundedness_verdict_failed",
            "positive_restoration_reintegration_not_declared",
        ]
        certificate_ref = None
        six_lane_closeout_posture = "current_turn_restoration_blocked_boundedness_failed"
    else:
        reintegration_status = "blocked"
        reason_codes = [
            "restoration_effect_not_reintegrable",
            "positive_restoration_reintegration_not_declared",
        ]
        certificate_ref = None
        six_lane_closeout_posture = "current_turn_restoration_blocked_non_aligned_effect"

    field_origin_tags = {
        "restoration_effect_summary": "current_turn_derived",
        "restoration_reintegration_witness_basis_summary": "current_turn_derived",
        "replay_law_proof_summary": "current_turn_derived",
        "six_lane_closeout_posture": "current_turn_derived",
    }
    field_dependence_tags = {
        "restoration_effect_summary": [
            restoration.restoration_id,
        ],
        "restoration_reintegration_witness_basis_summary": [
            admission.admission_id,
            live_restoration_handoff.handoff_id,
            restoration.restoration_id,
        ],
        "replay_law_proof_summary": [
            live_restoration_handoff.prior_reintegration_ref,
            restoration.restoration_id,
        ],
        "six_lane_closeout_posture": [
            admission.admission_id,
            live_restoration_handoff.handoff_id,
            restoration.restoration_id,
        ],
    }
    root_origin_dedup_summary = (
        "dedup roots="
        f"session:{live_turn_snapshot.session_id},"
        f"turn:{live_turn_snapshot.selected_turn_id},"
        f"ticket:{live_restoration_handoff.action_ticket_ref},"
        f"prior_reintegration:{live_restoration_handoff.prior_reintegration_ref},"
        f"restoration:{restoration.restoration_id};"
        " observability refs remain non-independent support"
    )
    return AgenticDeLiveRestorationReintegrationReport(
        target_arc=V58B_TARGET_ARC,
        target_path=V58B_TARGET_PATH,
        turn_admission_ref=admission.admission_id,
        live_restoration_handoff_ref=live_restoration_handoff.handoff_id,
        restoration_record_ref=restoration.restoration_id,
        restoration_effect_summary=restoration.restoration_effect,
        restoration_reintegration_status=reintegration_status,
        reason_codes=reason_codes,
        restoration_reintegration_witness_basis_summary=(
            "current-turn admission continuity + prior handoff/reintegration lineage + "
            "restoration pre/post state + restoration record"
        ),
        restoration_reintegration_certificate_ref_or_equivalent=certificate_ref,
        replay_law_proof_summary=(
            "bounded recomputation and re-evaluation of the exact compensating restore "
            "event over the same selected target and sandbox root only"
        ),
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_dedup_summary=root_origin_dedup_summary,
        six_lane_closeout_posture=six_lane_closeout_posture,
        evidence_refs=[
            admission.admission_id,
            live_restoration_handoff.handoff_id,
            restoration.restoration_id,
            *evidence_refs,
        ],
    )


def run_agentic_de_live_harness_v58b(
    *,
    live_turn_snapshot: CopilotTurnSnapshot,
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
    v56c_lane_drift_path: Path = DEFAULT_V56C_LANE_DRIFT_PATH,
    v56c_runtime_harvest_path: Path = DEFAULT_V56C_RUNTIME_HARVEST_PATH,
    v56c_governance_calibration_path: Path = DEFAULT_V56C_GOVERNANCE_CALIBRATION_PATH,
    v56c_migration_decision_path: Path = DEFAULT_V56C_MIGRATION_DECISION_PATH,
    v57a_lane_drift_path: Path = DEFAULT_V57A_LANE_DRIFT_PATH,
    v57a_observation_path: Path = DEFAULT_V57A_OBSERVATION_PATH,
    v57a_local_effect_conformance_path: Path = DEFAULT_V57A_LOCAL_EFFECT_CONFORMANCE_PATH,
    v57b_lane_drift_path: Path = DEFAULT_V57B_LANE_DRIFT_PATH,
    v57b_restoration_path: Path = DEFAULT_V57B_RESTORATION_PATH,
    v57c_lane_drift_path: Path = DEFAULT_V57C_LANE_DRIFT_PATH,
    v57c_hardening_path: Path = DEFAULT_V57C_HARDENING_PATH,
    v58a_lane_drift_path: Path = DEFAULT_V58A_LANE_DRIFT_PATH,
    v58a_admission_path: Path = DEFAULT_V58A_LIVE_TURN_ADMISSION_PATH,
    v58a_handoff_path: Path = DEFAULT_V58A_LIVE_TURN_HANDOFF_PATH,
    v58a_reintegration_path: Path = DEFAULT_V58A_LIVE_TURN_REINTEGRATION_PATH,
    lane_drift_path: Path = DEFAULT_V58B_LANE_DRIFT_PATH,
    v56a_evidence_path: Path = DEFAULT_V56C_V56A_EVIDENCE_PATH,
    v56b_evidence_path: Path = DEFAULT_V56C_V56B_EVIDENCE_PATH,
    v56c_evidence_path: Path = DEFAULT_V57A_V56C_EVIDENCE_PATH,
    v57a_evidence_path: Path = DEFAULT_V57A_EVIDENCE_PATH,
    v57b_evidence_path: Path = DEFAULT_V57B_EVIDENCE_PATH,
    v57c_evidence_path: Path = DEFAULT_V57C_EVIDENCE_PATH,
    v58a_evidence_path: Path = DEFAULT_V58A_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_LOCAL_EFFECT_TARGET_RELATIVE_PATH),
    materialized_observed_content_text: str = DEFAULT_LOCAL_EFFECT_PAYLOAD_TEXT,
    expected_relative_paths: tuple[str, ...] | None = None,
    materialize_observed_effect: bool = True,
) -> tuple[
    AgenticDeLiveRestorationHandoffRecord,
    AgenticDeLocalEffectRestorationRecord,
    AgenticDeLiveRestorationReintegrationReport,
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
    v56c_lane_drift_path = _resolve_path(repo_root_path=root, path=v56c_lane_drift_path)
    v56c_runtime_harvest_path = _resolve_path(repo_root_path=root, path=v56c_runtime_harvest_path)
    v56c_governance_calibration_path = _resolve_path(
        repo_root_path=root, path=v56c_governance_calibration_path
    )
    v56c_migration_decision_path = _resolve_path(
        repo_root_path=root, path=v56c_migration_decision_path
    )
    v57a_lane_drift_path = _resolve_path(repo_root_path=root, path=v57a_lane_drift_path)
    v57a_observation_path = _resolve_path(repo_root_path=root, path=v57a_observation_path)
    v57a_local_effect_conformance_path = _resolve_path(
        repo_root_path=root, path=v57a_local_effect_conformance_path
    )
    v57b_lane_drift_path = _resolve_path(repo_root_path=root, path=v57b_lane_drift_path)
    v57b_restoration_path = _resolve_path(repo_root_path=root, path=v57b_restoration_path)
    v57c_lane_drift_path = _resolve_path(repo_root_path=root, path=v57c_lane_drift_path)
    v57c_hardening_path = _resolve_path(repo_root_path=root, path=v57c_hardening_path)
    v58a_lane_drift_path = _resolve_path(repo_root_path=root, path=v58a_lane_drift_path)
    v58a_admission_path = _resolve_path(repo_root_path=root, path=v58a_admission_path)
    v58a_handoff_path = _resolve_path(repo_root_path=root, path=v58a_handoff_path)
    v58a_reintegration_path = _resolve_path(
        repo_root_path=root, path=v58a_reintegration_path
    )
    lane_drift_path = _resolve_path(repo_root_path=root, path=lane_drift_path)
    v56a_evidence_path = _resolve_path(repo_root_path=root, path=v56a_evidence_path)
    v56b_evidence_path = _resolve_path(repo_root_path=root, path=v56b_evidence_path)
    v56c_evidence_path = _resolve_path(repo_root_path=root, path=v56c_evidence_path)
    v57a_evidence_path = _resolve_path(repo_root_path=root, path=v57a_evidence_path)
    v57b_evidence_path = _resolve_path(repo_root_path=root, path=v57b_evidence_path)
    v57c_evidence_path = _resolve_path(repo_root_path=root, path=v57c_evidence_path)
    v58a_evidence_path = _resolve_path(repo_root_path=root, path=v58a_evidence_path)

    _validate_v58b_lane_drift_record(load_lane_drift_record(lane_drift_path))
    _validate_v58a_lane_drift_record(load_lane_drift_record(v58a_lane_drift_path))
    _validate_v57c_lane_drift_record(load_lane_drift_record(v57c_lane_drift_path))
    _validate_v57b_lane_drift_record(load_lane_drift_record(v57b_lane_drift_path))
    _validate_v57a_lane_drift_record(load_lane_drift_record(v57a_lane_drift_path))
    _validate_v56b_lane_drift_record(load_lane_drift_record(v56b_lane_drift_path))
    _validate_v56c_lane_drift_record(load_lane_drift_record(v56c_lane_drift_path))
    _validate_v56a_evidence_payload(
        _load_json_object(v56a_evidence_path, error_label="V56-A evidence")
    )
    _validate_v56b_evidence_payload(
        _load_json_object(v56b_evidence_path, error_label="V56-B evidence")
    )
    _validate_v56c_evidence_payload(
        _load_json_object(v56c_evidence_path, error_label="V56-C evidence")
    )
    _validate_v57a_evidence_payload(
        _load_json_object(v57a_evidence_path, error_label="V57-A evidence")
    )
    _validate_v57b_evidence_payload(
        _load_json_object(v57b_evidence_path, error_label="V57-B evidence")
    )
    _validate_v57c_evidence_payload(
        _load_json_object(v57c_evidence_path, error_label="V57-C evidence")
    )
    _validate_v58a_evidence_payload(
        _load_json_object(v58a_evidence_path, error_label="V58-A evidence")
    )

    packet = load_domain_packet(domain_packet_path)
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
    v56c_harvest = load_runtime_harvest_record(v56c_runtime_harvest_path)
    v56c_governance = load_governance_calibration_register(v56c_governance_calibration_path)
    v56c_migration = load_migration_decision_register(v56c_migration_decision_path)
    reference_v57a_observation = load_local_effect_observation_record(v57a_observation_path)
    reference_v57a_conformance = load_local_effect_conformance_report(
        v57a_local_effect_conformance_path
    )
    reference_v57b_restoration = load_local_effect_restoration_record(v57b_restoration_path)
    v57c_hardening = load_local_effect_hardening_register(v57c_hardening_path)
    v58a_admission = load_live_turn_admission_record(v58a_admission_path)
    v58a_handoff = load_live_turn_handoff_record(v58a_handoff_path)
    v58a_reintegration = load_live_turn_reintegration_report(v58a_reintegration_path)

    _validate_v56a_reference_surfaces(
        domain_packet=packet,
        morph_ir=morph_ir,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        diagnostics=v56a_diagnostics,
        conformance=v56a_conformance,
    )
    _validate_v56b_reference_surfaces(
        domain_packet=packet,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        taxonomy=v56b_taxonomy,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        diagnostics=v56b_diagnostics,
        conformance=v56b_conformance,
    )
    _validate_v57a_reference_surfaces(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        taxonomy=v56b_taxonomy,
        harvest=v56c_harvest,
        governance=v56c_governance,
        migration=v56c_migration,
    )
    _validate_v57a_local_effect_surfaces(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        harvest=v56c_harvest,
        observation=reference_v57a_observation,
        conformance=reference_v57a_conformance,
    )
    _validate_v57b_local_effect_restoration_surface(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        harvest=v56c_harvest,
        observation=reference_v57a_observation,
        conformance=reference_v57a_conformance,
        restoration=reference_v57b_restoration,
    )
    _validate_v57c_local_effect_hardening_surface(
        observation=reference_v57a_observation,
        conformance=reference_v57a_conformance,
        restoration=reference_v57b_restoration,
        hardening=v57c_hardening,
    )
    _validate_v58a_live_turn_surfaces(
        live_turn_snapshot=live_turn_snapshot,
        admission=v58a_admission,
        handoff=v58a_handoff,
        reintegration=v58a_reintegration,
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        ticket=v56b_ticket,
        observation=reference_v57a_observation,
        conformance=reference_v57a_conformance,
        target_relative_path=target_relative_path,
    )
    if v58a_handoff.action_ticket_ref != v56b_ticket.ticket_id:
        raise ValueError("V58-B requires the shipped V58-A ticket lineage")
    if v58a_reintegration.observation_ref != reference_v57a_observation.observation_id:
        raise ValueError("V58-B requires the shipped V58-A observed effect lineage")
    if v58a_reintegration.local_effect_conformance_ref != reference_v57a_conformance.report_id:
        raise ValueError("V58-B requires the shipped V58-A conformance lineage")

    (
        restoration_time_session_capability_snapshot,
        restoration_time_approval_posture_snapshot,
    ) = _validate_v58b_restoration_time_continuation(
        repo_root_path=root,
        live_turn_snapshot=live_turn_snapshot,
        admission=v58a_admission,
        target_relative_path=target_relative_path,
    )

    restoration = run_agentic_de_local_effect_v57b(
        repo_root_path=root,
        domain_packet_path=domain_packet_path,
        morph_ir_path=morph_ir_path,
        interaction_contract_path=interaction_contract_path,
        action_proposal_path=action_proposal_path,
        v56a_checkpoint_path=v56a_checkpoint_path,
        v56a_diagnostics_path=v56a_diagnostics_path,
        v56a_conformance_path=v56a_conformance_path,
        v56b_lane_drift_path=v56b_lane_drift_path,
        v56b_action_class_taxonomy_path=v56b_action_class_taxonomy_path,
        v56b_runtime_state_path=v56b_runtime_state_path,
        v56b_action_ticket_path=v56b_action_ticket_path,
        v56b_diagnostics_path=v56b_diagnostics_path,
        v56b_conformance_path=v56b_conformance_path,
        v56c_lane_drift_path=v56c_lane_drift_path,
        v56c_runtime_harvest_path=v56c_runtime_harvest_path,
        v56c_governance_calibration_path=v56c_governance_calibration_path,
        v56c_migration_decision_path=v56c_migration_decision_path,
        v57a_lane_drift_path=v57a_lane_drift_path,
        v57a_observation_path=v57a_observation_path,
        v57a_local_effect_conformance_path=v57a_local_effect_conformance_path,
        lane_drift_path=v57b_lane_drift_path,
        v56a_evidence_path=v56a_evidence_path,
        v56b_evidence_path=v56b_evidence_path,
        v56c_evidence_path=v56c_evidence_path,
        v57a_evidence_path=v57a_evidence_path,
        materialized_observed_content_text=materialized_observed_content_text,
        expected_relative_paths=expected_relative_paths,
        materialize_observed_effect=materialize_observed_effect,
    )
    if restoration.ticket_ref != v58a_handoff.action_ticket_ref:
        raise ValueError("V58-B restoration must preserve the shipped V58-A ticket lineage")
    if restoration.observation_ref != v58a_reintegration.observation_ref:
        raise ValueError("V58-B restoration must preserve the shipped V58-A observation lineage")
    if restoration.conformance_ref != v58a_reintegration.local_effect_conformance_ref:
        raise ValueError("V58-B restoration must preserve the shipped V58-A conformance lineage")
    if len(restoration.restoration_observed_write_set) != 1:
        raise ValueError("V58-B requires exactly one observed restoration target")
    expected_restoration_relative_path = (
        DESIGNATED_LOCAL_EFFECT_SANDBOX_ROOT / target_relative_path
    ).as_posix()
    if (
        restoration.restoration_observed_write_set[0].relative_path
        != expected_restoration_relative_path
    ):
        raise ValueError("V58-B restoration path must preserve the selected live target")

    base_evidence_refs = [
        _render_input_ref(repo_root_path=root, path=domain_packet_path),
        _render_input_ref(repo_root_path=root, path=morph_ir_path),
        _render_input_ref(repo_root_path=root, path=interaction_contract_path),
        _render_input_ref(repo_root_path=root, path=action_proposal_path),
        _render_input_ref(repo_root_path=root, path=v56a_checkpoint_path),
        _render_input_ref(repo_root_path=root, path=v56a_diagnostics_path),
        _render_input_ref(repo_root_path=root, path=v56a_conformance_path),
        _render_input_ref(repo_root_path=root, path=v56b_action_class_taxonomy_path),
        _render_input_ref(repo_root_path=root, path=v56b_runtime_state_path),
        _render_input_ref(repo_root_path=root, path=v56b_action_ticket_path),
        _render_input_ref(repo_root_path=root, path=v56b_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56b_diagnostics_path),
        _render_input_ref(repo_root_path=root, path=v56b_conformance_path),
        _render_input_ref(repo_root_path=root, path=v56c_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56c_runtime_harvest_path),
        _render_input_ref(repo_root_path=root, path=v56c_governance_calibration_path),
        _render_input_ref(repo_root_path=root, path=v56c_migration_decision_path),
        _render_input_ref(repo_root_path=root, path=v57a_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v57a_observation_path),
        _render_input_ref(repo_root_path=root, path=v57a_local_effect_conformance_path),
        _render_input_ref(repo_root_path=root, path=v57b_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v57b_restoration_path),
        _render_input_ref(repo_root_path=root, path=v57c_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v57c_hardening_path),
        _render_input_ref(repo_root_path=root, path=v58a_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v58a_admission_path),
        _render_input_ref(repo_root_path=root, path=v58a_handoff_path),
        _render_input_ref(repo_root_path=root, path=v58a_reintegration_path),
        _render_input_ref(repo_root_path=root, path=lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56a_evidence_path),
        _render_input_ref(repo_root_path=root, path=v56b_evidence_path),
        _render_input_ref(repo_root_path=root, path=v56c_evidence_path),
        _render_input_ref(repo_root_path=root, path=v57a_evidence_path),
        _render_input_ref(repo_root_path=root, path=v57b_evidence_path),
        _render_input_ref(repo_root_path=root, path=v57c_evidence_path),
        _render_input_ref(repo_root_path=root, path=v58a_evidence_path),
        *_snapshot_observability_refs(
            repo_root_path=root,
            live_turn_snapshot=live_turn_snapshot,
        ),
        restoration.restoration_pre_state_ref,
        restoration.restoration_post_state_ref,
    ]
    live_restoration_handoff = _build_v58b_live_restoration_handoff_record(
        live_turn_snapshot=live_turn_snapshot,
        admission=v58a_admission,
        handoff=v58a_handoff,
        prior_reintegration=v58a_reintegration,
        restoration=restoration,
        restoration_time_session_capability_snapshot=restoration_time_session_capability_snapshot,
        restoration_time_approval_posture_snapshot=restoration_time_approval_posture_snapshot,
        target_relative_path=target_relative_path,
        evidence_refs=base_evidence_refs,
    )
    restoration_reintegration = _build_v58b_live_restoration_reintegration_report(
        live_turn_snapshot=live_turn_snapshot,
        admission=v58a_admission,
        live_restoration_handoff=live_restoration_handoff,
        restoration=restoration,
        evidence_refs=base_evidence_refs,
    )
    return live_restoration_handoff, restoration, restoration_reintegration


def run_agentic_de_live_harness_v58c(
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
    v56c_lane_drift_path: Path = DEFAULT_V56C_LANE_DRIFT_PATH,
    v56c_runtime_harvest_path: Path = DEFAULT_V56C_RUNTIME_HARVEST_PATH,
    v56c_governance_calibration_path: Path = DEFAULT_V56C_GOVERNANCE_CALIBRATION_PATH,
    v56c_migration_decision_path: Path = DEFAULT_V56C_MIGRATION_DECISION_PATH,
    v57a_lane_drift_path: Path = DEFAULT_V57A_LANE_DRIFT_PATH,
    v57a_observation_path: Path = DEFAULT_V57A_OBSERVATION_PATH,
    v57a_local_effect_conformance_path: Path = DEFAULT_V57A_LOCAL_EFFECT_CONFORMANCE_PATH,
    v57b_lane_drift_path: Path = DEFAULT_V57B_LANE_DRIFT_PATH,
    v57b_restoration_path: Path = DEFAULT_V57B_RESTORATION_PATH,
    v57c_lane_drift_path: Path = DEFAULT_V57C_LANE_DRIFT_PATH,
    v57c_hardening_path: Path = DEFAULT_V57C_HARDENING_PATH,
    v58a_lane_drift_path: Path = DEFAULT_V58A_LANE_DRIFT_PATH,
    v58a_admission_path: Path = DEFAULT_V58A_LIVE_TURN_ADMISSION_PATH,
    v58a_handoff_path: Path = DEFAULT_V58A_LIVE_TURN_HANDOFF_PATH,
    v58a_reintegration_path: Path = DEFAULT_V58A_LIVE_TURN_REINTEGRATION_PATH,
    v58b_lane_drift_path: Path = DEFAULT_V58B_LANE_DRIFT_PATH,
    v58b_live_restoration_handoff_path: Path = DEFAULT_V58B_LIVE_RESTORATION_HANDOFF_PATH,
    v58b_live_restoration_reintegration_path: Path = (
        DEFAULT_V58B_LIVE_RESTORATION_REINTEGRATION_PATH
    ),
    v58c_lane_drift_path: Path = DEFAULT_V58C_LANE_DRIFT_PATH,
    v56a_evidence_path: Path = DEFAULT_V56C_V56A_EVIDENCE_PATH,
    v56b_evidence_path: Path = DEFAULT_V56C_V56B_EVIDENCE_PATH,
    v56c_evidence_path: Path = DEFAULT_V57A_V56C_EVIDENCE_PATH,
    v57a_evidence_path: Path = DEFAULT_V57A_EVIDENCE_PATH,
    v57b_evidence_path: Path = DEFAULT_V57B_EVIDENCE_PATH,
    v57c_evidence_path: Path = DEFAULT_V57C_EVIDENCE_PATH,
    v58a_evidence_path: Path = DEFAULT_V58A_EVIDENCE_PATH,
    v58b_evidence_path: Path = DEFAULT_V58B_EVIDENCE_PATH,
) -> AgenticDeLiveHarnessHardeningRegister:
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
    v56c_lane_drift_path = _resolve_path(repo_root_path=root, path=v56c_lane_drift_path)
    v56c_runtime_harvest_path = _resolve_path(repo_root_path=root, path=v56c_runtime_harvest_path)
    v56c_governance_calibration_path = _resolve_path(
        repo_root_path=root, path=v56c_governance_calibration_path
    )
    v56c_migration_decision_path = _resolve_path(
        repo_root_path=root, path=v56c_migration_decision_path
    )
    v57a_lane_drift_path = _resolve_path(repo_root_path=root, path=v57a_lane_drift_path)
    v57a_observation_path = _resolve_path(repo_root_path=root, path=v57a_observation_path)
    v57a_local_effect_conformance_path = _resolve_path(
        repo_root_path=root, path=v57a_local_effect_conformance_path
    )
    v57b_lane_drift_path = _resolve_path(repo_root_path=root, path=v57b_lane_drift_path)
    v57b_restoration_path = _resolve_path(repo_root_path=root, path=v57b_restoration_path)
    v57c_lane_drift_path = _resolve_path(repo_root_path=root, path=v57c_lane_drift_path)
    v57c_hardening_path = _resolve_path(repo_root_path=root, path=v57c_hardening_path)
    v58a_lane_drift_path = _resolve_path(repo_root_path=root, path=v58a_lane_drift_path)
    v58a_admission_path = _resolve_path(repo_root_path=root, path=v58a_admission_path)
    v58a_handoff_path = _resolve_path(repo_root_path=root, path=v58a_handoff_path)
    v58a_reintegration_path = _resolve_path(
        repo_root_path=root, path=v58a_reintegration_path
    )
    v58b_lane_drift_path = _resolve_path(repo_root_path=root, path=v58b_lane_drift_path)
    v58b_live_restoration_handoff_path = _resolve_path(
        repo_root_path=root,
        path=v58b_live_restoration_handoff_path,
    )
    v58b_live_restoration_reintegration_path = _resolve_path(
        repo_root_path=root,
        path=v58b_live_restoration_reintegration_path,
    )
    v58c_lane_drift_path = _resolve_path(repo_root_path=root, path=v58c_lane_drift_path)
    v56a_evidence_path = _resolve_path(repo_root_path=root, path=v56a_evidence_path)
    v56b_evidence_path = _resolve_path(repo_root_path=root, path=v56b_evidence_path)
    v56c_evidence_path = _resolve_path(repo_root_path=root, path=v56c_evidence_path)
    v57a_evidence_path = _resolve_path(repo_root_path=root, path=v57a_evidence_path)
    v57b_evidence_path = _resolve_path(repo_root_path=root, path=v57b_evidence_path)
    v57c_evidence_path = _resolve_path(repo_root_path=root, path=v57c_evidence_path)
    v58a_evidence_path = _resolve_path(repo_root_path=root, path=v58a_evidence_path)
    v58b_evidence_path = _resolve_path(repo_root_path=root, path=v58b_evidence_path)

    _validate_v58c_lane_drift_record(load_lane_drift_record(v58c_lane_drift_path))
    _validate_v58b_lane_drift_record(load_lane_drift_record(v58b_lane_drift_path))
    _validate_v58a_lane_drift_record(load_lane_drift_record(v58a_lane_drift_path))
    _validate_v57c_lane_drift_record(load_lane_drift_record(v57c_lane_drift_path))
    _validate_v57b_lane_drift_record(load_lane_drift_record(v57b_lane_drift_path))
    _validate_v57a_lane_drift_record(load_lane_drift_record(v57a_lane_drift_path))
    _validate_v56b_lane_drift_record(load_lane_drift_record(v56b_lane_drift_path))
    _validate_v56c_lane_drift_record(load_lane_drift_record(v56c_lane_drift_path))
    _validate_v56a_evidence_payload(
        _load_json_object(v56a_evidence_path, error_label="V56-A evidence")
    )
    _validate_v56b_evidence_payload(
        _load_json_object(v56b_evidence_path, error_label="V56-B evidence")
    )
    _validate_v56c_evidence_payload(
        _load_json_object(v56c_evidence_path, error_label="V56-C evidence")
    )
    _validate_v57a_evidence_payload(
        _load_json_object(v57a_evidence_path, error_label="V57-A evidence")
    )
    _validate_v57b_evidence_payload(
        _load_json_object(v57b_evidence_path, error_label="V57-B evidence")
    )
    _validate_v57c_evidence_payload(
        _load_json_object(v57c_evidence_path, error_label="V57-C evidence")
    )
    _validate_v58a_evidence_payload(
        _load_json_object(v58a_evidence_path, error_label="V58-A evidence")
    )
    _validate_v58b_evidence_payload(
        _load_json_object(v58b_evidence_path, error_label="V58-B evidence")
    )

    packet = load_domain_packet(domain_packet_path)
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
    v56c_harvest = load_runtime_harvest_record(v56c_runtime_harvest_path)
    v56c_governance = load_governance_calibration_register(v56c_governance_calibration_path)
    v56c_migration = load_migration_decision_register(v56c_migration_decision_path)
    v57a_observation = load_local_effect_observation_record(v57a_observation_path)
    v57a_local_effect_conformance = load_local_effect_conformance_report(
        v57a_local_effect_conformance_path
    )
    v57b_restoration = load_local_effect_restoration_record(v57b_restoration_path)
    v57c_hardening = load_local_effect_hardening_register(v57c_hardening_path)
    v58a_admission = load_live_turn_admission_record(v58a_admission_path)
    v58a_handoff = load_live_turn_handoff_record(v58a_handoff_path)
    v58a_reintegration = load_live_turn_reintegration_report(v58a_reintegration_path)
    v58b_live_restoration_handoff = load_live_restoration_handoff_record(
        v58b_live_restoration_handoff_path
    )
    v58b_live_restoration_reintegration = load_live_restoration_reintegration_report(
        v58b_live_restoration_reintegration_path
    )

    _validate_v56a_reference_surfaces(
        domain_packet=packet,
        morph_ir=morph_ir,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        diagnostics=v56a_diagnostics,
        conformance=v56a_conformance,
    )
    _validate_v56b_reference_surfaces(
        domain_packet=packet,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        taxonomy=v56b_taxonomy,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        diagnostics=v56b_diagnostics,
        conformance=v56b_conformance,
    )
    _validate_v57a_reference_surfaces(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        taxonomy=v56b_taxonomy,
        harvest=v56c_harvest,
        governance=v56c_governance,
        migration=v56c_migration,
    )
    _validate_v57a_local_effect_surfaces(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        harvest=v56c_harvest,
        observation=v57a_observation,
        conformance=v57a_local_effect_conformance,
    )
    _validate_v57b_local_effect_restoration_surface(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        harvest=v56c_harvest,
        observation=v57a_observation,
        conformance=v57a_local_effect_conformance,
        restoration=v57b_restoration,
    )
    _validate_v57c_local_effect_hardening_surface(
        observation=v57a_observation,
        conformance=v57a_local_effect_conformance,
        restoration=v57b_restoration,
        hardening=v57c_hardening,
    )
    _validate_v58a_live_turn_surfaces(
        live_turn_snapshot=None,
        admission=v58a_admission,
        handoff=v58a_handoff,
        reintegration=v58a_reintegration,
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        ticket=v56b_ticket,
        observation=v57a_observation,
        conformance=v57a_local_effect_conformance,
        target_relative_path=_derived_restore_target_relative_path(v57a_observation),
    )
    _validate_v58b_live_restoration_surfaces(
        admission=v58a_admission,
        handoff=v58a_handoff,
        turn_reintegration=v58a_reintegration,
        restoration=v57b_restoration,
        live_restoration_handoff=v58b_live_restoration_handoff,
        live_restoration_reintegration=v58b_live_restoration_reintegration,
        ticket=v56b_ticket,
        observation=v57a_observation,
    )

    evidence_refs = [
        _render_input_ref(repo_root_path=root, path=domain_packet_path),
        _render_input_ref(repo_root_path=root, path=morph_ir_path),
        _render_input_ref(repo_root_path=root, path=interaction_contract_path),
        _render_input_ref(repo_root_path=root, path=action_proposal_path),
        _render_input_ref(repo_root_path=root, path=v56a_checkpoint_path),
        _render_input_ref(repo_root_path=root, path=v56a_diagnostics_path),
        _render_input_ref(repo_root_path=root, path=v56a_conformance_path),
        _render_input_ref(repo_root_path=root, path=v56b_action_class_taxonomy_path),
        _render_input_ref(repo_root_path=root, path=v56b_runtime_state_path),
        _render_input_ref(repo_root_path=root, path=v56b_action_ticket_path),
        _render_input_ref(repo_root_path=root, path=v56b_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56b_diagnostics_path),
        _render_input_ref(repo_root_path=root, path=v56b_conformance_path),
        _render_input_ref(repo_root_path=root, path=v56c_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56c_runtime_harvest_path),
        _render_input_ref(repo_root_path=root, path=v56c_governance_calibration_path),
        _render_input_ref(repo_root_path=root, path=v56c_migration_decision_path),
        _render_input_ref(repo_root_path=root, path=v57a_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v57a_observation_path),
        _render_input_ref(repo_root_path=root, path=v57a_local_effect_conformance_path),
        _render_input_ref(repo_root_path=root, path=v57b_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v57b_restoration_path),
        _render_input_ref(repo_root_path=root, path=v57c_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v57c_hardening_path),
        _render_input_ref(repo_root_path=root, path=v58a_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v58a_admission_path),
        _render_input_ref(repo_root_path=root, path=v58a_handoff_path),
        _render_input_ref(repo_root_path=root, path=v58a_reintegration_path),
        _render_input_ref(repo_root_path=root, path=v58b_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v58b_live_restoration_handoff_path),
        _render_input_ref(repo_root_path=root, path=v58b_live_restoration_reintegration_path),
        _render_input_ref(repo_root_path=root, path=v58c_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56a_evidence_path),
        _render_input_ref(repo_root_path=root, path=v56b_evidence_path),
        _render_input_ref(repo_root_path=root, path=v56c_evidence_path),
        _render_input_ref(repo_root_path=root, path=v57a_evidence_path),
        _render_input_ref(repo_root_path=root, path=v57b_evidence_path),
        _render_input_ref(repo_root_path=root, path=v57c_evidence_path),
        _render_input_ref(repo_root_path=root, path=v58a_evidence_path),
        _render_input_ref(repo_root_path=root, path=v58b_evidence_path),
    ]

    return _build_v58c_live_harness_hardening_register(
        admission=v58a_admission,
        handoff=v58a_handoff,
        turn_reintegration=v58a_reintegration,
        observation=v57a_observation,
        conformance=v57a_local_effect_conformance,
        restoration=v57b_restoration,
        live_restoration_handoff=v58b_live_restoration_handoff,
        live_restoration_reintegration=v58b_live_restoration_reintegration,
        evidence_refs=evidence_refs,
    )


def run_agentic_de_workspace_continuity_v59a(
    *,
    live_turn_snapshot: CopilotTurnSnapshot,
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
    v56c_lane_drift_path: Path = DEFAULT_V56C_LANE_DRIFT_PATH,
    v56c_runtime_harvest_path: Path = DEFAULT_V56C_RUNTIME_HARVEST_PATH,
    v56c_governance_calibration_path: Path = DEFAULT_V56C_GOVERNANCE_CALIBRATION_PATH,
    v56c_migration_decision_path: Path = DEFAULT_V56C_MIGRATION_DECISION_PATH,
    lane_drift_path: Path = DEFAULT_V59A_LANE_DRIFT_PATH,
    v58c_evidence_path: Path = DEFAULT_V58C_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
    payload_text: str = DEFAULT_WORKSPACE_CONTINUITY_PAYLOAD_TEXT,
    expected_relative_paths: tuple[str, ...] | None = None,
    expected_content_contains: str | None = (
        "bounded persistent workspace continuity patch candidate"
    ),
) -> tuple[
    AgenticDeWorkspaceContinuityRegionDeclaration,
    AgenticDeWorkspaceContinuityAdmissionRecord,
    AgenticDeWorkspaceOccupancyReport,
    AgenticDeLiveTurnAdmissionRecord,
    AgenticDeLiveTurnHandoffRecord,
    AgenticDeLocalEffectObservationRecord,
    AgenticDeLocalEffectConformanceReport,
    AgenticDeLiveTurnReintegrationReport,
    AgenticDeWorkspaceContinuityReintegrationReport,
]:
    if repo_root_path is None:
        root = repo_root(anchor=Path(__file__)).resolve()
    else:
        if repo_root_path.exists() and repo_root_path.is_symlink():
            raise ValueError("repository root may not be a symlink for V59-A continuity")
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
        repo_root_path=root,
        path=v56b_action_class_taxonomy_path,
    )
    v56b_runtime_state_path = _resolve_path(repo_root_path=root, path=v56b_runtime_state_path)
    v56b_action_ticket_path = _resolve_path(repo_root_path=root, path=v56b_action_ticket_path)
    v56b_diagnostics_path = _resolve_path(repo_root_path=root, path=v56b_diagnostics_path)
    v56b_conformance_path = _resolve_path(repo_root_path=root, path=v56b_conformance_path)
    v56c_lane_drift_path = _resolve_path(repo_root_path=root, path=v56c_lane_drift_path)
    v56c_runtime_harvest_path = _resolve_path(repo_root_path=root, path=v56c_runtime_harvest_path)
    v56c_governance_calibration_path = _resolve_path(
        repo_root_path=root,
        path=v56c_governance_calibration_path,
    )
    v56c_migration_decision_path = _resolve_path(
        repo_root_path=root,
        path=v56c_migration_decision_path,
    )
    lane_drift_path = _resolve_path(repo_root_path=root, path=lane_drift_path)
    v58c_evidence_path = _resolve_path(repo_root_path=root, path=v58c_evidence_path)

    _validate_v59a_lane_drift_record(load_lane_drift_record(lane_drift_path))
    _validate_v56b_lane_drift_record(load_lane_drift_record(v56b_lane_drift_path))
    _validate_v56c_lane_drift_record(load_lane_drift_record(v56c_lane_drift_path))
    _validate_v58c_evidence_payload(
        _load_json_object(v58c_evidence_path, error_label="V58-C evidence")
    )

    packet = load_domain_packet(domain_packet_path)
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
    v56c_harvest = load_runtime_harvest_record(v56c_runtime_harvest_path)
    v56c_governance = load_governance_calibration_register(v56c_governance_calibration_path)
    v56c_migration = load_migration_decision_register(v56c_migration_decision_path)

    _validate_v56a_reference_surfaces(
        domain_packet=packet,
        morph_ir=morph_ir,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        diagnostics=v56a_diagnostics,
        conformance=v56a_conformance,
    )
    _validate_v56b_reference_surfaces(
        domain_packet=packet,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        taxonomy=v56b_taxonomy,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        diagnostics=v56b_diagnostics,
        conformance=v56b_conformance,
    )
    _validate_v57a_reference_surfaces(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        taxonomy=v56b_taxonomy,
        harvest=v56c_harvest,
        governance=v56c_governance,
        migration=v56c_migration,
    )

    base_evidence_refs = [
        _render_input_ref(repo_root_path=root, path=domain_packet_path),
        _render_input_ref(repo_root_path=root, path=morph_ir_path),
        _render_input_ref(repo_root_path=root, path=interaction_contract_path),
        _render_input_ref(repo_root_path=root, path=action_proposal_path),
        _render_input_ref(repo_root_path=root, path=v56a_checkpoint_path),
        _render_input_ref(repo_root_path=root, path=v56a_diagnostics_path),
        _render_input_ref(repo_root_path=root, path=v56a_conformance_path),
        _render_input_ref(repo_root_path=root, path=v56b_action_class_taxonomy_path),
        _render_input_ref(repo_root_path=root, path=v56b_runtime_state_path),
        _render_input_ref(repo_root_path=root, path=v56b_action_ticket_path),
        _render_input_ref(repo_root_path=root, path=v56b_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56b_diagnostics_path),
        _render_input_ref(repo_root_path=root, path=v56b_conformance_path),
        _render_input_ref(repo_root_path=root, path=v56c_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56c_runtime_harvest_path),
        _render_input_ref(repo_root_path=root, path=v56c_governance_calibration_path),
        _render_input_ref(repo_root_path=root, path=v56c_migration_decision_path),
        _render_input_ref(repo_root_path=root, path=lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v58c_evidence_path),
    ]
    continuity_region = _build_v59a_workspace_continuity_region_declaration(
        evidence_refs=base_evidence_refs
    )
    live_turn_admission = _build_v59a_live_turn_admission_record(
        repo_root_path=root,
        live_turn_snapshot=live_turn_snapshot,
        target_relative_path=target_relative_path,
        evidence_refs=[continuity_region.continuity_region_id, *base_evidence_refs],
    )
    if live_turn_admission.admission_verdict != "admitted":
        raise ValueError("V59-A live-turn admission must resolve to admitted")
    live_turn_handoff = _build_v59a_live_turn_handoff_record(
        admission=live_turn_admission,
        domain_packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        ticket=v56b_ticket,
        target_relative_path=target_relative_path,
        evidence_refs=[continuity_region.continuity_region_id, *base_evidence_refs],
    )

    pre_state = snapshot_workspace_continuity_state(
        repo_root_path=root,
        target_relative_path=target_relative_path,
        snapshot_name="reference_pre_state.json",
    )
    pre_state_summary = (
        f"target_present={'true' if pre_state.target_exists else 'false'};"
        f"non_target_context_count={len(pre_state.non_target_context_paths)};"
        f"marker_present={'true' if pre_state.marker_ref else 'false'}"
    )
    continuity_admission = _build_v59a_workspace_continuity_admission_record(
        repo_root_path=root,
        admission=live_turn_admission,
        handoff=live_turn_handoff,
        region=continuity_region,
        pre_state_summary=pre_state_summary,
        evidence_refs=[pre_state.snapshot_ref, *base_evidence_refs],
    )
    if continuity_admission.continuity_verdict != "admitted":
        raise ValueError("V59-A continuity admission must resolve to admitted")

    occupancy_assessment = classify_workspace_occupancy(state=pre_state)
    occupancy_report = _build_v59a_workspace_occupancy_report(
        continuity_admission=continuity_admission,
        target_relative_path=target_relative_path,
        occupancy_assessment=occupancy_assessment,
        evidence_refs=[pre_state.snapshot_ref, *base_evidence_refs],
    )
    if occupancy_report.occupancy_verdict != "unoccupied":
        raise ValueError("V59-A create_new continuity path requires unoccupied target")

    observed_effect = observe_workspace_continuity_create_new_effect(
        repo_root_path=root,
        pre_state=pre_state,
        target_relative_path=target_relative_path,
        payload_text=payload_text,
        expected_relative_paths=expected_relative_paths,
        expected_content_contains=expected_content_contains,
    )
    observation_evidence_refs = [
        continuity_region.continuity_region_id,
        continuity_admission.continuity_admission_id,
        occupancy_report.occupancy_report_id,
        pre_state.snapshot_ref,
        observed_effect.post_state_ref,
        *base_evidence_refs,
    ]
    observation = _build_v59a_local_effect_observation_record(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        harvest=v56c_harvest,
        selected_local_write_kind="create_new",
        declared_continuity_root=observed_effect.declared_continuity_root,
        pre_state_ref=observed_effect.pre_state_ref,
        observed_write_set=observed_effect.observed_write_set,
        post_state_ref=observed_effect.post_state_ref,
        observed_effect=observed_effect.observed_effect,
        observation_outcome=observed_effect.observation_outcome,
        boundedness_verdict=observed_effect.boundedness_verdict,
        boundedness_note=observed_effect.boundedness_note,
        evidence_refs=observation_evidence_refs,
    )
    conformance = build_local_effect_conformance_report(
        target_arc=V59A_TARGET_ARC,
        target_path=V59A_TARGET_PATH,
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        harvest=v56c_harvest,
        observation=observation,
        evidence_refs=observation_evidence_refs,
    )
    live_turn_reintegration = _build_v59a_live_turn_reintegration_report(
        live_turn_snapshot=live_turn_snapshot,
        admission=live_turn_admission,
        handoff=live_turn_handoff,
        observation=observation,
        conformance=conformance,
        evidence_refs=[
            continuity_region.continuity_region_id,
            continuity_admission.continuity_admission_id,
            occupancy_report.occupancy_report_id,
            *base_evidence_refs,
        ],
    )
    governed_marker_ref: str | None = None
    if (
        observation.observation_outcome == "bounded_effect_observed"
        and conformance.conformance_status == "effect_aligned"
        and live_turn_reintegration.reintegration_status == "reintegrated"
    ):
        governed_marker_ref = write_workspace_governed_lineage_marker(
            repo_root_path=root,
            target_relative_path=target_relative_path,
            governed_observation_ref=observation.observation_id,
            target_content_sha256=observation.observed_write_set[0].content_sha256,
        )
    continuity_reintegration = _build_v59a_workspace_continuity_reintegration_report(
        live_turn_snapshot=live_turn_snapshot,
        live_turn_reintegration=live_turn_reintegration,
        continuity_admission=continuity_admission,
        occupancy=occupancy_report,
        observation=observation,
        conformance=conformance,
        continuity_region_state_summary_after_act=observed_effect.post_state_summary,
        evidence_refs=[
            continuity_region.continuity_region_id,
            observed_effect.post_state_ref,
            *([governed_marker_ref] if governed_marker_ref is not None else []),
            *base_evidence_refs,
        ],
    )
    return (
        continuity_region,
        continuity_admission,
        occupancy_report,
        live_turn_admission,
        live_turn_handoff,
        observation,
        conformance,
        live_turn_reintegration,
        continuity_reintegration,
    )


def _validate_v59a_workspace_continuity_surfaces(
    *,
    packet: AgenticDeDomainPacket,
    proposal: AgenticDeActionProposal,
    checkpoint: AgenticDeMembraneCheckpoint,
    ticket: AgenticDeActionTicket,
    continuity_region: AgenticDeWorkspaceContinuityRegionDeclaration,
    continuity_admission: AgenticDeWorkspaceContinuityAdmissionRecord,
    occupancy: AgenticDeWorkspaceOccupancyReport,
    live_turn_admission: AgenticDeLiveTurnAdmissionRecord,
    live_turn_handoff: AgenticDeLiveTurnHandoffRecord,
    observation: AgenticDeLocalEffectObservationRecord,
    conformance: AgenticDeLocalEffectConformanceReport,
    live_turn_reintegration: AgenticDeLiveTurnReintegrationReport,
    continuity_reintegration: AgenticDeWorkspaceContinuityReintegrationReport,
    target_relative_path: str,
) -> None:
    if (
        continuity_region.target_arc != V59A_TARGET_ARC
        or continuity_region.target_path != V59A_TARGET_PATH
    ):
        raise ValueError("V59-B requires the shipped V59-A continuity region surface")
    if (
        continuity_admission.target_arc != V59A_TARGET_ARC
        or continuity_admission.target_path != V59A_TARGET_PATH
    ):
        raise ValueError("V59-B requires the shipped V59-A continuity admission surface")
    if occupancy.target_arc != V59A_TARGET_ARC or occupancy.target_path != V59A_TARGET_PATH:
        raise ValueError("V59-B requires the shipped V59-A occupancy surface")
    if (
        continuity_reintegration.target_arc != V59A_TARGET_ARC
        or continuity_reintegration.target_path != V59A_TARGET_PATH
    ):
        raise ValueError("V59-B requires the shipped V59-A continuity reintegration surface")
    if (
        live_turn_admission.target_arc != V59A_TARGET_ARC
        or live_turn_admission.target_path != V59A_TARGET_PATH
    ):
        raise ValueError("V59-B requires the shipped V59-A live-turn admission surface")
    if (
        live_turn_handoff.target_arc != V59A_TARGET_ARC
        or live_turn_handoff.target_path != V59A_TARGET_PATH
    ):
        raise ValueError("V59-B requires the shipped V59-A live-turn handoff surface")
    if (
        live_turn_reintegration.target_arc != V59A_TARGET_ARC
        or live_turn_reintegration.target_path != V59A_TARGET_PATH
    ):
        raise ValueError("V59-B requires the shipped V59-A live-turn reintegration surface")
    if (
        continuity_region.declared_continuity_root
        != DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix()
    ):
        raise ValueError("V59-B requires the shipped V59-A declared continuity root")
    if continuity_admission.live_turn_admission_ref != live_turn_admission.admission_id:
        raise ValueError(
            "V59-A continuity admission does not bind the provided live-turn admission"
        )
    if continuity_admission.live_turn_handoff_ref != live_turn_handoff.handoff_id:
        raise ValueError("V59-A continuity admission does not bind the provided live-turn handoff")
    if (
        continuity_admission.continuity_region_declaration_ref
        != continuity_region.continuity_region_id
    ):
        raise ValueError("V59-A continuity admission does not bind the provided region")
    if continuity_admission.continuity_verdict != "admitted":
        raise ValueError("V59-B requires one prior admitted V59-A continuity admission")
    if occupancy.continuity_admission_ref != continuity_admission.continuity_admission_id:
        raise ValueError("V59-A occupancy does not bind the provided continuity admission")
    if occupancy.target_relative_path != target_relative_path:
        raise ValueError("V59-B requires the shipped V59-A selected target relative path")
    if occupancy.occupancy_verdict != "unoccupied":
        raise ValueError("V59-B requires the shipped V59-A unoccupied starter occupancy")
    if live_turn_handoff.turn_admission_ref != live_turn_admission.admission_id:
        raise ValueError("V59-A handoff does not bind the provided admission")
    if live_turn_handoff.domain_packet_ref != packet.packet_id:
        raise ValueError("V59-A handoff does not bind the provided domain packet")
    if live_turn_handoff.action_proposal_ref != proposal.proposal_id:
        raise ValueError("V59-A handoff does not bind the provided action proposal")
    if live_turn_handoff.checkpoint_ref != checkpoint.checkpoint_id:
        raise ValueError("V59-A handoff does not bind the provided checkpoint")
    if live_turn_handoff.action_ticket_ref != ticket.ticket_id:
        raise ValueError("V59-A handoff does not bind the provided action ticket")
    if live_turn_handoff.target_relative_path != target_relative_path:
        raise ValueError("V59-B requires the shipped V59-A selected target")
    if observation.target_arc != V59A_TARGET_ARC or observation.target_path != V59A_TARGET_PATH:
        raise ValueError("V59-B requires the shipped V59-A observation surface")
    if observation.ticket_ref != ticket.ticket_id:
        raise ValueError("V59-A observation does not bind the provided ticket")
    if observation.designated_sandbox_root != continuity_region.declared_continuity_root:
        raise ValueError("V59-A observation must preserve the declared continuity root")
    if _derived_restore_target_relative_path(observation) != target_relative_path:
        raise ValueError("V59-A observation must preserve the shipped selected target")
    if conformance.target_arc != V59A_TARGET_ARC or conformance.target_path != V59A_TARGET_PATH:
        raise ValueError("V59-B requires the shipped V59-A conformance surface")
    if conformance.observation_ref != observation.observation_id:
        raise ValueError("V59-A conformance does not bind the provided observation")
    if live_turn_reintegration.turn_admission_ref != live_turn_admission.admission_id:
        raise ValueError("V59-A reintegration does not bind the provided admission")
    if live_turn_reintegration.turn_handoff_ref != live_turn_handoff.handoff_id:
        raise ValueError("V59-A reintegration does not bind the provided handoff")
    if live_turn_reintegration.observation_ref != observation.observation_id:
        raise ValueError("V59-A reintegration does not bind the provided observation")
    if live_turn_reintegration.local_effect_conformance_ref != conformance.report_id:
        raise ValueError("V59-A reintegration does not bind the provided conformance")
    if live_turn_reintegration.reintegration_status != "reintegrated":
        raise ValueError("V59-B requires one prior reintegrated V59-A live turn")
    if live_turn_reintegration.reintegration_certificate_ref_or_equivalent is None:
        raise ValueError("V59-B requires witness-bearing V59-A live reintegration")
    if (
        continuity_reintegration.live_turn_reintegration_ref
        != live_turn_reintegration.report_id
    ):
        raise ValueError(
            "V59-A continuity reintegration does not bind the provided live reintegration"
        )
    if (
        continuity_reintegration.continuity_admission_ref
        != continuity_admission.continuity_admission_id
    ):
        raise ValueError(
            "V59-A continuity reintegration does not bind the provided continuity admission"
        )
    if continuity_reintegration.occupancy_report_ref != occupancy.occupancy_report_id:
        raise ValueError("V59-A continuity reintegration does not bind the provided occupancy")
    if continuity_reintegration.observation_ref != observation.observation_id:
        raise ValueError("V59-A continuity reintegration does not bind the provided observation")
    if (
        continuity_reintegration.local_effect_conformance_ref
        != conformance.report_id
    ):
        raise ValueError("V59-A continuity reintegration does not bind the provided conformance")
    if continuity_reintegration.continuity_reintegration_status != "reintegrated":
        raise ValueError("V59-B requires one prior reintegrated V59-A continuity report")
    if continuity_reintegration.continuity_witness_certificate_ref_or_equivalent is None:
        raise ValueError("V59-B requires witness-bearing V59-A continuity reintegration")


def _validate_v59b_restoration_time_continuation(
    *,
    repo_root_path: Path,
    live_turn_snapshot: CopilotTurnSnapshot,
    live_turn_admission: AgenticDeLiveTurnAdmissionRecord,
    continuity_admission: AgenticDeWorkspaceContinuityAdmissionRecord,
    target_relative_path: str,
) -> tuple[str, str, str]:
    if live_turn_snapshot.session_id != live_turn_admission.live_session_id:
        raise ValueError("V59-B requires same-session continuation from the shipped V59-A turn")
    if live_turn_snapshot.selected_turn_id != live_turn_admission.live_turn_id:
        raise ValueError("V59-B requires same-turn continuation from the shipped V59-A turn")
    current_capability_snapshot = _session_capability_snapshot(live_turn_snapshot)
    current_approval_posture_snapshot = _approval_posture_snapshot(live_turn_snapshot)
    if current_capability_snapshot != live_turn_admission.session_capability_snapshot:
        raise ValueError(
            "V59-B restoration-time session capability snapshot must match the admitted "
            "V59-A continuation posture"
        )
    if current_approval_posture_snapshot != live_turn_admission.approval_posture_snapshot:
        raise ValueError(
            "V59-B restoration-time approval posture snapshot must match the admitted "
            "V59-A continuation posture"
        )
    if continuity_admission.continuity_verdict != "admitted":
        raise ValueError("V59-B requires an admitted V59-A continuity lineage before restore")
    cwd_resolved = _resolve_snapshot_cwd_path(
        repo_root_path=repo_root_path,
        raw_value=live_turn_snapshot.cwd,
        field_name="cwd",
    )
    if cwd_resolved != repo_root_path.resolve():
        raise ValueError(
            "V59-B restoration-time cwd must resolve to the admitted repository root"
        )
    if live_turn_snapshot.status not in {"starting", "running"}:
        raise ValueError("V59-B restoration-time session must remain live for continuation")
    selected_live_path_identity = (
        "urm_copilot_session_path::local_write/create_new::"
        f"{DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix()}/{target_relative_path}"
    )
    if live_turn_admission.selected_live_path_identity != selected_live_path_identity:
        raise ValueError("V59-B requires the shipped V59-A selected live path identity")
    witness_basis_summary = (
        "same-session same-turn continuation + restoration-time capability and approval "
        "resnapshot + repository-root cwd match + admitted continuity lineage"
    )
    return (
        current_capability_snapshot,
        current_approval_posture_snapshot,
        witness_basis_summary,
    )


def _validate_v59b_workspace_continuity_restoration_surfaces(
    *,
    packet: AgenticDeDomainPacket,
    proposal: AgenticDeActionProposal,
    checkpoint: AgenticDeMembraneCheckpoint,
    runtime_state: AgenticDeRuntimeState,
    ticket: AgenticDeActionTicket,
    harvest: AgenticDeRuntimeHarvestRecord,
    live_turn_admission: AgenticDeLiveTurnAdmissionRecord,
    live_turn_handoff: AgenticDeLiveTurnHandoffRecord,
    continuity_admission: AgenticDeWorkspaceContinuityAdmissionRecord,
    occupancy: AgenticDeWorkspaceOccupancyReport,
    observation: AgenticDeLocalEffectObservationRecord,
    conformance: AgenticDeLocalEffectConformanceReport,
    live_turn_reintegration: AgenticDeLiveTurnReintegrationReport,
    continuity_reintegration: AgenticDeWorkspaceContinuityReintegrationReport,
    restoration: AgenticDeLocalEffectRestorationRecord,
    continuity_restoration_handoff: AgenticDeWorkspaceContinuityRestorationHandoffRecord,
    continuity_restoration_reintegration: (
        AgenticDeWorkspaceContinuityRestorationReintegrationReport
    ),
    target_relative_path: str,
) -> None:
    if restoration.target_arc != V59B_TARGET_ARC or restoration.target_path != V59B_TARGET_PATH:
        raise ValueError("V59-C requires the shipped V59-B restoration surface")
    expected_continuity_root = DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix()
    if restoration.designated_sandbox_root != expected_continuity_root:
        raise ValueError(
            "V59-B restoration designated_sandbox_root must preserve the shipped V59-B "
            "continuity root before hardening evaluation is admitted"
        )
    if restoration.selected_live_action_class != "local_write":
        raise ValueError("V59-B restoration must preserve the shipped local_write action class")
    if restoration.selected_restoration_exemplar != V59B_RESTORATION_EXEMPLAR:
        raise ValueError("V59-B restoration must preserve the shipped create_new exemplar")
    if restoration.replay_mode != V59B_REPLAY_MODE:
        raise ValueError("V59-B restoration must preserve the shipped bounded replay law")
    if restoration.restoration_entitlement_mode != V59B_RESTORATION_ENTITLEMENT_MODE:
        raise ValueError("V59-B restoration must preserve the shipped entitlement posture")
    if restoration.packet_ref != packet.packet_id:
        raise ValueError("V59-B restoration does not bind the shipped domain packet")
    if restoration.action_proposal_ref != proposal.proposal_id:
        raise ValueError("V59-B restoration does not bind the shipped action proposal")
    if restoration.checkpoint_ref != checkpoint.checkpoint_id:
        raise ValueError("V59-B restoration does not bind the shipped checkpoint")
    if restoration.runtime_state_ref != runtime_state.state_id:
        raise ValueError("V59-B restoration does not bind the shipped runtime state")
    if restoration.ticket_ref != ticket.ticket_id:
        raise ValueError("V59-B restoration does not bind the shipped action ticket")
    if restoration.harvest_ref != harvest.harvest_id:
        raise ValueError("V59-B restoration does not bind the shipped harvest")
    if restoration.observation_ref != observation.observation_id:
        raise ValueError("V59-B restoration does not bind the shipped observation")
    if restoration.conformance_ref != conformance.report_id:
        raise ValueError("V59-B restoration does not bind the shipped conformance")
    if restoration.restoration_boundedness_verdict != "bounded":
        raise ValueError("V59-C requires the shipped bounded V59-B restoration verdict")
    if restoration.restoration_outcome != "restoration_effect_observed":
        raise ValueError("V59-C requires the shipped restoration_effect_observed V59-B posture")
    if len(restoration.restoration_observed_write_set) != 1:
        raise ValueError("V59-C requires exactly one shipped V59-B restoration target")
    restoration_entry = restoration.restoration_observed_write_set[0]
    observed_entry = observation.observed_write_set[0]
    if restoration_entry.relative_path != observed_entry.relative_path:
        raise ValueError("V59-B restoration must preserve the shipped observed target path")
    if restoration_entry.existed_before_restoration is not True:
        raise ValueError(
            "V59-C requires the shipped V59-B restoration lineage to record an existing "
            "target before compensating removal"
        )
    if restoration_entry.bytes_removed != observed_entry.bytes_written:
        raise ValueError(
            "V59-C requires the shipped V59-B restoration lineage to preserve removed-bytes "
            "equivalence with the observed exemplar"
        )
    if restoration_entry.removed_content_sha256 != observed_entry.content_sha256:
        raise ValueError(
            "V59-C requires the shipped V59-B restoration lineage to preserve removed-content "
            "equivalence with the observed exemplar"
        )
    if (
        continuity_restoration_handoff.target_arc != V59B_TARGET_ARC
        or continuity_restoration_handoff.target_path != V59B_TARGET_PATH
    ):
        raise ValueError("V59-C requires the shipped V59-B continuity restoration handoff")
    if (
        continuity_restoration_reintegration.target_arc != V59B_TARGET_ARC
        or continuity_restoration_reintegration.target_path != V59B_TARGET_PATH
    ):
        raise ValueError(
            "V59-C requires the shipped V59-B continuity restoration reintegration"
        )
    if continuity_restoration_handoff.evidence_only is not True:
        raise ValueError("V59-C requires the shipped evidence-only V59-B handoff posture")
    if continuity_restoration_handoff.changes_live_behavior_by_default:
        raise ValueError("V59-C requires the shipped non-live V59-B handoff posture")
    if continuity_restoration_reintegration.evidence_only is not True:
        raise ValueError(
            "V59-C requires the shipped evidence-only V59-B reintegration posture"
        )
    if continuity_restoration_reintegration.changes_live_behavior_by_default:
        raise ValueError("V59-C requires the shipped non-live V59-B reintegration posture")
    if continuity_restoration_handoff.turn_admission_ref != live_turn_admission.admission_id:
        raise ValueError("V59-B handoff does not bind the shipped V59-A admission lineage")
    if continuity_restoration_handoff.turn_handoff_ref != live_turn_handoff.handoff_id:
        raise ValueError("V59-B handoff does not bind the shipped V59-A handoff lineage")
    if (
        continuity_restoration_handoff.continuity_admission_ref
        != continuity_admission.continuity_admission_id
    ):
        raise ValueError("V59-B handoff does not bind the shipped V59-A continuity admission")
    if continuity_restoration_handoff.occupancy_report_ref != occupancy.occupancy_report_id:
        raise ValueError("V59-B handoff does not bind the shipped V59-A occupancy lineage")
    if (
        continuity_restoration_handoff.prior_continuity_reintegration_ref
        != continuity_reintegration.report_id
    ):
        raise ValueError(
            "V59-B handoff does not bind the shipped V59-A continuity reintegration lineage"
        )
    if continuity_restoration_handoff.restoration_record_ref != restoration.restoration_id:
        raise ValueError("V59-B handoff does not bind the shipped restoration record")
    if continuity_restoration_handoff.action_ticket_ref != live_turn_handoff.action_ticket_ref:
        raise ValueError("V59-B handoff does not preserve the shipped V56-B ticket lineage")
    if continuity_restoration_handoff.target_relative_path != target_relative_path:
        raise ValueError("V59-B handoff does not preserve the shipped selected target")
    if continuity_restoration_handoff.restoration_time_continuation_verdict != "continued":
        raise ValueError("V59-C requires the shipped continued V59-B restoration posture")
    if (
        continuity_restoration_handoff.prior_governed_state_baseline_match_verdict
        != "matched"
    ):
        raise ValueError("V59-C requires the shipped matched V59-B baseline posture")
    if continuity_restoration_handoff.selected_restoration_scope != V59B_SELECTED_RESTORATION_SCOPE:
        raise ValueError("V59-B handoff must preserve the shipped bounded restoration scope")
    if continuity_restoration_reintegration.turn_admission_ref != live_turn_admission.admission_id:
        raise ValueError(
            "V59-B reintegration does not bind the shipped V59-A admission lineage"
        )
    if (
        continuity_restoration_reintegration.workspace_continuity_restoration_handoff_ref
        != continuity_restoration_handoff.handoff_id
    ):
        raise ValueError("V59-B reintegration does not bind the shipped V59-B handoff")
    if continuity_restoration_reintegration.restoration_record_ref != restoration.restoration_id:
        raise ValueError("V59-B reintegration does not bind the shipped restoration record")
    if (
        continuity_restoration_reintegration.continuity_restoration_reintegration_status
        != "reintegrated"
    ):
        raise ValueError("V59-C requires the shipped reintegrated V59-B restoration posture")
    if (
        continuity_restoration_reintegration.continuity_restoration_reintegration_certificate_ref_or_equivalent
        is None
    ):
        raise ValueError("V59-C requires witness-bearing V59-B restoration reintegration")
    expected_witness_basis_dependencies = [
        live_turn_admission.admission_id,
        continuity_restoration_handoff.handoff_id,
        restoration.restoration_id,
    ]
    if (
        continuity_restoration_reintegration.field_dependence_tags[
            "continuity_restoration_reintegration_witness_basis_summary"
        ]
        != expected_witness_basis_dependencies
    ):
        raise ValueError(
            "V59-B reintegration must preserve the shipped non-independent witness basis"
        )
    if (
        continuity_restoration_reintegration.field_dependence_tags["six_lane_closeout_posture"]
        != expected_witness_basis_dependencies
    ):
        raise ValueError(
            "V59-B reintegration must preserve the shipped non-independent closeout basis"
        )
    if continuity_restoration_reintegration.field_dependence_tags["replay_law_proof_summary"] != [
        continuity_reintegration.report_id,
        restoration.restoration_id,
    ]:
        raise ValueError(
            "V59-B reintegration must preserve the shipped bounded replay proof lineage"
        )
    if continuity_reintegration.occupancy_report_ref != occupancy.occupancy_report_id:
        raise ValueError("V59-A continuity reintegration must preserve the shipped occupancy")
    if continuity_reintegration.observation_ref != observation.observation_id:
        raise ValueError("V59-A continuity reintegration must preserve the shipped observation")
    if continuity_reintegration.local_effect_conformance_ref != conformance.report_id:
        raise ValueError("V59-A continuity reintegration must preserve the shipped conformance")
    if live_turn_reintegration.turn_admission_ref != live_turn_admission.admission_id:
        raise ValueError("V59-A live reintegration must preserve the shipped admission")


def _build_v59b_workspace_continuity_restoration_handoff_record(
    *,
    live_turn_snapshot: CopilotTurnSnapshot,
    live_turn_admission: AgenticDeLiveTurnAdmissionRecord,
    live_turn_handoff: AgenticDeLiveTurnHandoffRecord,
    continuity_admission: AgenticDeWorkspaceContinuityAdmissionRecord,
    occupancy: AgenticDeWorkspaceOccupancyReport,
    prior_continuity_reintegration: AgenticDeWorkspaceContinuityReintegrationReport,
    restoration: AgenticDeLocalEffectRestorationRecord,
    restoration_time_session_capability_snapshot: str,
    restoration_time_approval_posture_snapshot: str,
    restoration_time_continuation_witness_basis_summary: str,
    prior_governed_state_baseline_summary: str,
    prior_governed_state_baseline_match_verdict: str,
    restoration_time_target_or_region_state_summary: str,
    target_relative_path: str,
    evidence_refs: list[str],
) -> AgenticDeWorkspaceContinuityRestorationHandoffRecord:
    field_origin_tags = {
        "turn_admission_ref": "prior_artifact",
        "turn_handoff_ref": "prior_artifact",
        "continuity_admission_ref": "prior_artifact",
        "occupancy_report_ref": "prior_artifact",
        "prior_continuity_reintegration_ref": "prior_artifact",
        "restoration_time_session_capability_snapshot": "current_turn_native",
        "restoration_time_approval_posture_snapshot": "current_turn_native",
        "restoration_time_continuation_verdict": "current_turn_derived",
        "restoration_time_continuation_witness_basis_summary": "current_turn_derived",
        "restoration_record_ref": "current_turn_derived",
        "action_ticket_ref": "prior_artifact",
        "prior_governed_state_baseline_summary": "current_turn_derived",
        "prior_governed_state_baseline_match_verdict": "current_turn_derived",
        "restoration_time_target_or_region_state_summary": "current_turn_derived",
        "bounded_compensating_scope_derivation_summary": "current_turn_derived",
        "target_relative_path": "current_turn_derived",
        "selected_restoration_scope": "current_turn_derived",
    }
    field_dependence_tags = {
        "turn_admission_ref": [],
        "turn_handoff_ref": [],
        "continuity_admission_ref": [],
        "occupancy_report_ref": [],
        "prior_continuity_reintegration_ref": [],
        "restoration_time_session_capability_snapshot": [],
        "restoration_time_approval_posture_snapshot": [],
        "restoration_time_continuation_verdict": [
            live_turn_admission.admission_id,
            continuity_admission.continuity_admission_id,
            prior_continuity_reintegration.report_id,
        ],
        "restoration_time_continuation_witness_basis_summary": [
            live_turn_admission.admission_id,
            continuity_admission.continuity_admission_id,
            prior_continuity_reintegration.report_id,
        ],
        "restoration_record_ref": [],
        "action_ticket_ref": [],
        "prior_governed_state_baseline_summary": [
            occupancy.occupancy_report_id,
            prior_continuity_reintegration.report_id,
            restoration.restoration_id,
        ],
        "prior_governed_state_baseline_match_verdict": [
            occupancy.occupancy_report_id,
            prior_continuity_reintegration.report_id,
            restoration.restoration_id,
        ],
        "restoration_time_target_or_region_state_summary": [
            occupancy.occupancy_report_id,
            restoration.restoration_id,
        ],
        "bounded_compensating_scope_derivation_summary": [
            live_turn_handoff.action_ticket_ref,
            prior_continuity_reintegration.report_id,
            occupancy.occupancy_report_id,
            restoration.restoration_id,
        ],
        "target_relative_path": [
            live_turn_admission.selected_live_path_identity,
        ],
        "selected_restoration_scope": [
            live_turn_handoff.action_ticket_ref,
            prior_continuity_reintegration.report_id,
            restoration.restoration_id,
            target_relative_path,
        ],
    }
    root_origin_ids = [
        f"session:{live_turn_snapshot.session_id}",
        f"turn:{live_turn_snapshot.selected_turn_id}",
        f"ticket:{live_turn_handoff.action_ticket_ref}",
        f"occupancy:{occupancy.occupancy_report_id}",
        f"restoration:{restoration.restoration_id}",
        f"target:{target_relative_path}",
    ]
    return AgenticDeWorkspaceContinuityRestorationHandoffRecord(
        target_arc=V59B_TARGET_ARC,
        target_path=V59B_TARGET_PATH,
        turn_admission_ref=live_turn_admission.admission_id,
        turn_handoff_ref=live_turn_handoff.handoff_id,
        continuity_admission_ref=continuity_admission.continuity_admission_id,
        occupancy_report_ref=occupancy.occupancy_report_id,
        prior_continuity_reintegration_ref=prior_continuity_reintegration.report_id,
        restoration_time_session_capability_snapshot=restoration_time_session_capability_snapshot,
        restoration_time_approval_posture_snapshot=restoration_time_approval_posture_snapshot,
        restoration_time_continuation_verdict="continued",
        restoration_time_continuation_witness_basis_summary=(
            restoration_time_continuation_witness_basis_summary
        ),
        restoration_record_ref=restoration.restoration_id,
        action_ticket_ref=live_turn_handoff.action_ticket_ref,
        prior_governed_state_baseline_summary=prior_governed_state_baseline_summary,
        prior_governed_state_baseline_match_verdict=(
            prior_governed_state_baseline_match_verdict
        ),
        restoration_time_target_or_region_state_summary=(
            restoration_time_target_or_region_state_summary
        ),
        bounded_compensating_scope_derivation_summary=(
            "bounded compensating scope derived from historical ticket/continuity lineage "
            "+ prior governed-state baseline match + current-turn restoration witness; "
            "historical refs remain non-entitling by themselves"
        ),
        target_relative_path=target_relative_path,
        selected_restoration_scope=V59B_SELECTED_RESTORATION_SCOPE,
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=root_origin_ids,
        evidence_refs=[
            live_turn_admission.admission_id,
            live_turn_handoff.handoff_id,
            continuity_admission.continuity_admission_id,
            occupancy.occupancy_report_id,
            prior_continuity_reintegration.report_id,
            restoration.restoration_id,
            *evidence_refs,
        ],
    )


def _build_v59b_workspace_continuity_restoration_reintegration_report(
    *,
    live_turn_snapshot: CopilotTurnSnapshot,
    live_turn_admission: AgenticDeLiveTurnAdmissionRecord,
    continuity_restoration_handoff: AgenticDeWorkspaceContinuityRestorationHandoffRecord,
    restoration: AgenticDeLocalEffectRestorationRecord,
    evidence_refs: list[str],
) -> AgenticDeWorkspaceContinuityRestorationReintegrationReport:
    if (
        restoration.restoration_outcome == "restoration_effect_observed"
        and restoration.restoration_boundedness_verdict == "bounded"
    ):
        reintegration_status = "reintegrated"
        reason_codes = [
            "current_turn_restoration_witness_declared",
            "prior_governed_state_baseline_matched",
            "bounded_compensating_scope_matched",
            "continuity_safe_restoration_effect_aligned",
        ]
        certificate_ref = (
            "v59b_continuity_restoration_reintegration::"
            f"{live_turn_snapshot.session_id}::"
            f"{live_turn_snapshot.selected_turn_id}::"
            f"{restoration.restoration_id}"
        )
        six_lane_closeout_posture = (
            "current_turn_continuity_lineage_preserved_then_bounded_compensating_"
            "continuity_restore_reintegrated"
        )
    elif restoration.restoration_outcome == "no_restoration_effect_observed":
        reintegration_status = "residualized"
        reason_codes = [
            "no_current_turn_restoration_effect_observed",
            "positive_continuity_restoration_reintegration_not_declared",
        ]
        certificate_ref = None
        six_lane_closeout_posture = "current_turn_continuity_restoration_residualized_no_effect"
    elif restoration.restoration_outcome == "restoration_boundedness_verdict_failed":
        reintegration_status = "blocked"
        reason_codes = [
            "restoration_boundedness_verdict_failed",
            "positive_continuity_restoration_reintegration_not_declared",
        ]
        certificate_ref = None
        six_lane_closeout_posture = (
            "current_turn_continuity_restoration_blocked_boundedness_failed"
        )
    else:
        reintegration_status = "blocked"
        reason_codes = [
            "continuity_safe_restoration_not_reintegrable",
            "positive_continuity_restoration_reintegration_not_declared",
        ]
        certificate_ref = None
        six_lane_closeout_posture = "current_turn_continuity_restoration_blocked_non_aligned_effect"

    field_origin_tags = {
        "restoration_effect_summary": "current_turn_derived",
        "continuity_restoration_reintegration_witness_basis_summary": "current_turn_derived",
        "replay_law_proof_summary": "current_turn_derived",
        "six_lane_closeout_posture": "current_turn_derived",
    }
    field_dependence_tags = {
        "restoration_effect_summary": [restoration.restoration_id],
        "continuity_restoration_reintegration_witness_basis_summary": [
            live_turn_admission.admission_id,
            continuity_restoration_handoff.handoff_id,
            restoration.restoration_id,
        ],
        "replay_law_proof_summary": [
            continuity_restoration_handoff.prior_continuity_reintegration_ref,
            restoration.restoration_id,
        ],
        "six_lane_closeout_posture": [
            live_turn_admission.admission_id,
            continuity_restoration_handoff.handoff_id,
            restoration.restoration_id,
        ],
    }
    root_origin_dedup_summary = (
        "dedup roots="
        f"session:{live_turn_snapshot.session_id},"
        f"turn:{live_turn_snapshot.selected_turn_id},"
        f"ticket:{continuity_restoration_handoff.action_ticket_ref},"
        f"prior_continuity_reintegration:{continuity_restoration_handoff.prior_continuity_reintegration_ref},"
        f"restoration:{restoration.restoration_id};"
        " repeated continuity and observability refs remain non-independent support"
    )
    return AgenticDeWorkspaceContinuityRestorationReintegrationReport(
        target_arc=V59B_TARGET_ARC,
        target_path=V59B_TARGET_PATH,
        turn_admission_ref=live_turn_admission.admission_id,
        workspace_continuity_restoration_handoff_ref=continuity_restoration_handoff.handoff_id,
        restoration_record_ref=restoration.restoration_id,
        restoration_effect_summary=restoration.restoration_effect,
        continuity_restoration_reintegration_status=reintegration_status,
        reason_codes=reason_codes,
        continuity_restoration_reintegration_witness_basis_summary=(
            "current-turn live admission continuity + prior continuity reintegration "
            "lineage + restoration-time baseline match + restoration pre/post state + "
            "restoration record"
        ),
        continuity_restoration_reintegration_certificate_ref_or_equivalent=certificate_ref,
        replay_law_proof_summary=(
            "bounded recomputation and re-evaluation of the exact continuity-safe "
            "compensating restore event against the prior continuity-bound lineage only"
        ),
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_dedup_summary=root_origin_dedup_summary,
        six_lane_closeout_posture=six_lane_closeout_posture,
        evidence_refs=[
            live_turn_admission.admission_id,
            continuity_restoration_handoff.handoff_id,
            restoration.restoration_id,
            *evidence_refs,
        ],
    )


def _derive_v59c_compensating_scope_match_verdict(
    handoff: AgenticDeWorkspaceContinuityRestorationHandoffRecord,
) -> str:
    if handoff.selected_restoration_scope != V59B_SELECTED_RESTORATION_SCOPE:
        raise ValueError("V59-C requires the shipped bounded continuity-safe restoration scope")
    return "matched"


def _build_v59c_workspace_continuity_hardening_register(
    *,
    continuity_admission: AgenticDeWorkspaceContinuityAdmissionRecord,
    occupancy: AgenticDeWorkspaceOccupancyReport,
    continuity_reintegration: AgenticDeWorkspaceContinuityReintegrationReport,
    live_turn_admission: AgenticDeLiveTurnAdmissionRecord,
    live_turn_handoff: AgenticDeLiveTurnHandoffRecord,
    live_turn_reintegration: AgenticDeLiveTurnReintegrationReport,
    continuity_restoration_handoff: AgenticDeWorkspaceContinuityRestorationHandoffRecord,
    restoration: AgenticDeLocalEffectRestorationRecord,
    continuity_restoration_reintegration: (
        AgenticDeWorkspaceContinuityRestorationReintegrationReport
    ),
    observation: AgenticDeLocalEffectObservationRecord,
    conformance: AgenticDeLocalEffectConformanceReport,
    evidence_refs: list[str],
) -> AgenticDeWorkspaceContinuityHardeningRegister:
    frozen_policy_ref = "docs/LOCKED_CONTINUATION_vNEXT_PLUS163.md#machine-checkable-contract"
    root_origin_ids = [
        f"session:{live_turn_admission.live_session_id}",
        f"turn:{live_turn_admission.live_turn_id}",
        f"ticket:{live_turn_handoff.action_ticket_ref}",
        f"occupancy:{occupancy.occupancy_report_id}",
        f"observation:{observation.observation_id}",
        f"conformance:{conformance.report_id}",
        f"continuity_reintegration:{continuity_reintegration.report_id}",
        f"restoration:{restoration.restoration_id}",
        f"continuity_restoration_reintegration:{continuity_restoration_reintegration.report_id}",
        f"policy:{frozen_policy_ref}",
    ]
    entry = AgenticDeWorkspaceContinuityHardeningEntry(
        continuity_admission_ref=continuity_admission.continuity_admission_id,
        occupancy_report_ref=occupancy.occupancy_report_id,
        continuity_reintegration_ref=continuity_reintegration.report_id,
        turn_admission_ref=live_turn_admission.admission_id,
        turn_handoff_ref=live_turn_handoff.handoff_id,
        turn_reintegration_ref=live_turn_reintegration.report_id,
        workspace_continuity_restoration_handoff_ref=continuity_restoration_handoff.handoff_id,
        restoration_ref=restoration.restoration_id,
        workspace_continuity_restoration_reintegration_ref=(
            continuity_restoration_reintegration.report_id
        ),
        observation_ref=observation.observation_id,
        local_effect_conformance_ref=conformance.report_id,
        occupancy_verdict=occupancy.occupancy_verdict,
        continuity_reintegration_status=continuity_reintegration.continuity_reintegration_status,
        restoration_time_continuation_verdict=(
            continuity_restoration_handoff.restoration_time_continuation_verdict
        ),
        prior_governed_state_baseline_match_verdict=(
            continuity_restoration_handoff.prior_governed_state_baseline_match_verdict
        ),
        bounded_compensating_scope_match_verdict=(
            _derive_v59c_compensating_scope_match_verdict(continuity_restoration_handoff)
        ),
        observation_boundedness_verdict=observation.boundedness_verdict,
        restoration_boundedness_verdict=restoration.restoration_boundedness_verdict,
        continuity_restoration_reintegration_status=(
            continuity_restoration_reintegration.continuity_restoration_reintegration_status
        ),
        selected_hardening_target_surface=(
            "observed_and_restored_continuity_bound_create_new_exemplar_only"
        ),
        frozen_policy_ref=frozen_policy_ref,
        evidence_basis_summary=(
            "shipped V59-A continuity admission/occupancy/reintegration plus shipped "
            "V59-B continuity-safe restoration handoff/reintegration over the same "
            "continuity-bound create_new exemplar"
        ),
        verdict_basis_summary=(
            "occupancy remained unoccupied at admission time, continuity reintegration "
            "stayed reintegrated, restoration-time continuation and prior governed "
            "baseline stayed matched, bounded compensating scope stayed matched, "
            "observation remained bounded, restoration remained bounded, and continuity "
            "restoration reintegration stayed reintegrated"
        ),
        root_origin_ids=root_origin_ids,
        root_origin_dedup_summary=(
            "dedup roots="
            + ",".join(root_origin_ids)
            + "; repeated continuity lineage artifacts remain non-independent escalation support"
        ),
        recommended_outcome="candidate_for_later_continuity_hardening",
        rationale=(
            "the exact continuity-bound observed-and-restored exemplar now has typed "
            "continuity admission, typed occupancy, witness-bearing continuity "
            "reintegration, continuity-safe restoration with freshness and baseline "
            "checks, and witness-bearing restoration reintegration under frozen "
            "policy, so it is a valid later path-level continuity hardening candidate, "
            "but any broader class, continuity, restoration, replay, or migration "
            "scope still requires a later explicit lock"
        ),
        reason_codes=[
            "occupancy_unoccupied",
            "continuity_reintegrated",
            "restoration_time_continued",
            "prior_governed_state_baseline_matched",
            "bounded_compensating_scope_matched",
            "observation_bounded",
            "restoration_bounded",
            "continuity_restoration_reintegrated",
            "path_level_only",
            "later_lock_required_for_scope",
            "extensional_replayable_policy",
            "lineage_root_dedup_applied",
            "no_live_mutation_in_v59c",
        ],
        evidence_refs=evidence_refs,
    )
    return AgenticDeWorkspaceContinuityHardeningRegister(
        target_arc=V59C_TARGET_ARC,
        target_path=V59C_TARGET_PATH,
        baseline_checker_version=V59B_CHECKER_VERSION,
        entry_count=1,
        entries=[entry],
    )


def run_agentic_de_workspace_continuity_v59b(
    *,
    live_turn_snapshot: CopilotTurnSnapshot,
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
    v56c_lane_drift_path: Path = DEFAULT_V56C_LANE_DRIFT_PATH,
    v56c_runtime_harvest_path: Path = DEFAULT_V56C_RUNTIME_HARVEST_PATH,
    v56c_governance_calibration_path: Path = DEFAULT_V56C_GOVERNANCE_CALIBRATION_PATH,
    v56c_migration_decision_path: Path = DEFAULT_V56C_MIGRATION_DECISION_PATH,
    v59a_lane_drift_path: Path = DEFAULT_V59A_LANE_DRIFT_PATH,
    v59a_continuity_region_path: Path = DEFAULT_V59A_CONTINUITY_REGION_DECLARATION_PATH,
    v59a_continuity_admission_path: Path = DEFAULT_V59A_CONTINUITY_ADMISSION_PATH,
    v59a_occupancy_path: Path = DEFAULT_V59A_OCCUPANCY_REPORT_PATH,
    v59a_live_turn_admission_path: Path = DEFAULT_V59A_LIVE_TURN_ADMISSION_PATH,
    v59a_live_turn_handoff_path: Path = DEFAULT_V59A_LIVE_TURN_HANDOFF_PATH,
    v59a_observation_path: Path = DEFAULT_V59A_OBSERVATION_PATH,
    v59a_local_effect_conformance_path: Path = DEFAULT_V59A_LOCAL_EFFECT_CONFORMANCE_PATH,
    v59a_live_turn_reintegration_path: Path = DEFAULT_V59A_LIVE_TURN_REINTEGRATION_PATH,
    v59a_continuity_reintegration_path: Path = DEFAULT_V59A_CONTINUITY_REINTEGRATION_PATH,
    lane_drift_path: Path = DEFAULT_V59B_LANE_DRIFT_PATH,
    v59a_evidence_path: Path = DEFAULT_V59A_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
    expected_relative_paths: tuple[str, ...] | None = None,
    materialize_restoration_effect: bool = True,
) -> tuple[
    AgenticDeWorkspaceContinuityRestorationHandoffRecord,
    AgenticDeLocalEffectRestorationRecord,
    AgenticDeWorkspaceContinuityRestorationReintegrationReport,
]:
    if repo_root_path is None:
        root = repo_root(anchor=Path(__file__)).resolve()
    else:
        if repo_root_path.exists() and repo_root_path.is_symlink():
            raise ValueError("repository root may not be a symlink for V59-B continuity")
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
    v56c_lane_drift_path = _resolve_path(repo_root_path=root, path=v56c_lane_drift_path)
    v56c_runtime_harvest_path = _resolve_path(repo_root_path=root, path=v56c_runtime_harvest_path)
    v56c_governance_calibration_path = _resolve_path(
        repo_root_path=root, path=v56c_governance_calibration_path
    )
    v56c_migration_decision_path = _resolve_path(
        repo_root_path=root, path=v56c_migration_decision_path
    )
    v59a_lane_drift_path = _resolve_path(repo_root_path=root, path=v59a_lane_drift_path)
    v59a_continuity_region_path = _resolve_path(
        repo_root_path=root, path=v59a_continuity_region_path
    )
    v59a_continuity_admission_path = _resolve_path(
        repo_root_path=root, path=v59a_continuity_admission_path
    )
    v59a_occupancy_path = _resolve_path(repo_root_path=root, path=v59a_occupancy_path)
    v59a_live_turn_admission_path = _resolve_path(
        repo_root_path=root, path=v59a_live_turn_admission_path
    )
    v59a_live_turn_handoff_path = _resolve_path(
        repo_root_path=root, path=v59a_live_turn_handoff_path
    )
    v59a_observation_path = _resolve_path(repo_root_path=root, path=v59a_observation_path)
    v59a_local_effect_conformance_path = _resolve_path(
        repo_root_path=root, path=v59a_local_effect_conformance_path
    )
    v59a_live_turn_reintegration_path = _resolve_path(
        repo_root_path=root, path=v59a_live_turn_reintegration_path
    )
    v59a_continuity_reintegration_path = _resolve_path(
        repo_root_path=root, path=v59a_continuity_reintegration_path
    )
    lane_drift_path = _resolve_path(repo_root_path=root, path=lane_drift_path)
    v59a_evidence_path = _resolve_path(repo_root_path=root, path=v59a_evidence_path)

    _validate_v59b_lane_drift_record(load_lane_drift_record(lane_drift_path))
    _validate_v59a_lane_drift_record(load_lane_drift_record(v59a_lane_drift_path))
    _validate_v56b_lane_drift_record(load_lane_drift_record(v56b_lane_drift_path))
    _validate_v56c_lane_drift_record(load_lane_drift_record(v56c_lane_drift_path))
    _validate_v59a_evidence_payload(
        _load_json_object(v59a_evidence_path, error_label="V59-A evidence")
    )

    packet = load_domain_packet(domain_packet_path)
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
    v56c_harvest = load_runtime_harvest_record(v56c_runtime_harvest_path)
    v56c_governance = load_governance_calibration_register(v56c_governance_calibration_path)
    v56c_migration = load_migration_decision_register(v56c_migration_decision_path)
    v59a_continuity_region = load_workspace_continuity_region_declaration(
        v59a_continuity_region_path
    )
    v59a_continuity_admission = load_workspace_continuity_admission_record(
        v59a_continuity_admission_path
    )
    v59a_occupancy = load_workspace_occupancy_report(v59a_occupancy_path)
    v59a_live_turn_admission = load_live_turn_admission_record(v59a_live_turn_admission_path)
    v59a_live_turn_handoff = load_live_turn_handoff_record(v59a_live_turn_handoff_path)
    v59a_observation = load_local_effect_observation_record(v59a_observation_path)
    v59a_conformance = load_local_effect_conformance_report(v59a_local_effect_conformance_path)
    v59a_live_turn_reintegration = load_live_turn_reintegration_report(
        v59a_live_turn_reintegration_path
    )
    v59a_continuity_reintegration = load_workspace_continuity_reintegration_report(
        v59a_continuity_reintegration_path
    )

    _validate_v56a_reference_surfaces(
        domain_packet=packet,
        morph_ir=morph_ir,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        diagnostics=v56a_diagnostics,
        conformance=v56a_conformance,
    )
    _validate_v56b_reference_surfaces(
        domain_packet=packet,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        taxonomy=v56b_taxonomy,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        diagnostics=v56b_diagnostics,
        conformance=v56b_conformance,
    )
    _validate_v57a_reference_surfaces(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        taxonomy=v56b_taxonomy,
        harvest=v56c_harvest,
        governance=v56c_governance,
        migration=v56c_migration,
    )
    _validate_v59a_workspace_continuity_surfaces(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        ticket=v56b_ticket,
        continuity_region=v59a_continuity_region,
        continuity_admission=v59a_continuity_admission,
        occupancy=v59a_occupancy,
        live_turn_admission=v59a_live_turn_admission,
        live_turn_handoff=v59a_live_turn_handoff,
        observation=v59a_observation,
        conformance=v59a_conformance,
        live_turn_reintegration=v59a_live_turn_reintegration,
        continuity_reintegration=v59a_continuity_reintegration,
        target_relative_path=target_relative_path,
    )

    (
        restoration_time_session_capability_snapshot,
        restoration_time_approval_posture_snapshot,
        restoration_time_continuation_witness_basis_summary,
    ) = _validate_v59b_restoration_time_continuation(
        repo_root_path=root,
        live_turn_snapshot=live_turn_snapshot,
        live_turn_admission=v59a_live_turn_admission,
        continuity_admission=v59a_continuity_admission,
        target_relative_path=target_relative_path,
    )

    if len(v59a_observation.observed_write_set) != 1:
        raise ValueError("V59-B requires exactly one shipped V59-A observed target")
    if _derived_restore_target_relative_path(v59a_observation) != target_relative_path:
        raise ValueError("V59-B requires the shipped V59-A observed target lineage")
    observed_entry = v59a_observation.observed_write_set[0]
    restoration_effect = observe_workspace_continuity_create_new_restoration_effect(
        repo_root_path=root,
        target_relative_path=target_relative_path,
        expected_prior_governed_lineage_ref=v59a_observation.observation_id,
        expected_target_content_sha256=observed_entry.content_sha256,
        expected_relative_paths=expected_relative_paths,
        materialize_restoration_effect=materialize_restoration_effect,
    )

    base_evidence_refs = [
        _render_input_ref(repo_root_path=root, path=domain_packet_path),
        _render_input_ref(repo_root_path=root, path=morph_ir_path),
        _render_input_ref(repo_root_path=root, path=interaction_contract_path),
        _render_input_ref(repo_root_path=root, path=action_proposal_path),
        _render_input_ref(repo_root_path=root, path=v56a_checkpoint_path),
        _render_input_ref(repo_root_path=root, path=v56a_diagnostics_path),
        _render_input_ref(repo_root_path=root, path=v56a_conformance_path),
        _render_input_ref(repo_root_path=root, path=v56b_action_class_taxonomy_path),
        _render_input_ref(repo_root_path=root, path=v56b_runtime_state_path),
        _render_input_ref(repo_root_path=root, path=v56b_action_ticket_path),
        _render_input_ref(repo_root_path=root, path=v56b_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56b_diagnostics_path),
        _render_input_ref(repo_root_path=root, path=v56b_conformance_path),
        _render_input_ref(repo_root_path=root, path=v56c_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56c_runtime_harvest_path),
        _render_input_ref(repo_root_path=root, path=v56c_governance_calibration_path),
        _render_input_ref(repo_root_path=root, path=v56c_migration_decision_path),
        _render_input_ref(repo_root_path=root, path=v59a_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v59a_continuity_region_path),
        _render_input_ref(repo_root_path=root, path=v59a_continuity_admission_path),
        _render_input_ref(repo_root_path=root, path=v59a_occupancy_path),
        _render_input_ref(repo_root_path=root, path=v59a_live_turn_admission_path),
        _render_input_ref(repo_root_path=root, path=v59a_live_turn_handoff_path),
        _render_input_ref(repo_root_path=root, path=v59a_observation_path),
        _render_input_ref(repo_root_path=root, path=v59a_local_effect_conformance_path),
        _render_input_ref(repo_root_path=root, path=v59a_live_turn_reintegration_path),
        _render_input_ref(repo_root_path=root, path=v59a_continuity_reintegration_path),
        _render_input_ref(repo_root_path=root, path=lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v59a_evidence_path),
        *_snapshot_observability_refs(
            repo_root_path=root,
            live_turn_snapshot=live_turn_snapshot,
        ),
        restoration_effect.restoration_pre_state_ref,
        restoration_effect.restoration_post_state_ref,
    ]
    restoration = _build_v57b_local_effect_restoration_record(
        target_arc=V59B_TARGET_ARC,
        target_path=V59B_TARGET_PATH,
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        harvest=v56c_harvest,
        observation=v59a_observation,
        conformance=v59a_conformance,
        designated_sandbox_root=restoration_effect.declared_continuity_root,
        restoration_pre_state_ref=restoration_effect.restoration_pre_state_ref,
        restoration_observed_write_set=restoration_effect.restoration_observed_write_set,
        restoration_post_state_ref=restoration_effect.restoration_post_state_ref,
        restoration_effect=restoration_effect.restoration_effect,
        restoration_outcome=restoration_effect.restoration_outcome,
        restoration_boundedness_verdict=restoration_effect.restoration_boundedness_verdict,
        restoration_boundedness_note=restoration_effect.restoration_boundedness_note,
        evidence_refs=base_evidence_refs,
    )
    continuity_restoration_handoff = _build_v59b_workspace_continuity_restoration_handoff_record(
        live_turn_snapshot=live_turn_snapshot,
        live_turn_admission=v59a_live_turn_admission,
        live_turn_handoff=v59a_live_turn_handoff,
        continuity_admission=v59a_continuity_admission,
        occupancy=v59a_occupancy,
        prior_continuity_reintegration=v59a_continuity_reintegration,
        restoration=restoration,
        restoration_time_session_capability_snapshot=restoration_time_session_capability_snapshot,
        restoration_time_approval_posture_snapshot=restoration_time_approval_posture_snapshot,
        restoration_time_continuation_witness_basis_summary=(
            restoration_time_continuation_witness_basis_summary
        ),
        prior_governed_state_baseline_summary=(
            restoration_effect.prior_governed_state_baseline_summary
        ),
        prior_governed_state_baseline_match_verdict=(
            restoration_effect.prior_governed_state_baseline_match_verdict
        ),
        restoration_time_target_or_region_state_summary=(
            restoration_effect.restoration_time_target_or_region_state_summary
        ),
        target_relative_path=target_relative_path,
        evidence_refs=base_evidence_refs,
    )
    continuity_restoration_reintegration = (
        _build_v59b_workspace_continuity_restoration_reintegration_report(
            live_turn_snapshot=live_turn_snapshot,
            live_turn_admission=v59a_live_turn_admission,
            continuity_restoration_handoff=continuity_restoration_handoff,
            restoration=restoration,
            evidence_refs=base_evidence_refs,
        )
    )
    return (
        continuity_restoration_handoff,
        restoration,
        continuity_restoration_reintegration,
    )


def run_agentic_de_workspace_continuity_v59c(
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
    v56c_lane_drift_path: Path = DEFAULT_V56C_LANE_DRIFT_PATH,
    v56c_runtime_harvest_path: Path = DEFAULT_V56C_RUNTIME_HARVEST_PATH,
    v56c_governance_calibration_path: Path = DEFAULT_V56C_GOVERNANCE_CALIBRATION_PATH,
    v56c_migration_decision_path: Path = DEFAULT_V56C_MIGRATION_DECISION_PATH,
    v59a_lane_drift_path: Path = DEFAULT_V59A_LANE_DRIFT_PATH,
    v59a_continuity_region_path: Path = DEFAULT_V59A_CONTINUITY_REGION_DECLARATION_PATH,
    v59a_continuity_admission_path: Path = DEFAULT_V59A_CONTINUITY_ADMISSION_PATH,
    v59a_occupancy_path: Path = DEFAULT_V59A_OCCUPANCY_REPORT_PATH,
    v59a_live_turn_admission_path: Path = DEFAULT_V59A_LIVE_TURN_ADMISSION_PATH,
    v59a_live_turn_handoff_path: Path = DEFAULT_V59A_LIVE_TURN_HANDOFF_PATH,
    v59a_observation_path: Path = DEFAULT_V59A_OBSERVATION_PATH,
    v59a_local_effect_conformance_path: Path = DEFAULT_V59A_LOCAL_EFFECT_CONFORMANCE_PATH,
    v59a_live_turn_reintegration_path: Path = DEFAULT_V59A_LIVE_TURN_REINTEGRATION_PATH,
    v59a_continuity_reintegration_path: Path = DEFAULT_V59A_CONTINUITY_REINTEGRATION_PATH,
    v59b_lane_drift_path: Path = DEFAULT_V59B_LANE_DRIFT_PATH,
    v59b_continuity_restoration_handoff_path: Path = (
        DEFAULT_V59B_CONTINUITY_RESTORATION_HANDOFF_PATH
    ),
    v59b_restoration_path: Path = DEFAULT_V59B_RESTORATION_PATH,
    v59b_continuity_restoration_reintegration_path: Path = (
        DEFAULT_V59B_CONTINUITY_RESTORATION_REINTEGRATION_PATH
    ),
    lane_drift_path: Path = DEFAULT_V59C_LANE_DRIFT_PATH,
    v59a_evidence_path: Path = DEFAULT_V59A_EVIDENCE_PATH,
    v59b_evidence_path: Path = DEFAULT_V59B_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
) -> AgenticDeWorkspaceContinuityHardeningRegister:
    if repo_root_path is None:
        root = repo_root(anchor=Path(__file__)).resolve()
    else:
        if repo_root_path.exists() and repo_root_path.is_symlink():
            raise ValueError("repository root may not be a symlink for V59-C continuity")
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
    v56c_lane_drift_path = _resolve_path(repo_root_path=root, path=v56c_lane_drift_path)
    v56c_runtime_harvest_path = _resolve_path(repo_root_path=root, path=v56c_runtime_harvest_path)
    v56c_governance_calibration_path = _resolve_path(
        repo_root_path=root, path=v56c_governance_calibration_path
    )
    v56c_migration_decision_path = _resolve_path(
        repo_root_path=root, path=v56c_migration_decision_path
    )
    v59a_lane_drift_path = _resolve_path(repo_root_path=root, path=v59a_lane_drift_path)
    v59a_continuity_region_path = _resolve_path(
        repo_root_path=root, path=v59a_continuity_region_path
    )
    v59a_continuity_admission_path = _resolve_path(
        repo_root_path=root, path=v59a_continuity_admission_path
    )
    v59a_occupancy_path = _resolve_path(repo_root_path=root, path=v59a_occupancy_path)
    v59a_live_turn_admission_path = _resolve_path(
        repo_root_path=root, path=v59a_live_turn_admission_path
    )
    v59a_live_turn_handoff_path = _resolve_path(
        repo_root_path=root, path=v59a_live_turn_handoff_path
    )
    v59a_observation_path = _resolve_path(repo_root_path=root, path=v59a_observation_path)
    v59a_local_effect_conformance_path = _resolve_path(
        repo_root_path=root, path=v59a_local_effect_conformance_path
    )
    v59a_live_turn_reintegration_path = _resolve_path(
        repo_root_path=root, path=v59a_live_turn_reintegration_path
    )
    v59a_continuity_reintegration_path = _resolve_path(
        repo_root_path=root, path=v59a_continuity_reintegration_path
    )
    v59b_lane_drift_path = _resolve_path(repo_root_path=root, path=v59b_lane_drift_path)
    v59b_continuity_restoration_handoff_path = _resolve_path(
        repo_root_path=root, path=v59b_continuity_restoration_handoff_path
    )
    v59b_restoration_path = _resolve_path(repo_root_path=root, path=v59b_restoration_path)
    v59b_continuity_restoration_reintegration_path = _resolve_path(
        repo_root_path=root, path=v59b_continuity_restoration_reintegration_path
    )
    lane_drift_path = _resolve_path(repo_root_path=root, path=lane_drift_path)
    v59a_evidence_path = _resolve_path(repo_root_path=root, path=v59a_evidence_path)
    v59b_evidence_path = _resolve_path(repo_root_path=root, path=v59b_evidence_path)

    _validate_v59c_lane_drift_record(load_lane_drift_record(lane_drift_path))
    _validate_v59b_lane_drift_record(load_lane_drift_record(v59b_lane_drift_path))
    _validate_v59a_lane_drift_record(load_lane_drift_record(v59a_lane_drift_path))
    _validate_v56b_lane_drift_record(load_lane_drift_record(v56b_lane_drift_path))
    _validate_v56c_lane_drift_record(load_lane_drift_record(v56c_lane_drift_path))
    _validate_v59a_evidence_payload(
        _load_json_object(v59a_evidence_path, error_label="V59-A evidence")
    )
    _validate_v59b_evidence_payload(
        _load_json_object(v59b_evidence_path, error_label="V59-B evidence")
    )

    packet = load_domain_packet(domain_packet_path)
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
    v56c_harvest = load_runtime_harvest_record(v56c_runtime_harvest_path)
    v56c_governance = load_governance_calibration_register(v56c_governance_calibration_path)
    v56c_migration = load_migration_decision_register(v56c_migration_decision_path)
    v59a_continuity_region = load_workspace_continuity_region_declaration(
        v59a_continuity_region_path
    )
    v59a_continuity_admission = load_workspace_continuity_admission_record(
        v59a_continuity_admission_path
    )
    v59a_occupancy = load_workspace_occupancy_report(v59a_occupancy_path)
    v59a_live_turn_admission = load_live_turn_admission_record(v59a_live_turn_admission_path)
    v59a_live_turn_handoff = load_live_turn_handoff_record(v59a_live_turn_handoff_path)
    v59a_observation = load_local_effect_observation_record(v59a_observation_path)
    v59a_conformance = load_local_effect_conformance_report(v59a_local_effect_conformance_path)
    v59a_live_turn_reintegration = load_live_turn_reintegration_report(
        v59a_live_turn_reintegration_path
    )
    v59a_continuity_reintegration = load_workspace_continuity_reintegration_report(
        v59a_continuity_reintegration_path
    )
    v59b_continuity_restoration_handoff = load_workspace_continuity_restoration_handoff_record(
        v59b_continuity_restoration_handoff_path
    )
    v59b_restoration = load_local_effect_restoration_record(v59b_restoration_path)
    v59b_continuity_restoration_reintegration = (
        load_workspace_continuity_restoration_reintegration_report(
            v59b_continuity_restoration_reintegration_path
        )
    )

    _validate_v56a_reference_surfaces(
        domain_packet=packet,
        morph_ir=morph_ir,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        diagnostics=v56a_diagnostics,
        conformance=v56a_conformance,
    )
    _validate_v56b_reference_surfaces(
        domain_packet=packet,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        taxonomy=v56b_taxonomy,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        diagnostics=v56b_diagnostics,
        conformance=v56b_conformance,
    )
    _validate_v57a_reference_surfaces(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        taxonomy=v56b_taxonomy,
        harvest=v56c_harvest,
        governance=v56c_governance,
        migration=v56c_migration,
    )
    _validate_v59a_workspace_continuity_surfaces(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        ticket=v56b_ticket,
        continuity_region=v59a_continuity_region,
        continuity_admission=v59a_continuity_admission,
        occupancy=v59a_occupancy,
        live_turn_admission=v59a_live_turn_admission,
        live_turn_handoff=v59a_live_turn_handoff,
        observation=v59a_observation,
        conformance=v59a_conformance,
        live_turn_reintegration=v59a_live_turn_reintegration,
        continuity_reintegration=v59a_continuity_reintegration,
        target_relative_path=target_relative_path,
    )
    _validate_v59b_workspace_continuity_restoration_surfaces(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        harvest=v56c_harvest,
        live_turn_admission=v59a_live_turn_admission,
        live_turn_handoff=v59a_live_turn_handoff,
        continuity_admission=v59a_continuity_admission,
        occupancy=v59a_occupancy,
        observation=v59a_observation,
        conformance=v59a_conformance,
        live_turn_reintegration=v59a_live_turn_reintegration,
        continuity_reintegration=v59a_continuity_reintegration,
        restoration=v59b_restoration,
        continuity_restoration_handoff=v59b_continuity_restoration_handoff,
        continuity_restoration_reintegration=v59b_continuity_restoration_reintegration,
        target_relative_path=target_relative_path,
    )

    evidence_refs = [
        _render_input_ref(repo_root_path=root, path=domain_packet_path),
        _render_input_ref(repo_root_path=root, path=morph_ir_path),
        _render_input_ref(repo_root_path=root, path=interaction_contract_path),
        _render_input_ref(repo_root_path=root, path=action_proposal_path),
        _render_input_ref(repo_root_path=root, path=v56a_checkpoint_path),
        _render_input_ref(repo_root_path=root, path=v56a_diagnostics_path),
        _render_input_ref(repo_root_path=root, path=v56a_conformance_path),
        _render_input_ref(repo_root_path=root, path=v56b_action_class_taxonomy_path),
        _render_input_ref(repo_root_path=root, path=v56b_runtime_state_path),
        _render_input_ref(repo_root_path=root, path=v56b_action_ticket_path),
        _render_input_ref(repo_root_path=root, path=v56b_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56b_diagnostics_path),
        _render_input_ref(repo_root_path=root, path=v56b_conformance_path),
        _render_input_ref(repo_root_path=root, path=v56c_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56c_runtime_harvest_path),
        _render_input_ref(repo_root_path=root, path=v56c_governance_calibration_path),
        _render_input_ref(repo_root_path=root, path=v56c_migration_decision_path),
        _render_input_ref(repo_root_path=root, path=v59a_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v59a_continuity_region_path),
        _render_input_ref(repo_root_path=root, path=v59a_continuity_admission_path),
        _render_input_ref(repo_root_path=root, path=v59a_occupancy_path),
        _render_input_ref(repo_root_path=root, path=v59a_live_turn_admission_path),
        _render_input_ref(repo_root_path=root, path=v59a_live_turn_handoff_path),
        _render_input_ref(repo_root_path=root, path=v59a_observation_path),
        _render_input_ref(repo_root_path=root, path=v59a_local_effect_conformance_path),
        _render_input_ref(repo_root_path=root, path=v59a_live_turn_reintegration_path),
        _render_input_ref(repo_root_path=root, path=v59a_continuity_reintegration_path),
        _render_input_ref(repo_root_path=root, path=v59b_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v59b_continuity_restoration_handoff_path),
        _render_input_ref(repo_root_path=root, path=v59b_restoration_path),
        _render_input_ref(
            repo_root_path=root,
            path=v59b_continuity_restoration_reintegration_path,
        ),
        _render_input_ref(repo_root_path=root, path=lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v59a_evidence_path),
        _render_input_ref(repo_root_path=root, path=v59b_evidence_path),
    ]
    return _build_v59c_workspace_continuity_hardening_register(
        continuity_admission=v59a_continuity_admission,
        occupancy=v59a_occupancy,
        continuity_reintegration=v59a_continuity_reintegration,
        live_turn_admission=v59a_live_turn_admission,
        live_turn_handoff=v59a_live_turn_handoff,
        live_turn_reintegration=v59a_live_turn_reintegration,
        continuity_restoration_handoff=v59b_continuity_restoration_handoff,
        restoration=v59b_restoration,
        continuity_restoration_reintegration=v59b_continuity_restoration_reintegration,
        observation=v59a_observation,
        conformance=v59a_conformance,
        evidence_refs=evidence_refs,
    )


def _expected_v60a_selected_downstream_path_summary(target_relative_path: str) -> str:
    return (
        "urm_copilot_session_path::local_write/create_new::"
        f"{DESIGNATED_WORKSPACE_CONTINUITY_ROOT.as_posix()}/{target_relative_path}"
    )


def _validate_v60a_seed_intent_record(
    *,
    seed_intent: AgenticDeSeedIntentRecord,
    target_relative_path: str,
) -> None:
    if seed_intent.target_arc != V60A_TARGET_ARC or seed_intent.target_path != V60A_TARGET_PATH:
        raise ValueError("V60-A seed intent record must target the shipped V60-A slice")
    if seed_intent.evidence_only is not True:
        raise ValueError("V60-A seed intent record must remain evidence-only")
    if seed_intent.changes_live_behavior_by_default:
        raise ValueError("V60-A seed intent record must not change live behavior by default")
    if seed_intent.seed_source_class != "typed_seed_intent_record":
        raise ValueError("V60-A seed ingress must remain typed and non-chat-native")
    expected_path_summary = _expected_v60a_selected_downstream_path_summary(target_relative_path)
    if seed_intent.selected_downstream_path_summary != expected_path_summary:
        raise ValueError(
            "V60-A seed intent must remain closed to the exact shipped downstream path"
        )


def _validate_v60a_current_session_posture(
    *,
    repo_root_path: Path,
    live_turn_snapshot: CopilotTurnSnapshot,
    live_turn_admission: AgenticDeLiveTurnAdmissionRecord,
    continuity_admission: AgenticDeWorkspaceContinuityAdmissionRecord,
    target_relative_path: str,
) -> tuple[str, str, str]:
    if live_turn_snapshot.session_id != live_turn_admission.live_session_id:
        raise ValueError("V60-A requires the same live session as the shipped V59-A lineage")
    if live_turn_snapshot.selected_turn_id != live_turn_admission.live_turn_id:
        raise ValueError("V60-A requires the same live turn as the shipped V59-A lineage")
    current_capability_snapshot = _session_capability_snapshot(live_turn_snapshot)
    current_approval_posture_snapshot = _approval_posture_snapshot(live_turn_snapshot)
    if current_capability_snapshot != live_turn_admission.session_capability_snapshot:
        raise ValueError(
            "V60-A current session capability snapshot must match the shipped V59-A "
            "admission posture"
        )
    if current_approval_posture_snapshot != live_turn_admission.approval_posture_snapshot:
        raise ValueError(
            "V60-A current approval posture snapshot must match the shipped V59-A "
            "admission posture"
        )
    cwd_resolved = _resolve_snapshot_cwd_path(
        repo_root_path=repo_root_path,
        raw_value=live_turn_snapshot.cwd,
        field_name="cwd",
    )
    if cwd_resolved != repo_root_path.resolve():
        raise ValueError("V60-A current cwd must resolve to the admitted repository root")
    if live_turn_snapshot.status not in {"starting", "running"}:
        raise ValueError("V60-A requires a live current session posture")
    if continuity_admission.continuity_verdict != "admitted":
        raise ValueError("V60-A requires admitted continuity lineage before continuation compile")
    expected_path_summary = _expected_v60a_selected_downstream_path_summary(target_relative_path)
    if live_turn_admission.selected_live_path_identity != expected_path_summary:
        raise ValueError("V60-A requires the shipped selected live path identity")
    witness_basis_summary = (
        "same-session same-turn continuation + current capability/approval posture match + "
        "repository-root cwd match + admitted continuity lineage"
    )
    return (
        current_capability_snapshot,
        current_approval_posture_snapshot,
        witness_basis_summary,
    )


def _validate_v60a_workspace_continuity_hardening_surface(
    *,
    hardening: AgenticDeWorkspaceContinuityHardeningRegister,
    continuity_admission: AgenticDeWorkspaceContinuityAdmissionRecord,
    occupancy: AgenticDeWorkspaceOccupancyReport,
    continuity_reintegration: AgenticDeWorkspaceContinuityReintegrationReport,
    live_turn_admission: AgenticDeLiveTurnAdmissionRecord,
    live_turn_handoff: AgenticDeLiveTurnHandoffRecord,
    live_turn_reintegration: AgenticDeLiveTurnReintegrationReport,
    continuity_restoration_handoff: AgenticDeWorkspaceContinuityRestorationHandoffRecord,
    restoration: AgenticDeLocalEffectRestorationRecord,
    continuity_restoration_reintegration: (
        AgenticDeWorkspaceContinuityRestorationReintegrationReport
    ),
    observation: AgenticDeLocalEffectObservationRecord,
    conformance: AgenticDeLocalEffectConformanceReport,
) -> None:
    if hardening.target_arc != V59C_TARGET_ARC or hardening.target_path != V59C_TARGET_PATH:
        raise ValueError("V60-A requires the shipped V59-C continuity hardening surface")
    if hardening.advisory_only is not True:
        raise ValueError("V60-A requires the shipped advisory-only V59-C posture")
    if hardening.path_level_only is not True:
        raise ValueError("V60-A requires the shipped path-level-only V59-C posture")
    if hardening.recommendation_function_extensional_and_replayable is not True:
        raise ValueError("V60-A requires the shipped replayable V59-C recommendation posture")
    if hardening.explicit_frozen_policy_anchor_required is not True:
        raise ValueError("V60-A requires the shipped frozen-policy V59-C posture")
    if hardening.lineage_root_non_independence_dedup_applied is not True:
        raise ValueError("V60-A requires the shipped V59-C lineage-root dedup posture")
    if hardening.entry_count != 1:
        raise ValueError("V60-A requires exactly one shipped V59-C hardening entry")
    entry = hardening.entries[0]
    if entry.continuity_admission_ref != continuity_admission.continuity_admission_id:
        raise ValueError("V59-C hardening does not bind the shipped continuity admission")
    if entry.occupancy_report_ref != occupancy.occupancy_report_id:
        raise ValueError("V59-C hardening does not bind the shipped occupancy report")
    if entry.continuity_reintegration_ref != continuity_reintegration.report_id:
        raise ValueError("V59-C hardening does not bind the shipped continuity reintegration")
    if entry.turn_admission_ref != live_turn_admission.admission_id:
        raise ValueError("V59-C hardening does not bind the shipped live admission")
    if entry.turn_handoff_ref != live_turn_handoff.handoff_id:
        raise ValueError("V59-C hardening does not bind the shipped live handoff")
    if entry.turn_reintegration_ref != live_turn_reintegration.report_id:
        raise ValueError("V59-C hardening does not bind the shipped live reintegration")
    if (
        entry.workspace_continuity_restoration_handoff_ref
        != continuity_restoration_handoff.handoff_id
    ):
        raise ValueError(
            "V59-C hardening does not bind the shipped continuity restoration handoff"
        )
    if entry.restoration_ref != restoration.restoration_id:
        raise ValueError("V59-C hardening does not bind the shipped restoration record")
    if (
        entry.workspace_continuity_restoration_reintegration_ref
        != continuity_restoration_reintegration.report_id
    ):
        raise ValueError(
            "V59-C hardening does not bind the shipped continuity restoration reintegration"
        )
    if entry.observation_ref != observation.observation_id:
        raise ValueError("V59-C hardening does not bind the shipped observation")
    if entry.local_effect_conformance_ref != conformance.report_id:
        raise ValueError("V59-C hardening does not bind the shipped conformance")
    if entry.selected_hardening_target_surface != (
        "observed_and_restored_continuity_bound_create_new_exemplar_only"
    ):
        raise ValueError("V60-A requires the shipped V59-C hardening target surface")
    if (
        entry.frozen_policy_ref
        != "docs/LOCKED_CONTINUATION_vNEXT_PLUS163.md#machine-checkable-contract"
    ):
        raise ValueError("V60-A requires the shipped V59-C frozen policy anchor")
    if entry.recommended_outcome != "candidate_for_later_continuity_hardening":
        raise ValueError("V60-A requires the shipped V59-C candidate continuity posture")
    if entry.occupancy_verdict != "unoccupied":
        raise ValueError("V60-A requires the shipped unoccupied V59-C occupancy posture")
    if entry.continuity_reintegration_status != "reintegrated":
        raise ValueError("V60-A requires the shipped reintegrated V59-A continuity posture")
    if entry.restoration_time_continuation_verdict != "continued":
        raise ValueError("V60-A requires the shipped continued V59-B restoration posture")
    if entry.prior_governed_state_baseline_match_verdict != "matched":
        raise ValueError("V60-A requires the shipped matched V59-B baseline posture")
    if entry.bounded_compensating_scope_match_verdict != "matched":
        raise ValueError("V60-A requires the shipped matched V59-B compensating scope posture")
    if entry.observation_boundedness_verdict != "bounded":
        raise ValueError("V60-A requires the shipped bounded observation posture")
    if entry.restoration_boundedness_verdict != "bounded":
        raise ValueError("V60-A requires the shipped bounded restoration posture")
    if entry.continuity_restoration_reintegration_status != "reintegrated":
        raise ValueError(
            "V60-A requires the shipped reintegrated V59-B continuity restoration posture"
        )


def _build_v60a_task_charter_packet(
    *,
    seed_intent: AgenticDeSeedIntentRecord,
    evidence_refs: list[str],
) -> AgenticDeTaskCharterPacket:
    field_origin_tags = {
        "charter_scope_summary": "current_turn_derived",
        "completion_test_summary": "current_turn_derived",
        "stop_condition_summary": "current_turn_derived",
        "required_imports_summary": "current_turn_derived",
        "selected_downstream_path_summary": "current_turn_derived",
        "frozen_policy_basis_ref": "shaping_only",
        "charter_compilation_basis_summary": "current_turn_derived",
    }
    field_dependence_tags = {
        "charter_scope_summary": [seed_intent.seed_intent_id, V60A_FROZEN_POLICY_REF],
        "completion_test_summary": [seed_intent.seed_intent_id, V60A_FROZEN_POLICY_REF],
        "stop_condition_summary": [seed_intent.seed_intent_id, V60A_FROZEN_POLICY_REF],
        "required_imports_summary": [seed_intent.seed_intent_id, V60A_FROZEN_POLICY_REF],
        "selected_downstream_path_summary": [seed_intent.seed_intent_id],
        "frozen_policy_basis_ref": [],
        "charter_compilation_basis_summary": [seed_intent.seed_intent_id, V60A_FROZEN_POLICY_REF],
    }
    return AgenticDeTaskCharterPacket(
        target_arc=V60A_TARGET_ARC,
        target_path=V60A_TARGET_PATH,
        seed_intent_ref=seed_intent.seed_intent_id,
        charter_scope_summary=(
            "compile bounded task law over the exact shipped V59 continuity-bound "
            "local_write/create_new exemplar only"
        ),
        completion_test_summary=seed_intent.declared_completion_test_summary,
        stop_condition_summary=seed_intent.declared_stop_condition_summary,
        required_imports_summary=(
            "typed seed intent + frozen V60-A policy + shipped V59 continuity/reintegration/"
            "restoration/hardening lineage only"
        ),
        selected_downstream_path_summary=seed_intent.selected_downstream_path_summary,
        frozen_policy_basis_ref=V60A_FROZEN_POLICY_REF,
        charter_compilation_basis_summary=(
            "typed seed intent + frozen policy anchor + exact shipped downstream path freeze"
        ),
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        evidence_refs=[seed_intent.seed_intent_id, *evidence_refs],
    )


def _build_v60a_task_residual_packet(
    *,
    live_turn_snapshot: CopilotTurnSnapshot,
    task_charter: AgenticDeTaskCharterPacket,
    live_turn_reintegration: AgenticDeLiveTurnReintegrationReport,
    continuity_reintegration: AgenticDeWorkspaceContinuityReintegrationReport,
    continuity_restoration_reintegration: (
        AgenticDeWorkspaceContinuityRestorationReintegrationReport
    ),
    hardening: AgenticDeWorkspaceContinuityHardeningRegister,
    current_session_witness_basis_summary: str,
    evidence_refs: list[str],
) -> AgenticDeTaskResidualPacket:
    hardening_entry = hardening.entries[0]
    field_origin_tags = {
        "current_frontier_summary": "current_turn_derived",
        "open_obligation_summary": "current_turn_derived",
        "blocker_summary": "current_turn_derived",
        "owed_communication_posture_summary": "current_turn_derived",
        "residual_derivation_basis_summary": "current_turn_derived",
    }
    field_dependence_tags = {
        "current_frontier_summary": [
            task_charter.charter_id,
            continuity_reintegration.report_id,
            continuity_restoration_reintegration.report_id,
        ],
        "open_obligation_summary": [
            task_charter.charter_id,
            hardening.register_id,
            V60A_FROZEN_POLICY_REF,
        ],
        "blocker_summary": [
            live_turn_reintegration.report_id,
            continuity_reintegration.report_id,
            continuity_restoration_reintegration.report_id,
        ],
        "owed_communication_posture_summary": [
            task_charter.charter_id,
            V60A_FROZEN_POLICY_REF,
        ],
        "residual_derivation_basis_summary": [
            task_charter.charter_id,
            live_turn_reintegration.report_id,
            continuity_reintegration.report_id,
            continuity_restoration_reintegration.report_id,
            hardening.register_id,
        ],
    }
    root_origin_ids = [
        f"session:{live_turn_snapshot.session_id}",
        f"turn:{live_turn_snapshot.selected_turn_id}",
        f"charter:{task_charter.charter_id}",
        f"live_reintegration:{live_turn_reintegration.report_id}",
        f"continuity_reintegration:{continuity_reintegration.report_id}",
        f"continuity_restoration_reintegration:{continuity_restoration_reintegration.report_id}",
        f"hardening:{hardening_entry.hardening_id}",
        f"policy:{V60A_FROZEN_POLICY_REF}",
    ]
    return AgenticDeTaskResidualPacket(
        target_arc=V60A_TARGET_ARC,
        target_path=V60A_TARGET_PATH,
        task_charter_ref=task_charter.charter_id,
        latest_live_turn_reintegration_ref_or_none=live_turn_reintegration.report_id,
        latest_continuity_reintegration_ref_or_none=continuity_reintegration.report_id,
        current_frontier_summary=(
            "exact downstream frontier remains the shipped V59 continuity-bound "
            "local_write/create_new exemplar over runtime/reference_patch_candidate.diff"
        ),
        open_obligation_summary=(
            "if continued, descend only into the exact shipped downstream path under fresh "
            "V58/V56 act law; broader communication, replay, and repo widening remain deferred"
        ),
        blocker_summary="none_under_current_v60a_policy",
        open_approval_refs=[],
        owed_communication_posture_summary=(
            "none_now; emit_governed_communication remains posture-only until V61"
        ),
        residual_derivation_basis_summary=(
            "task charter + shipped live/continuity reintegration lineage + shipped "
            "continuity-safe restoration reintegration + shipped V59-C advisory hardening + "
            f"{current_session_witness_basis_summary}"
        ),
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=root_origin_ids,
        evidence_refs=[
            task_charter.charter_id,
            live_turn_reintegration.report_id,
            continuity_reintegration.report_id,
            continuity_restoration_reintegration.report_id,
            hardening.register_id,
            *evidence_refs,
        ],
    )


def _build_v60a_loop_state_ledger(
    *,
    live_turn_snapshot: CopilotTurnSnapshot,
    task_charter: AgenticDeTaskCharterPacket,
    task_residual: AgenticDeTaskResidualPacket,
    continuity_region: AgenticDeWorkspaceContinuityRegionDeclaration,
    live_turn_reintegration: AgenticDeLiveTurnReintegrationReport,
    continuity_reintegration: AgenticDeWorkspaceContinuityReintegrationReport,
    evidence_refs: list[str],
) -> AgenticDeLoopStateLedger:
    loop_prefix_identity = (
        f"{live_turn_snapshot.session_id}::{live_turn_snapshot.selected_turn_id}::"
        f"{task_charter.selected_downstream_path_summary}"
    )
    field_origin_tags = {
        "resident_session_ref": "current_turn_native",
        "continuity_region_ref": "prior_artifact",
        "loop_prefix_identity": "current_turn_derived",
    }
    field_dependence_tags = {
        "resident_session_ref": [],
        "continuity_region_ref": [],
        "loop_prefix_identity": [
            task_charter.charter_id,
            task_residual.residual_id,
            live_turn_snapshot.session_id,
            live_turn_snapshot.selected_turn_id,
        ],
    }
    root_origin_ids = [
        f"session:{live_turn_snapshot.session_id}",
        f"turn:{live_turn_snapshot.selected_turn_id}",
        f"charter:{task_charter.charter_id}",
        f"residual:{task_residual.residual_id}",
        f"continuity_region:{continuity_region.continuity_region_id}",
        f"live_reintegration:{live_turn_reintegration.report_id}",
        f"continuity_reintegration:{continuity_reintegration.report_id}",
    ]
    return AgenticDeLoopStateLedger(
        target_arc=V60A_TARGET_ARC,
        target_path=V60A_TARGET_PATH,
        task_charter_ref=task_charter.charter_id,
        task_residual_ref=task_residual.residual_id,
        resident_session_ref=live_turn_snapshot.session_id,
        continuity_region_ref=continuity_region.continuity_region_id,
        latest_live_turn_reintegration_ref_or_none=live_turn_reintegration.report_id,
        latest_continuity_reintegration_ref_or_none=continuity_reintegration.report_id,
        open_approval_refs=[],
        loop_prefix_identity=loop_prefix_identity,
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=root_origin_ids,
        evidence_refs=[
            task_charter.charter_id,
            task_residual.residual_id,
            continuity_region.continuity_region_id,
            live_turn_reintegration.report_id,
            continuity_reintegration.report_id,
            *evidence_refs,
        ],
    )


def _build_v60a_continuation_decision_record(
    *,
    live_turn_snapshot: CopilotTurnSnapshot,
    loop_state_ledger: AgenticDeLoopStateLedger,
    seed_intent: AgenticDeSeedIntentRecord,
    task_charter: AgenticDeTaskCharterPacket,
    task_residual: AgenticDeTaskResidualPacket,
    hardening: AgenticDeWorkspaceContinuityHardeningRegister,
    evidence_refs: list[str],
) -> AgenticDeContinuationDecisionRecord:
    selected_next_path_summary = seed_intent.selected_downstream_path_summary
    continuation_reason_codes = [
        "typed_seed_intent_compiled",
        "task_charter_replayable",
        "task_residual_derived_not_authorizing",
        "exact_v59_downstream_path_selected",
        "single_step_local_ticket_duration_preserved",
        "communication_law_still_deferred_to_v61",
    ]
    field_origin_tags = {
        "continuation_outcome": "current_turn_derived",
        "frozen_policy_anchor_ref": "shaping_only",
        "evidence_basis_summary": "current_turn_derived",
        "selected_next_path_summary": "current_turn_derived",
    }
    field_dependence_tags = {
        "continuation_outcome": [
            loop_state_ledger.ledger_id,
            hardening.register_id,
            V60A_FROZEN_POLICY_REF,
        ],
        "frozen_policy_anchor_ref": [],
        "evidence_basis_summary": [
            seed_intent.seed_intent_id,
            task_charter.charter_id,
            task_residual.residual_id,
            loop_state_ledger.ledger_id,
            hardening.register_id,
        ],
        "selected_next_path_summary": [
            seed_intent.seed_intent_id,
            loop_state_ledger.ledger_id,
        ],
    }
    root_origin_ids = [
        f"session:{live_turn_snapshot.session_id}",
        f"turn:{live_turn_snapshot.selected_turn_id}",
        f"seed:{seed_intent.seed_intent_id}",
        f"charter:{task_charter.charter_id}",
        f"residual:{task_residual.residual_id}",
        f"loop:{loop_state_ledger.ledger_id}",
        f"hardening:{hardening.entries[0].hardening_id}",
        f"policy:{V60A_FROZEN_POLICY_REF}",
    ]
    return AgenticDeContinuationDecisionRecord(
        target_arc=V60A_TARGET_ARC,
        target_path=V60A_TARGET_PATH,
        loop_state_ledger_ref=loop_state_ledger.ledger_id,
        continuation_outcome="continue_to_governed_act",
        continuation_reason_codes=continuation_reason_codes,
        frozen_policy_anchor_ref=V60A_FROZEN_POLICY_REF,
        evidence_basis_summary=(
            "typed seed intent + replayable charter + derived residual + shipped V59 "
            "continuity/restoration/hardening lineage + frozen V60-A policy anchor"
        ),
        selected_next_path_summary=selected_next_path_summary,
        field_origin_tags=field_origin_tags,
        field_dependence_tags=field_dependence_tags,
        root_origin_ids=root_origin_ids,
        evidence_refs=[
            seed_intent.seed_intent_id,
            task_charter.charter_id,
            task_residual.residual_id,
            loop_state_ledger.ledger_id,
            hardening.register_id,
            *evidence_refs,
        ],
    )


def run_agentic_de_continuation_v60a(
    *,
    live_turn_snapshot: CopilotTurnSnapshot,
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
    v56c_lane_drift_path: Path = DEFAULT_V56C_LANE_DRIFT_PATH,
    v56c_runtime_harvest_path: Path = DEFAULT_V56C_RUNTIME_HARVEST_PATH,
    v56c_governance_calibration_path: Path = DEFAULT_V56C_GOVERNANCE_CALIBRATION_PATH,
    v56c_migration_decision_path: Path = DEFAULT_V56C_MIGRATION_DECISION_PATH,
    v59a_lane_drift_path: Path = DEFAULT_V59A_LANE_DRIFT_PATH,
    v59a_continuity_region_path: Path = DEFAULT_V59A_CONTINUITY_REGION_DECLARATION_PATH,
    v59a_continuity_admission_path: Path = DEFAULT_V59A_CONTINUITY_ADMISSION_PATH,
    v59a_occupancy_path: Path = DEFAULT_V59A_OCCUPANCY_REPORT_PATH,
    v59a_live_turn_admission_path: Path = DEFAULT_V59A_LIVE_TURN_ADMISSION_PATH,
    v59a_live_turn_handoff_path: Path = DEFAULT_V59A_LIVE_TURN_HANDOFF_PATH,
    v59a_observation_path: Path = DEFAULT_V59A_OBSERVATION_PATH,
    v59a_local_effect_conformance_path: Path = DEFAULT_V59A_LOCAL_EFFECT_CONFORMANCE_PATH,
    v59a_live_turn_reintegration_path: Path = DEFAULT_V59A_LIVE_TURN_REINTEGRATION_PATH,
    v59a_continuity_reintegration_path: Path = DEFAULT_V59A_CONTINUITY_REINTEGRATION_PATH,
    v59b_lane_drift_path: Path = DEFAULT_V59B_LANE_DRIFT_PATH,
    v59b_continuity_restoration_handoff_path: Path = (
        DEFAULT_V59B_CONTINUITY_RESTORATION_HANDOFF_PATH
    ),
    v59b_restoration_path: Path = DEFAULT_V59B_RESTORATION_PATH,
    v59b_continuity_restoration_reintegration_path: Path = (
        DEFAULT_V59B_CONTINUITY_RESTORATION_REINTEGRATION_PATH
    ),
    v59c_lane_drift_path: Path = DEFAULT_V59C_LANE_DRIFT_PATH,
    v59c_hardening_path: Path = DEFAULT_V59C_HARDENING_PATH,
    lane_drift_path: Path = DEFAULT_V60A_LANE_DRIFT_PATH,
    seed_intent_path: Path = DEFAULT_V60A_SEED_INTENT_PATH,
    v56a_evidence_path: Path = DEFAULT_V56C_V56A_EVIDENCE_PATH,
    v56b_evidence_path: Path = DEFAULT_V56C_V56B_EVIDENCE_PATH,
    v56c_evidence_path: Path = DEFAULT_V57A_V56C_EVIDENCE_PATH,
    v57a_evidence_path: Path = DEFAULT_V57A_EVIDENCE_PATH,
    v57b_evidence_path: Path = DEFAULT_V57B_EVIDENCE_PATH,
    v57c_evidence_path: Path = DEFAULT_V57C_EVIDENCE_PATH,
    v58a_evidence_path: Path = DEFAULT_V58A_EVIDENCE_PATH,
    v58b_evidence_path: Path = DEFAULT_V58B_EVIDENCE_PATH,
    v58c_evidence_path: Path = DEFAULT_V58C_EVIDENCE_PATH,
    v59a_evidence_path: Path = DEFAULT_V59A_EVIDENCE_PATH,
    v59b_evidence_path: Path = DEFAULT_V59B_EVIDENCE_PATH,
    v59c_evidence_path: Path = DEFAULT_V59C_EVIDENCE_PATH,
    target_relative_path: str = str(DEFAULT_WORKSPACE_CONTINUITY_TARGET_RELATIVE_PATH),
) -> tuple[
    AgenticDeSeedIntentRecord,
    AgenticDeTaskCharterPacket,
    AgenticDeTaskResidualPacket,
    AgenticDeLoopStateLedger,
    AgenticDeContinuationDecisionRecord,
]:
    if repo_root_path is None:
        root = repo_root(anchor=Path(__file__)).resolve()
    else:
        if repo_root_path.exists() and repo_root_path.is_symlink():
            raise ValueError("repository root may not be a symlink for V60-A continuation")
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
    v56c_lane_drift_path = _resolve_path(repo_root_path=root, path=v56c_lane_drift_path)
    v56c_runtime_harvest_path = _resolve_path(repo_root_path=root, path=v56c_runtime_harvest_path)
    v56c_governance_calibration_path = _resolve_path(
        repo_root_path=root, path=v56c_governance_calibration_path
    )
    v56c_migration_decision_path = _resolve_path(
        repo_root_path=root, path=v56c_migration_decision_path
    )
    v59a_lane_drift_path = _resolve_path(repo_root_path=root, path=v59a_lane_drift_path)
    v59a_continuity_region_path = _resolve_path(
        repo_root_path=root, path=v59a_continuity_region_path
    )
    v59a_continuity_admission_path = _resolve_path(
        repo_root_path=root, path=v59a_continuity_admission_path
    )
    v59a_occupancy_path = _resolve_path(repo_root_path=root, path=v59a_occupancy_path)
    v59a_live_turn_admission_path = _resolve_path(
        repo_root_path=root, path=v59a_live_turn_admission_path
    )
    v59a_live_turn_handoff_path = _resolve_path(
        repo_root_path=root, path=v59a_live_turn_handoff_path
    )
    v59a_observation_path = _resolve_path(repo_root_path=root, path=v59a_observation_path)
    v59a_local_effect_conformance_path = _resolve_path(
        repo_root_path=root, path=v59a_local_effect_conformance_path
    )
    v59a_live_turn_reintegration_path = _resolve_path(
        repo_root_path=root, path=v59a_live_turn_reintegration_path
    )
    v59a_continuity_reintegration_path = _resolve_path(
        repo_root_path=root, path=v59a_continuity_reintegration_path
    )
    v59b_lane_drift_path = _resolve_path(repo_root_path=root, path=v59b_lane_drift_path)
    v59b_continuity_restoration_handoff_path = _resolve_path(
        repo_root_path=root, path=v59b_continuity_restoration_handoff_path
    )
    v59b_restoration_path = _resolve_path(repo_root_path=root, path=v59b_restoration_path)
    v59b_continuity_restoration_reintegration_path = _resolve_path(
        repo_root_path=root, path=v59b_continuity_restoration_reintegration_path
    )
    v59c_lane_drift_path = _resolve_path(repo_root_path=root, path=v59c_lane_drift_path)
    v59c_hardening_path = _resolve_path(repo_root_path=root, path=v59c_hardening_path)
    lane_drift_path = _resolve_path(repo_root_path=root, path=lane_drift_path)
    seed_intent_path = _resolve_path(repo_root_path=root, path=seed_intent_path)
    v56a_evidence_path = _resolve_path(repo_root_path=root, path=v56a_evidence_path)
    v56b_evidence_path = _resolve_path(repo_root_path=root, path=v56b_evidence_path)
    v56c_evidence_path = _resolve_path(repo_root_path=root, path=v56c_evidence_path)
    v57a_evidence_path = _resolve_path(repo_root_path=root, path=v57a_evidence_path)
    v57b_evidence_path = _resolve_path(repo_root_path=root, path=v57b_evidence_path)
    v57c_evidence_path = _resolve_path(repo_root_path=root, path=v57c_evidence_path)
    v58a_evidence_path = _resolve_path(repo_root_path=root, path=v58a_evidence_path)
    v58b_evidence_path = _resolve_path(repo_root_path=root, path=v58b_evidence_path)
    v58c_evidence_path = _resolve_path(repo_root_path=root, path=v58c_evidence_path)
    v59a_evidence_path = _resolve_path(repo_root_path=root, path=v59a_evidence_path)
    v59b_evidence_path = _resolve_path(repo_root_path=root, path=v59b_evidence_path)
    v59c_evidence_path = _resolve_path(repo_root_path=root, path=v59c_evidence_path)

    _validate_v60a_lane_drift_record(load_lane_drift_record(lane_drift_path))
    _validate_v59c_lane_drift_record(load_lane_drift_record(v59c_lane_drift_path))
    _validate_v59b_lane_drift_record(load_lane_drift_record(v59b_lane_drift_path))
    _validate_v59a_lane_drift_record(load_lane_drift_record(v59a_lane_drift_path))
    _validate_v56b_lane_drift_record(load_lane_drift_record(v56b_lane_drift_path))
    _validate_v56c_lane_drift_record(load_lane_drift_record(v56c_lane_drift_path))
    _validate_v56a_evidence_payload(
        _load_json_object(v56a_evidence_path, error_label="V56-A evidence")
    )
    _validate_v56b_evidence_payload(
        _load_json_object(v56b_evidence_path, error_label="V56-B evidence")
    )
    _validate_v56c_evidence_payload(
        _load_json_object(v56c_evidence_path, error_label="V56-C evidence")
    )
    _validate_v57a_evidence_payload(
        _load_json_object(v57a_evidence_path, error_label="V57-A evidence")
    )
    _validate_v57b_evidence_payload(
        _load_json_object(v57b_evidence_path, error_label="V57-B evidence")
    )
    _validate_v57c_evidence_payload(
        _load_json_object(v57c_evidence_path, error_label="V57-C evidence")
    )
    _validate_v58a_evidence_payload(
        _load_json_object(v58a_evidence_path, error_label="V58-A evidence")
    )
    _validate_v58b_evidence_payload(
        _load_json_object(v58b_evidence_path, error_label="V58-B evidence")
    )
    _validate_v58c_evidence_payload(
        _load_json_object(v58c_evidence_path, error_label="V58-C evidence")
    )
    _validate_v59a_evidence_payload(
        _load_json_object(v59a_evidence_path, error_label="V59-A evidence")
    )
    _validate_v59b_evidence_payload(
        _load_json_object(v59b_evidence_path, error_label="V59-B evidence")
    )
    _validate_v59c_evidence_payload(
        _load_json_object(v59c_evidence_path, error_label="V59-C evidence")
    )

    packet = load_domain_packet(domain_packet_path)
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
    v56c_harvest = load_runtime_harvest_record(v56c_runtime_harvest_path)
    v56c_governance = load_governance_calibration_register(v56c_governance_calibration_path)
    v56c_migration = load_migration_decision_register(v56c_migration_decision_path)
    v59a_continuity_region = load_workspace_continuity_region_declaration(
        v59a_continuity_region_path
    )
    v59a_continuity_admission = load_workspace_continuity_admission_record(
        v59a_continuity_admission_path
    )
    v59a_occupancy = load_workspace_occupancy_report(v59a_occupancy_path)
    v59a_live_turn_admission = load_live_turn_admission_record(v59a_live_turn_admission_path)
    v59a_live_turn_handoff = load_live_turn_handoff_record(v59a_live_turn_handoff_path)
    v59a_observation = load_local_effect_observation_record(v59a_observation_path)
    v59a_conformance = load_local_effect_conformance_report(v59a_local_effect_conformance_path)
    v59a_live_turn_reintegration = load_live_turn_reintegration_report(
        v59a_live_turn_reintegration_path
    )
    v59a_continuity_reintegration = load_workspace_continuity_reintegration_report(
        v59a_continuity_reintegration_path
    )
    v59b_continuity_restoration_handoff = load_workspace_continuity_restoration_handoff_record(
        v59b_continuity_restoration_handoff_path
    )
    v59b_restoration = load_local_effect_restoration_record(v59b_restoration_path)
    v59b_continuity_restoration_reintegration = (
        load_workspace_continuity_restoration_reintegration_report(
            v59b_continuity_restoration_reintegration_path
        )
    )
    v59c_hardening = load_workspace_continuity_hardening_register(v59c_hardening_path)
    seed_intent = load_seed_intent_record(seed_intent_path)

    _validate_v56a_reference_surfaces(
        domain_packet=packet,
        morph_ir=morph_ir,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        diagnostics=v56a_diagnostics,
        conformance=v56a_conformance,
    )
    _validate_v56b_reference_surfaces(
        domain_packet=packet,
        contract=contract,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        taxonomy=v56b_taxonomy,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        diagnostics=v56b_diagnostics,
        conformance=v56b_conformance,
    )
    _validate_v57a_reference_surfaces(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        taxonomy=v56b_taxonomy,
        harvest=v56c_harvest,
        governance=v56c_governance,
        migration=v56c_migration,
    )
    _validate_v59a_workspace_continuity_surfaces(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        ticket=v56b_ticket,
        continuity_region=v59a_continuity_region,
        continuity_admission=v59a_continuity_admission,
        occupancy=v59a_occupancy,
        live_turn_admission=v59a_live_turn_admission,
        live_turn_handoff=v59a_live_turn_handoff,
        observation=v59a_observation,
        conformance=v59a_conformance,
        live_turn_reintegration=v59a_live_turn_reintegration,
        continuity_reintegration=v59a_continuity_reintegration,
        target_relative_path=target_relative_path,
    )
    _validate_v59b_workspace_continuity_restoration_surfaces(
        packet=packet,
        proposal=proposal,
        checkpoint=v56a_checkpoint,
        runtime_state=v56b_runtime_state,
        ticket=v56b_ticket,
        harvest=v56c_harvest,
        live_turn_admission=v59a_live_turn_admission,
        live_turn_handoff=v59a_live_turn_handoff,
        continuity_admission=v59a_continuity_admission,
        occupancy=v59a_occupancy,
        observation=v59a_observation,
        conformance=v59a_conformance,
        live_turn_reintegration=v59a_live_turn_reintegration,
        continuity_reintegration=v59a_continuity_reintegration,
        restoration=v59b_restoration,
        continuity_restoration_handoff=v59b_continuity_restoration_handoff,
        continuity_restoration_reintegration=v59b_continuity_restoration_reintegration,
        target_relative_path=target_relative_path,
    )
    _validate_v60a_workspace_continuity_hardening_surface(
        hardening=v59c_hardening,
        continuity_admission=v59a_continuity_admission,
        occupancy=v59a_occupancy,
        continuity_reintegration=v59a_continuity_reintegration,
        live_turn_admission=v59a_live_turn_admission,
        live_turn_handoff=v59a_live_turn_handoff,
        live_turn_reintegration=v59a_live_turn_reintegration,
        continuity_restoration_handoff=v59b_continuity_restoration_handoff,
        restoration=v59b_restoration,
        continuity_restoration_reintegration=v59b_continuity_restoration_reintegration,
        observation=v59a_observation,
        conformance=v59a_conformance,
    )
    (
        _current_capability_snapshot,
        _current_approval_posture_snapshot,
        current_session_witness_basis_summary,
    ) = _validate_v60a_current_session_posture(
        repo_root_path=root,
        live_turn_snapshot=live_turn_snapshot,
        live_turn_admission=v59a_live_turn_admission,
        continuity_admission=v59a_continuity_admission,
        target_relative_path=target_relative_path,
    )
    _validate_v60a_seed_intent_record(
        seed_intent=seed_intent,
        target_relative_path=target_relative_path,
    )

    base_evidence_refs = [
        _render_input_ref(repo_root_path=root, path=domain_packet_path),
        _render_input_ref(repo_root_path=root, path=morph_ir_path),
        _render_input_ref(repo_root_path=root, path=interaction_contract_path),
        _render_input_ref(repo_root_path=root, path=action_proposal_path),
        _render_input_ref(repo_root_path=root, path=v56a_checkpoint_path),
        _render_input_ref(repo_root_path=root, path=v56a_diagnostics_path),
        _render_input_ref(repo_root_path=root, path=v56a_conformance_path),
        _render_input_ref(repo_root_path=root, path=v56b_action_class_taxonomy_path),
        _render_input_ref(repo_root_path=root, path=v56b_runtime_state_path),
        _render_input_ref(repo_root_path=root, path=v56b_action_ticket_path),
        _render_input_ref(repo_root_path=root, path=v56b_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56b_diagnostics_path),
        _render_input_ref(repo_root_path=root, path=v56b_conformance_path),
        _render_input_ref(repo_root_path=root, path=v56c_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v56c_runtime_harvest_path),
        _render_input_ref(repo_root_path=root, path=v56c_governance_calibration_path),
        _render_input_ref(repo_root_path=root, path=v56c_migration_decision_path),
        _render_input_ref(repo_root_path=root, path=v59a_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v59a_continuity_region_path),
        _render_input_ref(repo_root_path=root, path=v59a_continuity_admission_path),
        _render_input_ref(repo_root_path=root, path=v59a_occupancy_path),
        _render_input_ref(repo_root_path=root, path=v59a_live_turn_admission_path),
        _render_input_ref(repo_root_path=root, path=v59a_live_turn_handoff_path),
        _render_input_ref(repo_root_path=root, path=v59a_observation_path),
        _render_input_ref(repo_root_path=root, path=v59a_local_effect_conformance_path),
        _render_input_ref(repo_root_path=root, path=v59a_live_turn_reintegration_path),
        _render_input_ref(repo_root_path=root, path=v59a_continuity_reintegration_path),
        _render_input_ref(repo_root_path=root, path=v59b_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v59b_continuity_restoration_handoff_path),
        _render_input_ref(repo_root_path=root, path=v59b_restoration_path),
        _render_input_ref(
            repo_root_path=root,
            path=v59b_continuity_restoration_reintegration_path,
        ),
        _render_input_ref(repo_root_path=root, path=v59c_lane_drift_path),
        _render_input_ref(repo_root_path=root, path=v59c_hardening_path),
        _render_input_ref(repo_root_path=root, path=lane_drift_path),
        _render_input_ref(repo_root_path=root, path=seed_intent_path),
        _render_input_ref(repo_root_path=root, path=v56a_evidence_path),
        _render_input_ref(repo_root_path=root, path=v56b_evidence_path),
        _render_input_ref(repo_root_path=root, path=v56c_evidence_path),
        _render_input_ref(repo_root_path=root, path=v57a_evidence_path),
        _render_input_ref(repo_root_path=root, path=v57b_evidence_path),
        _render_input_ref(repo_root_path=root, path=v57c_evidence_path),
        _render_input_ref(repo_root_path=root, path=v58a_evidence_path),
        _render_input_ref(repo_root_path=root, path=v58b_evidence_path),
        _render_input_ref(repo_root_path=root, path=v58c_evidence_path),
        _render_input_ref(repo_root_path=root, path=v59a_evidence_path),
        _render_input_ref(repo_root_path=root, path=v59b_evidence_path),
        _render_input_ref(repo_root_path=root, path=v59c_evidence_path),
        *_snapshot_observability_refs(
            repo_root_path=root,
            live_turn_snapshot=live_turn_snapshot,
        ),
    ]
    task_charter = _build_v60a_task_charter_packet(
        seed_intent=seed_intent,
        evidence_refs=base_evidence_refs,
    )
    task_residual = _build_v60a_task_residual_packet(
        live_turn_snapshot=live_turn_snapshot,
        task_charter=task_charter,
        live_turn_reintegration=v59a_live_turn_reintegration,
        continuity_reintegration=v59a_continuity_reintegration,
        continuity_restoration_reintegration=v59b_continuity_restoration_reintegration,
        hardening=v59c_hardening,
        current_session_witness_basis_summary=current_session_witness_basis_summary,
        evidence_refs=base_evidence_refs,
    )
    loop_state_ledger = _build_v60a_loop_state_ledger(
        live_turn_snapshot=live_turn_snapshot,
        task_charter=task_charter,
        task_residual=task_residual,
        continuity_region=v59a_continuity_region,
        live_turn_reintegration=v59a_live_turn_reintegration,
        continuity_reintegration=v59a_continuity_reintegration,
        evidence_refs=base_evidence_refs,
    )
    continuation_decision = _build_v60a_continuation_decision_record(
        live_turn_snapshot=live_turn_snapshot,
        loop_state_ledger=loop_state_ledger,
        seed_intent=seed_intent,
        task_charter=task_charter,
        task_residual=task_residual,
        hardening=v59c_hardening,
        evidence_refs=base_evidence_refs,
    )
    if (
        continuation_decision.selected_next_path_summary
        != _expected_v60a_selected_downstream_path_summary(target_relative_path)
    ):
        raise ValueError("V60-A continuation decision must preserve the exact selected path")
    return (
        seed_intent,
        task_charter,
        task_residual,
        loop_state_ledger,
        continuation_decision,
    )


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


def render_live_turn_admission_payload(admission: AgenticDeLiveTurnAdmissionRecord) -> str:
    return json.dumps(admission.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_live_turn_handoff_payload(handoff: AgenticDeLiveTurnHandoffRecord) -> str:
    return json.dumps(handoff.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_live_turn_reintegration_payload(
    report: AgenticDeLiveTurnReintegrationReport,
) -> str:
    return json.dumps(report.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_seed_intent_payload(seed_intent: AgenticDeSeedIntentRecord) -> str:
    return json.dumps(seed_intent.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_task_charter_payload(task_charter: AgenticDeTaskCharterPacket) -> str:
    return json.dumps(task_charter.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_task_residual_payload(task_residual: AgenticDeTaskResidualPacket) -> str:
    return json.dumps(task_residual.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_loop_state_ledger_payload(loop_state_ledger: AgenticDeLoopStateLedger) -> str:
    return (
        json.dumps(loop_state_ledger.model_dump(mode="json"), indent=2, sort_keys=True)
        + "\n"
    )


def render_continuation_decision_payload(
    decision: AgenticDeContinuationDecisionRecord,
) -> str:
    return json.dumps(decision.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_workspace_continuity_region_declaration_payload(
    region: AgenticDeWorkspaceContinuityRegionDeclaration,
) -> str:
    return json.dumps(region.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_workspace_continuity_admission_payload(
    admission: AgenticDeWorkspaceContinuityAdmissionRecord,
) -> str:
    return json.dumps(admission.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_workspace_occupancy_payload(report: AgenticDeWorkspaceOccupancyReport) -> str:
    return json.dumps(report.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_workspace_continuity_reintegration_payload(
    report: AgenticDeWorkspaceContinuityReintegrationReport,
) -> str:
    return json.dumps(report.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_workspace_continuity_restoration_handoff_payload(
    handoff: AgenticDeWorkspaceContinuityRestorationHandoffRecord,
) -> str:
    return json.dumps(handoff.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_workspace_continuity_restoration_reintegration_payload(
    report: AgenticDeWorkspaceContinuityRestorationReintegrationReport,
) -> str:
    return json.dumps(report.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_workspace_continuity_hardening_payload(
    register: AgenticDeWorkspaceContinuityHardeningRegister,
) -> str:
    return json.dumps(register.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_live_restoration_handoff_payload(
    handoff: AgenticDeLiveRestorationHandoffRecord,
) -> str:
    return json.dumps(handoff.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_live_restoration_reintegration_payload(
    report: AgenticDeLiveRestorationReintegrationReport,
) -> str:
    return json.dumps(report.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_live_harness_hardening_payload(
    register: AgenticDeLiveHarnessHardeningRegister,
) -> str:
    return json.dumps(register.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_migration_decision_register_payload(
    register: AgenticDeMigrationDecisionRegister,
) -> str:
    return json.dumps(register.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_local_effect_observation_payload(
    observation: AgenticDeLocalEffectObservationRecord,
) -> str:
    return json.dumps(observation.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_local_effect_conformance_payload(
    report: AgenticDeLocalEffectConformanceReport,
) -> str:
    return json.dumps(report.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_local_effect_restoration_payload(
    restoration: AgenticDeLocalEffectRestorationRecord,
) -> str:
    return json.dumps(restoration.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"


def render_local_effect_hardening_payload(
    register: AgenticDeLocalEffectHardeningRegister,
) -> str:
    return json.dumps(register.model_dump(mode="json"), indent=2, sort_keys=True) + "\n"
